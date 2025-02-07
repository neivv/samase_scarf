//! Function / global / string / byte searchers

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{FuncCallPair, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Rva};

use crate::analysis::{AnalysisCtx};
use crate::x86_64_unwind::UnwindFunctions;

// Tries to return a func index to the address less or equal to `entry` that is definitely a
// function entry. Has still a hard limit.
fn first_definite_entry<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    entry: Va,
    func_list: &FunctionList<'_, Va>,
    limit: usize,
    lowest_allowed: Va,
) -> (usize, usize) {
    fn is_definitely_entry<Va: VirtualAddress>(
        binary: &BinaryFile<Va>,
        entry: Va,
    ) -> bool {
        if entry.as_u64() & 0xf != 0 {
            return false;
        }
        // Casting to u64 -> u32 is fine as there aren't going to be 4GB binaries
        let relative = (entry.as_u64() - binary.base.as_u64()) as u32;
        if Va::SIZE == 4 {
            let first_bytes = match binary.slice_from(relative..relative + 3) {
                Ok(o) => o,
                Err(_) => return false,
            };
            // push ebx; mov ebx, esp or push ebp; mov ebp, esp
            // Two different encodings for both
            first_bytes == [0x53, 0x8b, 0xdc] ||
                first_bytes == [0x53, 0x89, 0xe3] ||
                first_bytes == [0x55, 0x8b, 0xec] ||
                first_bytes == [0x55, 0x89, 0xe5]
        } else {
            let first_bytes: &[u8; 64] = match binary.slice_from(relative..relative + 64) {
                Ok(o) => match o.try_into() {
                    Ok(o) => o,
                    Err(_) => return false,
                },
                Err(_) => return false,
            };
            // Check for 48, 89, xx, 24, [08|10|18|20]
            // for mov [rsp + x], reg
            if first_bytes[0] == 0x48 &&
                first_bytes[1] == 0x89 &&
                first_bytes[2] & 0x7 == 4 &&
                first_bytes[3] == 0x24 &&
                first_bytes[4] & 0x7 == 0 &&
                first_bytes[4].wrapping_sub(1) < 0x20
            {
                return true;
            }
            // Also 88, xx, 24, [08|10|18|20]
            // for u8 move
            if first_bytes[0] == 0x88 &&
                first_bytes[1] & 0x7 == 4 &&
                first_bytes[2] == 0x24 &&
                first_bytes[3] & 0x7 == 0 &&
                first_bytes[3].wrapping_sub(1) < 0x20
            {
                return true;
            }
            if complex_x86_64_entry_check(&first_bytes).unwrap_or(false) {
                return true;
            }
            false
        }
    }
    let funcs = func_list.functions;
    let mut index = funcs.binary_search_by(|&x| match x <= entry {
        true => std::cmp::Ordering::Less,
        false => std::cmp::Ordering::Greater,
    }).unwrap_or_else(|e| e);
    let end = index;
    if index != 0 {
        index -= 1;
    }
    while index != 0 {
        let address = funcs[index];
        if address < lowest_allowed {
            if index + 1 != funcs.len() {
                index += 1;
                break;
            }
        }
        if is_definitely_entry(binary, address) {
            break;
        }
        if end - index >= limit {
            break;
        }
        index -= 1;
    }
    (index, end)
}

#[inline]
fn slice_to_arr_ref<const SIZE: usize>(slice: &[u8]) -> Option<&[u8; SIZE]> {
    slice.get(..SIZE)?.try_into().ok()
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum RegisterState {
    Any,
    Caller,
    Stack,
}

fn check_rsp_move(bytes: &[u8; 3]) -> Option<u8> {
    if bytes[0] & 0xf8 == 0x48 {
        // Accept both mov r, rm and mov rm, r
        if bytes[1] == 0x89 && bytes[2] & 0xf8 == 0xe0 {
            let add_8 = (bytes[0] & 1) << 3;
            Some((bytes[2] & 7) | add_8)
        } else if bytes[1] == 0x8b && bytes[2] & 0xc7 == 0xc4 {
            let add_8 = (bytes[0] & 4) << 1;
            Some(((bytes[2] >> 3) & 7) | add_8)
        } else {
            None
        }
    } else {
        None
    }
}

fn complex_x86_64_entry_check(bytes: &[u8; 64]) -> Option<bool> {
    use RegisterState::*;
    // Accepts following
    //   mov volatilereg, rsp
    //      (optional)
    //   mov [rsp | volatilereg + C], non-volatile or arg
    //      (Optional; moves to 4-word shadow space)
    //   push 0~7 non-volatile registers
    //   lea rbp, [volatilereg - C]
    //      (Optional; only if rsp was copied to volatilereg and rbp was pushed)
    //   mov rbp, rsp
    //      (Alt for the lea)
    //   sub rsp, C
    //      where C aligns the stack to 16 (function entry is in 8-misalign)
    //   For large alloc:
    //      mov eax, C (Still aligning stack correctly)
    //      call X
    //      sub rsp, rax

    let mut register_state = [
        Any, Any, Any, Caller,
        Stack, Caller, Caller, Caller,
        Any, Any, Any, Any,
        Caller, Caller, Caller, Caller,
    ];
    let mut next = slice_to_arr_ref::<61>(bytes)?;

    // -- mov volatilereg, rsp --
    if let Some(dest) = check_rsp_move(slice_to_arr_ref(bytes)?) {
        let dest = (dest & 0xf) as usize;
        if register_state[dest] != Any {
            return Some(false);
        }
        register_state[dest] = Stack;
        next = slice_to_arr_ref(&bytes[3..])?;
    }
    // -- Moves to shadow space --
    let bytes = next;
    let mut pos = 0usize;
    for _ in 0..4 {
        if let Some(slice) = bytes.get(pos..pos.wrapping_add(4)) {
            if slice[0] & 0xf0 == 0x40 && slice[1] == 0x89 && slice[2] & 0xc0 == 0x40 {
                let offset = slice[3];
                if offset & 0x7 != 0 || offset.wrapping_sub(8) > 0x20 {
                    return Some(false);
                }
                let dest_base = (slice[2] & 0x7) | ((slice[0] & 0x1) << 3);
                let dest_base = (dest_base & 0xf) as usize;
                let reg = ((slice[2] >> 3) & 0x7) | ((slice[0] & 0x4) << 1);
                let reg = (reg & 0xf) as usize;
                if register_state[dest_base] != Stack {
                    return Some(false);
                }
                if register_state[reg] != Caller && matches!(reg, 1 | 2 | 8 | 9) == false {
                    return Some(false);
                }
                register_state[reg] = Any;
                pos += 4;
            } else {
                break;
            }
        }
    }
    let bytes = slice_to_arr_ref::<45>(&bytes[pos..])?;
    let mut pos = 0usize;
    // -- pushes --
    let mut push_count = 0;
    for _ in 0..8 {
        if let Some(slice) = bytes.get(pos..pos.wrapping_add(2)) {
            if slice[0] & 0xf8 == 0x50 {
                let dest = (slice[0] & 0x7) as usize;
                if register_state[dest] != Caller {
                    return Some(false);
                }
                register_state[dest] = Any;
                pos += 1;
            } else if slice[0] & 0xf0 == 0x40 && slice[1] & 0xf8 == 0x50 {
                let dest = ((slice[1] & 0x7) | ((slice[0] & 0x1) << 3) & 0xf) as usize;
                if register_state[dest] != Caller {
                    return Some(false);
                }
                register_state[dest] = Any;
                pos += 2;
            } else {
                break;
            }
            push_count += 1;
        }
    }
    let bytes = slice_to_arr_ref::<29>(&bytes[pos..])?;
    // -- lea reg, [rsp(or copy) - x] --
    let mut next = slice_to_arr_ref::<21>(bytes)?;
    if bytes[0] & 0xf0 == 0x40 && bytes[1] == 0x8d {
        let dest = ((bytes[2] >> 3) & 7) | ((bytes[0] & 0x4) << 1);
        let dest = (dest & 0xf) as usize;
        let src = (bytes[2] & 7) | ((bytes[0] & 0x1) << 3);
        let src = (src & 0xf) as usize;
        if bytes[2] & 0xc0 == 0x80 {
            if src & 7 == 4 {
                // SIB, require no scale (mask 0x18 = 0x20),
                // assume rsp/r12 for base (mask 0x7 = 0x4)
                if bytes[3] & 0x3f == 0x24 {
                    if register_state[src] != Stack || register_state[dest] != Any {
                        return Some(false);
                    }
                    next = slice_to_arr_ref(&bytes[8..])?;
                }
            } else {
                if register_state[src] != Stack || register_state[dest] != Any {
                    return Some(false);
                }
                next = slice_to_arr_ref(&bytes[7..])?;
            }
        } else if bytes[2] & 0xc0 == 0x40 {
            if src & 7 == 4 {
                // SIB, require no scale (mask 0x18 = 0x20),
                // assume rsp/r12 for base (mask 0x7 = 0x4)
                if bytes[3] & 0x3f == 0x24 {
                    if register_state[src] != Stack || register_state[dest] != Any {
                        return Some(false);
                    }
                    next = slice_to_arr_ref(&bytes[5..])?;
                }
            } else {
                if register_state[src] != Stack || register_state[dest] != Any {
                    return Some(false);
                }
                next = slice_to_arr_ref(&bytes[4..])?;
            }
        }
    }

    let bytes = next;
    // -- second possible move of rsp  --
    let mut next = slice_to_arr_ref::<18>(bytes)?;
    if let Some(dest) = check_rsp_move(slice_to_arr_ref(bytes)?) {
        let dest = (dest & 0xf) as usize;
        if register_state[dest] != Any {
            return Some(false);
        }
        register_state[dest] = Stack;
        next = slice_to_arr_ref(&bytes[3..])?;
    }

    // sub rsp, const
    let bytes = next;
    let misalign = if push_count & 1 == 0 { 8 } else { 0 };
    if bytes[0] == 0x48 &&
        matches!(bytes[1], 0x81 | 0x83) &&
        bytes[2] == 0xec &&
        bytes[3] & 0xf == misalign
    {
        return Some(true);
    }
    // mov eax, const; call X; sub rsp, rax
    if bytes[0] == 0xb8 &&
        bytes[1] & 0xf == misalign &&
        bytes[5] == 0xe8 &&
        &bytes[0xa..][..3] == &[0x48, 0x2b, 0xe0]
    {
        return Some(true);
    }
    Some(false)
}

#[test]
fn test_complex_x86_64_entry() {
    fn do_test(input: &[u8]) -> bool {
        let mut buf = [0u8; 64];
        (&mut buf[..input.len()]).copy_from_slice(input);
        complex_x86_64_entry_check(&buf) == Some(true)
    }

    assert!(do_test(&[
        0x48, 0x8b, 0xc4, // mov rax, rsp
        0x55, 0x41, 0x56, 0x41, 0x57, // push rbp, r14, r15
        0x48, 0x8d, 0xa8, 0x38, 0xfd, 0xff, 0xff, // lea rbp, [rax - 2c8]
        0x48, 0x81, 0xec, 0xb0, 0x03, 0x00, 0x00, // sub rsp, 3b0
    ]));
    assert!(do_test(&[
        0x57, // push rdi
        0x48, 0x83, 0xEC, 0x20, // sub rsp, 20
    ]));
    assert!(do_test(&[
        0x48, 0x81, 0xec, 0x98, 0x00, 0x00, 0x00, // sub rsp, 98
    ]));
    assert!(do_test(&[
        // Odd to have r11 == rbp + 8 but that can happen.
        // They both end up being used too.
        0x4c, 0x8b, 0xdc, // mov r11, rsp
        0x55, // push rbp,
        0x48, 0x8b, 0xec, // mov rbp, rsp
        0x48, 0x81, 0xec, 0x80, 0x00, 0x00, 0x00, // sub rsp, 80
    ]));
    assert!(do_test(&[
        0x40, 0x55, // push rbp
        0x41, 0x54, // push r12,
        0x48, 0x8d, 0x6c, 0x24, 0xb1, // lea rbp, [rsp - 4f]
        0x48, 0x81, 0xec, 0xc8, 0x00, 0x00, 0x00, // sub rsp, c8
    ]));
    assert!(do_test(&[
        0x40, 0x55, // push rbp
        0x48, 0x8d, 0xac, 0x24, 0x50, 0xd7, 0xff, 0xff, // lea rbp, [rsp - 28]
        0xb8, 0xb0, 0x29, 0x00, 0x00, // mov eax, 29b0
        0xe8, 0x00, 0xff, 0xff, 0xff, // call x
        0x48, 0x2b, 0xe0, // sub rsp, rax
    ]));
    assert!(do_test(&[
        0x48, 0x8b, 0xc4, // mov rax, rsp
        0x48, 0x89, 0x58, 0x08, // mov [rax + 8], rbx
        0x44, 0x89, 0x48, 0x20, // mov [rax + 20], r9d
        0x55, // push rbp
        0x56, // push rsi
        0x57, // push rdi
        0x41, 0x54, // push r12
        0x41, 0x55, // push r13
        0x41, 0x56, // push r14
        0x41, 0x57, // push r15
        0x48, 0x8d, 0x68, 0x98, // lea rbp, [rax - 68]
        0x48, 0x81, 0xec, 0x30, 0x01, 0x00, 0x00, // sub rsp, 130
    ]));
}

#[derive(Debug, Copy, Clone)]
pub struct StringRefs<Va> {
    pub use_address: Va,
    pub func_entry: Va,
    pub string_address: Va,
}

#[derive(Debug, Copy, Clone)]
pub struct GlobalRefs<Va: VirtualAddress> {
    pub use_address: Va,
    pub func_entry: Va,
}

#[derive(Debug, Copy, Clone)]
pub enum EntryOf<R> {
    Ok(R),
    Retry,
    Stop,
}

impl<R> EntryOf<R> {
    pub fn is_ok(&self) -> bool {
        match self {
            EntryOf::Ok(..) => true,
            EntryOf::Retry | EntryOf::Stop => false,
        }
    }
}

#[derive(Debug)]
pub enum EntryOfResult<R, Va: VirtualAddress> {
    /// Found the result which was looked for, as well as the entry
    Ok(Va, R),
    /// No result, but determined the address to be entry
    Entry(Va),
    None,
}

impl<R, Va: VirtualAddress> EntryOfResult<R, Va> {
    pub fn is_ok(&self) -> bool {
        match self {
            EntryOfResult::Ok(..) => true,
            _ => false,
        }
    }

    pub fn into_option(self) -> Option<R> {
        match self {
            EntryOfResult::Ok(_, b) => Some(b),
            _ => None,
        }
    }

    pub fn into_option_with_entry(self) -> Option<(Va, R)> {
        match self {
            EntryOfResult::Ok(a, b) => Some((a, b)),
            _ => None,
        }
    }
}

/// Better version of entry_of, retries with an earlier func if the cb returns false,
/// helps against false positive func entries.
pub fn entry_of_until<'a, Va: VirtualAddress, R, F>(
    binary: &BinaryFile<Va>,
    funcs: &FunctionList<'_, Va>,
    caller: Va,
    mut cb: F,
) -> EntryOfResult<R, Va>
where F: FnMut(Va) -> EntryOf<R>
{
    entry_of_until_with_limit(binary, funcs, caller, 16, &mut cb)
}

pub fn entry_of_until_with_limit<'a, Va: VirtualAddress, R, F>(
    binary: &BinaryFile<Va>,
    funcs: &FunctionList<'_, Va>,
    caller: Va,
    limit: usize,
    mut cb: F,
) -> EntryOfResult<R, Va>
where F: FnMut(Va) -> EntryOf<R>
{
    let lowest_allowed;
    if let Some((start, end)) = funcs.unwind_functions.previous_unwind_function(binary, caller) {
        // Inside unwind info, assume start to be the real entry
        if end > caller {
            match cb(start) {
                EntryOf::Ok(s) => return EntryOfResult::Ok(start, s),
                EntryOf::Stop => return EntryOfResult::Entry(start),
                EntryOf::Retry => return EntryOfResult::None,
            }
        }
        // Else it should not be further than this address
        lowest_allowed = end;
    } else {
        lowest_allowed = Va::from_u64(0);
    }
    let (start, end) = first_definite_entry(binary, caller, funcs, limit, lowest_allowed);
    for &entry in funcs.functions.iter().take(end).skip(start) {
        match cb(entry) {
            EntryOf::Ok(s) => return EntryOfResult::Ok(entry, s),
            EntryOf::Stop => return EntryOfResult::Entry(entry),
            EntryOf::Retry => (),
        }
    }
    //debug!("entry_of_until limit reached for caller {:?} {:?}", caller, start..end);
    EntryOfResult::None
}

pub struct FunctionFinder<'a, 'e, E: ExecutionState<'e>> {
    functions: &'a [E::VirtualAddress],
    globals_with_values: &'a [RelocValues<E::VirtualAddress>],
    functions_with_callers: &'a [FuncCallPair<E::VirtualAddress>],
    unwind_functions: &'a UnwindFunctions,
}

/// What originally was just sorted list of functions, now also carries
/// unwind info for better entry_of results.
/// Maybe could just take FunctionFinder reference though now.
pub struct FunctionList<'a, Va: VirtualAddress> {
    pub functions: &'a [Va],
    unwind_functions: &'a UnwindFunctions,
}

impl<'a, 'e, E: ExecutionState<'e>> FunctionFinder<'a, 'e, E> {
    pub fn new(
        functions: &'a [E::VirtualAddress],
        globals_with_values: &'a [RelocValues<E::VirtualAddress>],
        functions_with_callers: &'a [FuncCallPair<E::VirtualAddress>],
        unwind_functions: &'a UnwindFunctions,
    ) -> FunctionFinder<'a, 'e, E> {
        FunctionFinder {
            functions,
            globals_with_values,
            functions_with_callers,
            unwind_functions,
        }
    }

    pub fn functions(&self) -> FunctionList<'_, E::VirtualAddress> {
        FunctionList {
            functions: self.functions,
            unwind_functions: self.unwind_functions,
        }
    }

    pub fn globals_with_values(&self) -> &[RelocValues<E::VirtualAddress>] {
        &self.globals_with_values
    }

    pub fn functions_with_callers(&self) -> &[FuncCallPair<E::VirtualAddress>] {
        &self.functions_with_callers
    }

    pub fn string_refs<'acx>(
        &self,
        cache: &'acx AnalysisCtx<'e, E>,
        string: &[u8],
    ) -> BumpVec<'acx, StringRefs<E::VirtualAddress>> {
        let rdata = cache.binary_sections.rdata;
        let bump = &cache.bump;
        let str_ref_addrs = find_strings_casei(bump, &rdata.data, string);
        // (Use rva, string rva)
        let rdata_base = rdata.virtual_address;
        let result = str_ref_addrs
            .into_iter()
            .flat_map(|str_rva| {
                let addr = rdata_base + str_rva.0;
                let ptr_refs = self.find_functions_using_global(cache, addr);
                ptr_refs.into_iter().map(move |x| (x.use_address, x.func_entry, str_rva))
            })
            .map(|(code_va, func_entry, str_rva)| {
                StringRefs {
                    use_address: code_va,
                    func_entry,
                    string_address: rdata_base + str_rva.0,
                }
            });
        BumpVec::from_iter_in(result, bump)
    }

    pub fn find_callers<'acx>(
        &self,
        analysis: &'acx AnalysisCtx<'e, E>,
        func_entry: E::VirtualAddress,
    ) -> BumpVec<'acx, E::VirtualAddress> {
        use std::cmp::Ordering;
        let callers = self.functions_with_callers();
        let lower_bound = callers.binary_search_by(|x| match x.callee >= func_entry {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let result = (&callers[lower_bound..]).iter()
            .take_while(|&x| x.callee == func_entry)
            .map(|x| x.caller);
        BumpVec::from_iter_in(result, &analysis.bump)
    }

    pub fn find_functions_using_global<'acx>(
        &self,
        actx: &'acx AnalysisCtx<'e, E>,
        addr: E::VirtualAddress,
    ) -> BumpVec<'acx, GlobalRefs<E::VirtualAddress>> {
        use std::cmp::Ordering;

        let relocs = self.globals_with_values();
        let functions = self.functions().functions;
        let start = relocs.binary_search_by(|x| match x.value >= addr {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let result = (&relocs[start..]).iter()
            .take_while(|x| x.value == addr)
            .map(|x| {
                let index = functions.binary_search(&x.address).unwrap_or_else(|e| e);
                GlobalRefs {
                    use_address: x.address,
                    func_entry: functions[index.saturating_sub(1)],
                }
            });
        BumpVec::from_iter_in(result, &actx.bump)
    }
}

/// Returns any matching strings as Rvas.
///
/// Remember to null-terminate strings if needed =)
pub fn find_strings_casei<'a>(bump: &'a Bump, mut data: &[u8], needle: &[u8]) -> BumpVec<'a, Rva> {
    let mut ret = BumpVec::new_in(bump);
    let mut offset = 0usize;
    let first = needle[0];
    while data.len() >= needle.len() {
        let result = match first {
            x if x >= b'a' && x <= b'z' => {
                memchr::memchr2(x, x.wrapping_sub(b'a').wrapping_add(b'A'), data)
            }
            x if x >= b'A' && x <= b'Z' => {
                memchr::memchr2(x, x.wrapping_sub(b'A').wrapping_add(b'a'), data)
            }
            x => memchr::memchr(x, data),
        };
        match result {
            Some(pos) => {
                let end = pos.wrapping_add(needle.len());
                if end > data.len() {
                    break;
                }
                let compare = match data.get(pos..end) {
                    Some(s) => s,
                    None => break,
                };
                if needle.eq_ignore_ascii_case(compare) {
                    ret.push(Rva((offset.wrapping_add(pos)) as u32));
                }
                offset = offset.wrapping_add(pos).wrapping_add(1);
                data = match data.get(pos.wrapping_add(1)..) {
                    Some(s) => s,
                    None => break,
                };
            }
            None => break,
        }
    }
    ret
}

pub fn find_address_refs<'a, Va: VirtualAddress>(
    bump: &'a Bump,
    data: &[u8],
    addr: Va,
) -> BumpVec<'a, Rva> {
    let mut result = if Va::SIZE == 4 {
        let bytes = (addr.as_u64() as u32).to_le_bytes();
        find_bytes(bump, data, &bytes[..])
    } else {
        let bytes = addr.as_u64().to_le_bytes();
        find_bytes(bump, data, &bytes[..])
    };
    // Filter out if align is less than 4.
    // 64-bit bw can have 4-aligned pointers.
    result.retain(|x| x.0 & 3 == 0);
    result
}

pub fn find_bytes<'a>(bump: &'a Bump, data: &[u8], needle: &[u8]) -> BumpVec<'a, Rva> {
    use memchr::memmem::{Finder};

    let mut ret = BumpVec::new_in(bump);
    let finder = Finder::new(needle);
    for index in finder.find_iter(data) {
        ret.push(Rva(index as u32));
    }
    ret
}
