use std::convert::TryFrom;

use bumpalo::collections::Vec as BumpVec;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operation, Operand};

use crate::util::{bumpvec_with_capacity, ControlExt};

pub struct StackSizeTracker<'acx, 'e, E: ExecutionState<'e>> {
    stack_allocs: BumpVec<'acx, (i32, E::VirtualAddress)>,
    entry: E::VirtualAddress,
    binary: &'e BinaryFile<E::VirtualAddress>,
    // Esp offset before the main stack alloc sub (I.e. 4 if only ebp was pushed)
    pre_offset: u32,
    // Stack alloc sub size
    stack_alloc_size: u32,
    // Resolved value of esp *after* the stack allocation by sub is done,
    // used to determine point where the stack allocation is reverted
    // (register(4) - pre_offset - stack_alloc_size)
    init_esp: Option<Operand<'e>>,
    // Original offset of allocated values.
    // If the allocations are placed at top of stack,
    // index 0 is at entry_esp - (pre_offset + stack_alloc_size),
    // index 1 at -4, 2 at -8 etc.
    //
    // If they're placed at bottom,
    // index 0 is the topmost post_alloc_esp(*) + stack_alloc_size
    // index 1 one word lower at + 4 etc.
    //  (*) confusingly actual name is self.init_esp
    remaps: BumpVec<'acx, i32>,
    // Records instructions that read/write memory at addresses >= (register(4) - pre_offset)
    // Used when expanding the stack
    low_stack_accesses: BumpVec<'acx, E::VirtualAddress>,
    // When another register is used to point to stack,
    // its offset needs to be patched when `self.allocs_at_bottom` is set to true.
    alt_stack_pointer_inits: BumpVec<'acx, E::VirtualAddress>,
    first_branch_call: bool,
    allocs_at_bottom: bool,
}

impl<'acx, 'e, E: ExecutionState<'e>> StackSizeTracker<'acx, 'e, E> {
    pub fn new(
        entry: E::VirtualAddress,
        binary: &'e BinaryFile<E::VirtualAddress>,
        bump: &'acx bumpalo::Bump,
    ) -> StackSizeTracker<'acx, 'e, E> {
        StackSizeTracker {
            stack_allocs: BumpVec::new_in(bump),
            entry,
            binary,
            pre_offset: 0,
            stack_alloc_size: 0,
            init_esp: None,
            remaps: BumpVec::new_in(bump),
            low_stack_accesses: BumpVec::new_in(bump),
            alt_stack_pointer_inits: bumpvec_with_capacity(4, bump),
            first_branch_call: true,
            allocs_at_bottom: false,
        }
    }

    pub fn empty(
        binary: &'e BinaryFile<E::VirtualAddress>,
        bump: &'acx bumpalo::Bump,
    ) -> StackSizeTracker<'acx, 'e, E> {
        StackSizeTracker {
            stack_allocs: BumpVec::new_in(bump),
            entry: E::VirtualAddress::from_u64(0),
            binary,
            pre_offset: 0,
            stack_alloc_size: 0,
            init_esp: None,
            remaps: BumpVec::new_in(bump),
            low_stack_accesses: BumpVec::new_in(bump),
            alt_stack_pointer_inits: BumpVec::new_in(bump),
            first_branch_call: true,
            allocs_at_bottom: false,
        }
    }

    pub fn reset(&mut self) {
        self.stack_allocs.clear();
        self.pre_offset = 0;
        self.stack_alloc_size = 0;
        self.init_esp = None;
        self.first_branch_call = true;
        self.low_stack_accesses.clear();
        self.alt_stack_pointer_inits.clear();
        // I think not resetting remaps is correct? if reset() is intended to
        // reset analysis when reanalyzing a function.
    }

    /// Return true if operation was skipped (Due to it being large stack alloc call)
    pub fn operation<A>(&mut self, ctrl: &mut Control<'e, '_, '_, A>, op: &Operation<'e>) -> bool
    where A: analysis::Analyzer<'e, Exec=E>,
    {
        if self.first_branch_call {
            match *op {
                Operation::Jump { .. } => {
                    self.first_branch_call = false;
                }
                Operation::Call(..) => {
                    self.first_branch_call = false;
                    return ctrl.check_stack_probe();
                }
                _ => (),
            }
        }
        match *op {
            Operation::Move(ref dest, val, None) => {
                let ctx = ctrl.ctx();
                if matches!(dest, DestOperand::Register64(4)) {
                    let constant = val.if_add_with_const()
                        .filter(|x| x.0 == ctx.register(4))
                        .and_then(|x| i32::try_from(x.1).ok())
                        .or_else(|| {
                            val.if_sub_with_const()
                                .filter(|x| x.0 == ctx.register(4))
                                .and_then(|x| i32::try_from(x.1).ok())
                                .map(|x| 0i32.wrapping_sub(x))
                        });
                    if let Some(c) = constant {
                        let ctx = ctrl.ctx();
                        // Usually the entry is push ebp; mov ebp, esp; sub esp, alloc,
                        // if current address is entry + 3 then assume that it is intended
                        // to be a stack allocation.
                        if c < -0x20 || c > 0x20 ||
                            (ctrl.address() == self.entry + 3 &&
                                c < 0i32.wrapping_sub(E::VirtualAddress::SIZE as i32))
                        {
                            let address = ctrl.address();
                            let current_esp = ctrl.exec_state().resolve_register(4);
                            if self.stack_allocs.is_empty() && c < 0 {
                                let pre_offset = current_esp.if_sub_with_const()
                                    .and_then(|x| u32::try_from(x.1).ok());
                                if let Some(pre_offset) = pre_offset {
                                    self.pre_offset = pre_offset;
                                    // abs(c), since c is negative here
                                    self.stack_alloc_size = 0i32.wrapping_sub(c) as u32;
                                    // Becomes `rsp - stack_alloc_size` since c is negative here
                                    let init_esp = ctx.add_const(
                                        ctrl.resolve(ctx.register(4)),
                                        c as i64 as u64,
                                    );
                                    self.init_esp = Some(init_esp);
                                }
                            }
                            if c > 0 && self.stack_alloc_size != 0 {
                                // Try to avoid catching add esp, xx
                                // which is executed after cdecl call by checking
                                // that it esp should be at what it was after initial
                                // stack allocation.
                                if let Some(init_esp) = self.init_esp {
                                    if current_esp != init_esp {
                                        return false;
                                    }
                                }
                            }
                            if !self.stack_allocs.iter().any(|x| x.1 == address) {
                                self.stack_allocs.push((c, address));
                            }
                        }
                    }
                } else {
                    if self.stack_allocs.is_empty() {
                        if let DestOperand::Register64(..) = *dest {
                            // Check for moving esp to other register
                            // (Or esp +- offset)
                            // Checking before resolve for (hopefully) bit less work,
                            // don't know how to patch fancier moves anyway
                            let is_reg_move = val.if_register().is_some() ||
                                val.if_add_with_const().or_else(|| val.if_sub_with_const())
                                    .and_then(|x| x.0.if_register()).is_some();
                            if is_reg_move {
                                let val = ctrl.resolve(val);
                                let is_esp_move = if let Some((a, _)) = val.if_add_with_const()
                                    .or_else(|| val.if_sub_with_const())
                                {
                                    a == ctx.register(4)
                                } else {
                                    val == ctx.register(4)
                                };
                                if is_esp_move {
                                    self.alt_stack_pointer_inits.push(ctrl.address());
                                }
                            }
                        }
                    }
                    // Check for low stack accesses
                    // First iteration for val, second for dest
                    for i in 0..2 {
                        let mem = if i == 0 {
                            val.if_memory()
                        } else {
                            match dest {
                                DestOperand::Memory(mem) => Some(mem),
                                _ => None,
                            }
                        };
                        if let Some(mem) = mem {
                            let mem = ctrl.resolve_mem(mem);
                            let (base, offset) = mem.address();
                            if base == ctx.register(4) &&
                                offset.wrapping_add(self.pre_offset as u64) < 0x8000_0000
                            {
                                // If esp has been added back to be <= init_esp - self.pre_offset,
                                // ignore, skipping function prologue pops.
                                let current_esp = ctrl.resolve_register(4);
                                let esp_above_pre_offset = match current_esp.if_sub_with_const() {
                                    Some((l, r)) => {
                                        l == ctx.register(4) && r > self.pre_offset as u64
                                    }
                                    None => true,
                                };
                                if esp_above_pre_offset || offset < 0x8000_0000 {
                                    let address = ctrl.address();
                                    if self.low_stack_accesses.capacity() == 0 {
                                        self.low_stack_accesses.reserve(16);
                                    }
                                    self.low_stack_accesses.push(address);
                                }
                            }
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn remap_stack_offset(&mut self, offset: i32, reg_offset: i32) -> Option<i32> {
        // Offsets are 4 even on 64bit, as this is expected to be used
        // for widening u8 index -> u32 index variables
        if self.stack_alloc_size == 0 {
            // Uh, assuming that just aligned offset is fine
            // Can happen when only 1 dword is allocated,
            // as esp - 4 operations are explicitly skipped as they are hard to
            // distinguish from a jump
            return Some(offset & !0x3);
        }
        if reg_offset > 0 {
            // Accessing through register that was set to init_esp + x??
            // Too weird to try to handle for now.
            return None;
        }
        let reg_offset_pos = reg_offset.unsigned_abs();
        // Normalize offset to be independent of register
        let offset = reg_offset.checked_add(offset)?;
        if self.allocs_at_bottom || reg_offset_pos > self.pre_offset {
            // Handling for cases where reg_offset isn't between
            // stack vars and func arguments.
            // When reg points to top of stack (or middle?) going
            // to allocate the extra stack vars at the bottom of stack, and
            // fixing up arg accesses

            if !self.remaps.is_empty() && self.allocs_at_bottom == false {
                // Already had allocated at top, would need to reset
                // analysis or something??
                dat_warn!(
                    self, "Allocation in func {:?} with reg offset {:x} would need to be placed \
                    at bottom, but another allocation was already at top",
                    self.entry, reg_offset_pos,
                );
                return None;
            }
            self.allocs_at_bottom = true;

            let stack_bottom_from_reg_offset = reg_offset_pos - self.pre_offset;
            if let Some(pos) = self.remaps.iter().position(|&x| x == offset) {
                let result = stack_bottom_from_reg_offset.checked_add(pos as u32 * 4)? as i32;
                return Some(result);
            }
            let pos = self.remaps.len();
            let result = stack_bottom_from_reg_offset.checked_add(pos as u32 * 4)? as i32;
            self.remaps.push(offset);
            Some(result)
        } else {
            let stack_top = self.pre_offset.wrapping_add(self.stack_alloc_size);
            if let Some(pos) = self.remaps.iter().position(|&x| x == offset) {
                let relative_to_init_esp = stack_top.wrapping_add(pos as u32 * 4);
                let result = (-4i32).wrapping_sub(relative_to_init_esp as i32)
                    .wrapping_sub(reg_offset);
                return Some(result);
            }
            let relative_to_init_esp = stack_top.wrapping_add(self.remaps.len() as u32 * 4);
            self.remaps.push(offset);
            let result = (-4i32).wrapping_sub(relative_to_init_esp as i32)
                .wrapping_sub(reg_offset);
            Some(result)
        }
    }

    pub fn generate_patches<Cb>(&mut self, mut add_result: Cb)
    // patch, skip
    // Hook if skip != patch length
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        if self.stack_alloc_size == 0 || self.remaps.len() == 0 {
            return;
        }
        let orig_alloc_amt = match self.stack_allocs.get(0) {
            Some(s) => s.0,
            None => {
                dat_warn!(self, "Had no stack allocs in {:?}", self.entry);
                return;
            }
        };
        // Align to 16 bytes to not break SSE alignment assumptions if function
        // happens to have any. And of course 64-bit has to always have 16-aligned stack.
        let extra_alloc = align16(self.remaps.len() as u32 * 4);
        for &(alloc_amt, addr) in self.stack_allocs.iter() {
            if alloc_amt == orig_alloc_amt || alloc_amt == 0i32.wrapping_sub(orig_alloc_amt) {
                self.patch_stack_alloc(addr, extra_alloc, &mut add_result);
                if E::VirtualAddress::SIZE == 8 {
                    // Needs to find the unwind opcode for stack alloc and correct the size there
                    dat_warn!(self, "Unwind info fixup unimplemented for {:?}", self.entry);
                }
            }
        }
        if self.allocs_at_bottom {
            for &addr in &self.alt_stack_pointer_inits {
                self.patch_alt_stack_pointer_init(addr, extra_alloc, &mut add_result);
            }
            let mut prev = E::VirtualAddress::from_u64(0);
            for &addr in &self.low_stack_accesses {
                if addr == prev {
                    // May be common, but not common enough to need a hashmap?
                    continue;
                }
                prev = addr;
                self.patch_low_stack_access(addr, extra_alloc, &mut add_result);
            }
        }
    }

    fn patch_stack_alloc<Cb>(
        &self,
        address: E::VirtualAddress,
        extra_alloc: u32,
        add_result: &mut Cb,
    )
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't read instruction @ {:?}", address);
                return;
            }
        };
        if E::VirtualAddress::SIZE == 4 {
            match *bytes {
                // add/sub esp, imm32
                [0x81, 0xc4 | 0xec, ..] => {
                    let old_alloc = LittleEndian::read_u32(&bytes[2..]) as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[1] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 6, value, add_result);
                }
                // add/sub esp, imm8
                [0x83, 0xc4 | 0xec, ..] => {
                    let old_alloc = bytes[2] as i8 as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[1] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 3, value, add_result);
                }
                _ => {
                    dat_warn!(self, "Can't patch stack alloc @ {:?}", address);
                }
            }
        } else {
            match *bytes {
                // add/sub rsp, imm32
                [0x48, 0x81, 0xc4 | 0xec, ..] => {
                    let old_alloc = LittleEndian::read_u32(&bytes[2..]) as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[2] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 7, value, add_result);
                }
                // add/sub rsp, imm8
                [0x48, 0x83, 0xc4 | 0xec, ..] => {
                    let old_alloc = bytes[2] as i8 as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[2] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 4, value, add_result);
                }
                _ => {
                    dat_warn!(self, "Can't patch stack alloc @ {:?}", address);
                }
            }
        }
    }

    fn patch_alt_stack_pointer_init<Cb>(
        &self,
        address: E::VirtualAddress,
        extra_alloc: u32,
        add_result: &mut Cb,
    )
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't read instruction @ {:?}", address);
                return;
            }
        };
        if E::VirtualAddress::SIZE == 4 {
            dat_warn!(self, "Can't patch alt stack pointer init @ {:?}", address);
        } else {
            match *bytes {
                // lea reg, [rsp/r12 + imm8/32]
                [rex, 0x8d, modrm, 0x24, ..]
                    if rex & 0xf8 == 0x48 && matches!(modrm & 0xc7, 0x44 | 0x84) =>
                {
                    let mut buffer = [0u8; 8];
                    buffer.copy_from_slice(&bytes[..8]);
                    let (offset, old_len) = if modrm & 0xc0 == 0x40 {
                        // imm8
                        (buffer[4] as i8 as i32, 5)
                    } else {
                        // imm32
                        (LittleEndian::read_i32(&buffer[4..]), 8)
                    };
                    if offset >= 0 {
                        dat_warn!(self, "Can't patch alt stack pointer init @ {:?}", address);
                        return;
                    }
                    let new_offset = offset.wrapping_sub(extra_alloc as i32);
                    // If using imm8, the 3 high bytes written here will just
                    // be ignored
                    LittleEndian::write_i32(&mut buffer[4..], new_offset);
                    if new_offset < -0x7f {
                        // Convert to imm32 if new_offset doesn't fit in imm8
                        buffer[2] = buffer[2] & !0xc0 | 0x80;
                        add_result(address, &buffer[..8], old_len);
                    } else {
                        // If new offset fits in imm8, old offset should have too
                        debug_assert!(buffer[2] & 0xc0 == 0x40 && old_len == 5);
                        add_result(address, &buffer[..5], old_len);
                    }
                }
                _ => {
                    dat_warn!(self, "Can't patch alt stack pointer init @ {:?}", address);
                }
            }
        }
    }

    fn patch_low_stack_access<Cb>(
        &self,
        address: E::VirtualAddress,
        _extra_alloc: u32,
        _add_result: &mut Cb,
    )
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't read instruction @ {:?}", address);
                return;
            }
        };
        if E::VirtualAddress::SIZE == 4 {
            dat_warn!(self, "Can't patch low stack access @ {:?}", address);
        } else {
            match *bytes {
                _ => {
                    dat_warn!(self, "Can't patch low stack access @ {:?}", address);
                }
            }
        }
    }

    fn add_esp_add<Cb>(
        &self,
        address: E::VirtualAddress,
        skip: usize,
        add: i32,
        add_result: &mut Cb,
    )
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let second_byte = if add < 0 {
            0xec
        } else {
            0xc4
        };
        let add = add.wrapping_abs() as u32;
        if add >= 0x80 {
            let mut patch = [0x48, 0x81, second_byte, 0x00, 0x00, 0x00, 0x00];
            LittleEndian::write_u32(&mut patch[3..], add);
            if E::VirtualAddress::SIZE == 4 {
                add_result(address, &patch[1..], skip);
            } else {
                add_result(address, &patch, skip);
            }
        } else {
            let patch = [0x48, 0x83, second_byte, add as u8];
            if E::VirtualAddress::SIZE == 4 {
                add_result(address, &patch[1..], skip);
            } else {
                add_result(address, &patch, skip);
            }
        }
    }
}

fn align16(val: u32) -> u32 {
    (val.wrapping_sub(1) | 0xf).wrapping_add(1)
}
