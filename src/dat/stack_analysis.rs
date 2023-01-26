use std::convert::TryFrom;

use bumpalo::collections::Vec as BumpVec;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operation, Operand};

use crate::util::ControlExt;

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
    // (register(4) - pre_offset - post_offset)
    init_esp: Option<Operand<'e>>,
    // Original offset of allocated values.
    // If the allocations are placed at top of stack,
    // index 0 is at pre_offset + stack_alloc_size,
    // index 1 at +4, 2 at +8 etc.
    remaps: BumpVec<'acx, i32>,
    first_branch_call: bool,
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
            first_branch_call: true,
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
            first_branch_call: true,
        }
    }

    pub fn reset(&mut self) {
        self.stack_allocs.clear();
        self.pre_offset = 0;
        self.stack_alloc_size = 0;
        self.init_esp = None;
        self.first_branch_call = true;
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
                        if c < -0x20 || c > 0x20 || (ctrl.address() == self.entry + 3 && c < -4) {
                            let address = ctrl.address();
                            let current_esp = ctrl.exec_state().resolve_register(4);
                            if self.stack_allocs.is_empty() && c < 0 {
                                let pre_offset = current_esp.if_sub_with_const()
                                    .and_then(|x| u32::try_from(x.1).ok());
                                if let Some(pre_offset) = pre_offset {
                                    self.pre_offset = pre_offset;
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
                }
                false
            }
            _ => false,
        }
    }

    pub fn remap_ebp_offset(&mut self, offset: i32, reg_offset: i32) -> Option<i32> {
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
        if reg_offset_pos > self.pre_offset {
            // Todo handling for cases where reg_offset isn't between
            // stack vars and func arguments.
            // When reg points to top of stack (or middle?) probably wanting
            // to allocate the extra stack vars at the bottom of stack, and
            // fixing up arg accesses?
            return None;
        }
        let offset = reg_offset.checked_add(offset)?;
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
        for &(alloc_amt, addr) in self.stack_allocs.iter() {
            if alloc_amt == orig_alloc_amt || alloc_amt == 0i32.wrapping_sub(orig_alloc_amt) {
                self.patch_stack_alloc(addr, &mut add_result);
            }
        }
    }

    fn patch_stack_alloc<Cb>(&self, address: E::VirtualAddress, add_result: &mut Cb)
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't widen instruction @ {:?}", address);
                return;
            }
        };
        // Align to 16 bytes to not break SSE alignment assumptions if function
        // happens to have any. And of course 64-bit has to always have 16-aligned stack.
        let extra_alloc = align16(self.remaps.len() as u32 * 4);
        match *bytes {
            // sub esp, imm32
            [0x81, 0xec, ..] => {
                let old_alloc = LittleEndian::read_u32(&bytes[2..]) as i32;
                let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                self.add_esp_add(address, 6, 0i32.wrapping_sub(new_alloc), add_result);
            }
            // sub esp, imm8
            [0x83, 0xec, ..] => {
                let old_alloc = bytes[2] as i8 as i32;
                let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                self.add_esp_add(address, 3, 0i32.wrapping_sub(new_alloc), add_result);
            }
            _ => {
                dat_warn!(self, "Can't widen instruction @ {:?}", address);
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
            let mut patch = [0x81, second_byte, 0x00, 0x00, 0x00, 0x00];
            LittleEndian::write_u32(&mut patch[2..], add);
            add_result(address, &patch, skip);
        } else {
            let patch = [0x83, second_byte, add as u8];
            add_result(address, &patch, skip);
        }
    }
}

fn align16(val: u32) -> u32 {
    (val.wrapping_sub(1) | 0xf).wrapping_add(1)
}
