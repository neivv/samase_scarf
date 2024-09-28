use arrayvec::ArrayVec;
use bumpalo::collections::Vec as BumpVec;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operation, Operand};

use crate::util::{bumpvec_with_capacity, ControlExt};
use crate::x86_64_instruction_info;
use crate::x86_64_unwind::UnwindFunctions;

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
    // Records instructions that read/write memory across self.pre_offset
    // Either base reg is above pre_offset, having been fixed to have larger allocation
    // than before, but memory access is to arguments/shadow space, or
    // base reg is below pre_offset but memory access is to local variables.
    across_pre_offset_accesses: BumpVec<'acx, E::VirtualAddress>,
    // When another register is used to point to stack,
    // its offset needs to be patched when `self.allocs_at_bottom` is set to true.
    // The first offset is "stack offset of the destination register after instruction",
    // the second offset is "stack offset of the register which was used as input to this
    // instruction"
    alt_stack_pointer_inits: BumpVec<'acx, (E::VirtualAddress, u32, u32)>,
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
            across_pre_offset_accesses: BumpVec::new_in(bump),
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
            across_pre_offset_accesses: BumpVec::new_in(bump),
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
        self.across_pre_offset_accesses.clear();
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
            Operation::Move(ref dest, val) => {
                let ctx = ctrl.ctx();
                let reg_dest = match dest {
                    DestOperand::Arch(x) => x.if_register(),
                    _ => None,
                };
                if reg_dest == Some(4) {
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
                                        ctrl.resolve_register(4),
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
                    if reg_dest.is_some() {
                        let val_unres = val;
                        // Check for moving esp to other register
                        // (Or esp +- offset)
                        // Checking before resolve for (hopefully) bit less work,
                        // don't know how to patch fancier moves anyway
                        let is_reg_move = val_unres.if_register().is_some() ||
                            val_unres.if_add_with_const()
                                .or_else(|| val_unres.if_sub_with_const())
                                .and_then(|x| x.0.if_register()).is_some();
                        if is_reg_move {
                            let val = ctrl.resolve(val);
                            let esp_offset = if let Some((l, r)) = val.if_sub_with_const() {
                                if l == ctx.register(4) {
                                    u32::try_from(r).ok()
                                } else {
                                    None
                                }
                            } else if val == ctx.register(4) {
                                Some(0)
                            } else {
                                None
                            };
                            // Assuming that val_unres is `reg` or `reg +/- c`
                            let source_offset =
                                if let Some((_, r)) = val_unres.if_add_with_const()
                            {
                                i32::try_from(r).ok()
                            } else if let Some((_, r)) = val_unres.if_sub_with_const() {
                                i32::try_from(r).ok().map(|x| -x)
                            } else {
                                Some(0)
                            };
                            if let Some(off) = esp_offset {
                                // source_offset is the source register's stack offset before
                                // move. If the source register is at bottom of the stack
                                // frame (Below self.pre_offset), the move won't need to fixed
                                // up afterwards.
                                let source_offset = source_offset.and_then(|x| {
                                    let x = i32::try_from(off).ok()?
                                        .checked_add(x)?;
                                    u32::try_from(x).ok()
                                });
                                if let Some(source) = source_offset {
                                    let address = ctrl.address();
                                    self.alt_stack_pointer_inits.push((address, off, source));
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
                        if let Some(mem_unres) = mem {
                            let (unres_base, unres_offset) = mem_unres.address();
                            let mem = ctrl.resolve_mem(mem_unres);
                            let (base, offset) = mem.address();
                            let unres_offset = offset.wrapping_sub(unres_offset);
                            let offset = (offset as i64 as i32).unsigned_abs();
                            let unres_offset = (unres_offset as i64 as i32).unsigned_abs();
                            let crosses_pre_offset =
                                (offset <= self.pre_offset && unres_offset > self.pre_offset) ||
                                (unres_offset <= self.pre_offset && offset > self.pre_offset);
                            if base == ctx.register(4) &&
                                crosses_pre_offset &&
                                unres_base.if_register().is_some()
                            {
                                let address = ctrl.address();
                                if self.across_pre_offset_accesses.capacity() == 0 {
                                    self.across_pre_offset_accesses.reserve(16);
                                }
                                self.across_pre_offset_accesses.push(address);
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

    pub fn generate_patches<Cb>(&mut self, unwind: &UnwindFunctions, mut add_result: Cb)
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
        let add_result = &mut add_result;
        // Align to 16 bytes to not break SSE alignment assumptions if function
        // happens to have any. And of course 64-bit has to always have 16-aligned stack.
        let extra_alloc = align16(self.remaps.len() as u32 * 4);
        let mut unwind_patch_addresses = ArrayVec::<E::VirtualAddress, 4>::new();
        for &(alloc_amt, addr) in self.stack_allocs.iter() {
            if alloc_amt == orig_alloc_amt || alloc_amt == 0i32.wrapping_sub(orig_alloc_amt) {
                if let Some(end_addr) = self.patch_stack_alloc(addr, extra_alloc, add_result) {
                    if E::VirtualAddress::SIZE == 8 {
                        if !unwind_patch_addresses.contains(&end_addr) {
                            if unwind_patch_addresses.try_push(end_addr).is_err() {
                                dat_warn!(self, "Too many unwind patches in {:?}", self.entry);
                            }
                        }
                    }
                }
            }
        }
        if self.allocs_at_bottom {
            let mut prev = E::VirtualAddress::from_u64(0);
            for &(addr, off1, off2) in &self.alt_stack_pointer_inits {
                if addr == prev {
                    // May be common, but not common enough to need a hashmap?
                    continue;
                }
                prev = addr;
                // Hoping that any alt stack pointers pointing to bottom of stack
                // are only used during prologue
                // Only patch stack pointer inits that cross the point where
                // new stack variables are placed (self.pre_offset)
                if off1 <= self.pre_offset && off2 > self.pre_offset ||
                    off2 <= self.pre_offset && off1 > self.pre_offset
                {
                    self.patch_alt_stack_pointer_init(addr, extra_alloc, add_result);
                }
            }
            let mut prev = E::VirtualAddress::from_u64(0);
            for &addr in &self.across_pre_offset_accesses {
                if addr == prev {
                    // May be common, but not common enough to need a hashmap?
                    continue;
                }
                prev = addr;
                self.patch_low_stack_access(addr, extra_alloc, add_result);
            }
        }
        if !unwind_patch_addresses.is_empty() {
            self.patch_unwind_info(&unwind_patch_addresses, extra_alloc, unwind, add_result);
        }
    }

    /// Returns instruction end for unwind info patching (Unwind info insturction offsets
    /// for instruction end)
    fn patch_stack_alloc<Cb>(
        &self,
        address: E::VirtualAddress,
        extra_alloc: u32,
        add_result: &mut Cb,
    ) -> Option<E::VirtualAddress>
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't read instruction @ {:?}", address);
                return None;
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
            None
        } else {
            match *bytes {
                // add/sub rsp, imm32
                [0x48, 0x81, 0xc4 | 0xec, ..] => {
                    let old_alloc = LittleEndian::read_u32(&bytes[3..]) as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[2] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 7, value, add_result);
                    Some(address + 7)
                }
                // add/sub rsp, imm8
                [0x48, 0x83, 0xc4 | 0xec, ..] => {
                    let old_alloc = bytes[3] as i8 as i32;
                    let new_alloc = old_alloc.saturating_add(extra_alloc as i32);
                    let value = match bytes[3] == 0xc4 {
                        true => new_alloc,
                        false => 0i32.wrapping_sub(new_alloc),
                    };
                    self.add_esp_add(address, 4, value, add_result);
                    Some(address + 4)
                }
                _ => {
                    dat_warn!(self, "Can't patch stack alloc @ {:?}", address);
                    None
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
                // lea reg, [reg + imm8/32]
                [rex, 0x8d, modrm, maybe_sib, ..]
                    if rex & 0xf8 == 0x48 &&
                        matches!(modrm & 0xc0, 0x40 | 0x80) &&
                        (modrm & 7 != 4 || maybe_sib == 0x24) =>
                {
                    let mut buffer = [0u8; 8];
                    buffer.copy_from_slice(&bytes[..8]);
                    let imm_offset = if modrm & 7 == 4 {
                        4
                    } else {
                        3
                    };
                    let (offset, old_len) = if modrm & 0xc0 == 0x40 {
                        // imm8
                        (buffer[imm_offset] as i8 as i32, imm_offset + 1)
                    } else {
                        // imm32
                        (LittleEndian::read_i32(&buffer[imm_offset..]), imm_offset + 4)
                    };
                    let new_offset = if offset >= 0 {
                        offset.wrapping_add(extra_alloc as i32)
                    } else {
                        offset.wrapping_sub(extra_alloc as i32)
                    };
                    // If using imm8, the 3 high bytes written here will just
                    // be ignored
                    LittleEndian::write_i32(&mut buffer[imm_offset..], new_offset);
                    if new_offset > 0x7f || new_offset < -0x80 {
                        // Convert to imm32 if new_offset doesn't fit in imm8
                        buffer[2] = buffer[2] & !0xc0 | 0x80;
                        add_result(address, &buffer[..(imm_offset + 4)], old_len);
                    } else {
                        // If new offset fits in imm8, old offset should have too
                        debug_assert!(buffer[2] & 0xc0 == 0x40 && old_len == imm_offset + 1);
                        add_result(address, &buffer[..(imm_offset + 1)], old_len);
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
            dat_warn!(self, "Can't patch low stack access @ {:?}", address);
        } else {
            let mut buffer = [0u8; 0x18];
            buffer.copy_from_slice(&bytes[..0x18]);
            let mut main_opcode_pos = 0;
            while main_opcode_pos < buffer.len() &&
                x86_64_instruction_info::is_prefix(buffer[main_opcode_pos])
            {
                main_opcode_pos += 1;
            }
            if main_opcode_pos >= buffer.len() - 8 {
                dat_warn!(self, "Can't patch low stack access @ {:?}", address);
                return;
            }
            let main_op = &mut buffer[main_opcode_pos..];
            let opcode = match main_op[0] == 0x0f {
                true => 0x100 + main_op[1] as usize,
                false => main_op[0] as usize
            };
            let params_pos = if opcode < 0x100 { 1 } else { 2 };
            if !x86_64_instruction_info::is_modrm_instruction(opcode) {
                dat_warn!(self, "Can't patch low stack access @ {:?}", address);
                return;
            }
            let modrm = main_op[params_pos];
            if matches!(modrm & 0xc0, 0x40 | 0x80) == false {
                dat_warn!(self, "Can't patch low stack access @ {:?}", address);
                return;
            }
            // Can't calculate old length otherwise unless x86_64_instruction_info also
            // adds non-modrm imm size function
            let old_len = match
                super::instruction_length::<E::VirtualAddress>(self.binary, address)
            {
                Some(s) => s as usize,
                None => {
                    dat_warn!(self, "Can't read instruction @ {:?}", address);
                    return;
                }
            };
            let imm_pos = if modrm & 7 == 4 {
                params_pos + 2
            } else {
                params_pos + 1
            };
            let imm = if modrm & 0xc0 == 0x40 {
                main_op[imm_pos] as i8 as i32
            } else {
                LittleEndian::read_i32(&main_op[imm_pos..])
            };
            let new_imm = if imm < 0 {
                imm.wrapping_sub(extra_alloc as i32)
            } else {
                imm.wrapping_add(extra_alloc as i32)
            };
            if let Ok(new_imm) = i8::try_from(new_imm) {
                main_op[params_pos] = (modrm & !0xc0) | 0x40;
                main_op[imm_pos] = new_imm as u8;
                add_result(address, &buffer[..(main_opcode_pos + imm_pos + 1)], old_len);
            } else {
                main_op[params_pos] = (modrm & !0xc0) | 0x80;
                LittleEndian::write_i32(&mut main_op[imm_pos..], new_imm);
                add_result(address, &buffer[..(main_opcode_pos + imm_pos + 4)], old_len);
            }
        }
    }

    fn patch_unwind_info<Cb>(
        &self,
        // End of stack alloc instruction
        patch_addresses: &[E::VirtualAddress],
        extra_alloc: u32,
        unwind: &UnwindFunctions,
        add_result: &mut Cb,
    )
    where Cb: FnMut(E::VirtualAddress, &[u8], usize),
    {
        let extra_alloc_words = extra_alloc / 8;
        let binary = self.binary;
        let unwind_info = unwind.function_unwind_info_address(binary, self.entry)
            .and_then(|x| Some((x, binary.slice_from_address_to_end(x).ok()?)));
        let (unwind_info, unwind_info_bytes) = match unwind_info {
            Some(s) => s,
            None => {
                dat_warn!(self, "Unwind info not found for {:?}", self.entry);
                return;
            }
        };
        if unwind.unwind_info_refcount(binary, unwind_info) != 1 {
            // Could make work by asking patcher to either allocate
            // completely new unwind info (If windows doesn't care about it
            // not being in the exe), or by copying the entire function to
            // new memory and dynamically adding unwind info for it.
            // But this branch is likely never hit so not going to do that work now.
            dat_warn!(self, "Unwind info for {:?} is shared by other functions", self.entry);
            return;
        }
        let failed = (|| {
            let &prologue_length = unwind_info_bytes.get(1)?;
            let &unwind_code_count = unwind_info_bytes.get(2)?;
            let unwind_codes = unwind_info_bytes.get(4..)?
                .get(..(unwind_code_count as usize * 2))?;
            let mut new_codes = ArrayVec::<u8, 64>::new();
            new_codes.try_extend_from_slice(unwind_codes).ok()?;
            let mut changed = false;
            for &addr in patch_addresses {
                let func_relative = match addr.as_u64().checked_sub(self.entry.as_u64())
                    .and_then(|x| u8::try_from(x).ok())
                {
                    Some(s) => s,
                    None => continue,
                };
                if func_relative > prologue_length {
                    continue;
                }
                let mut pos = 0usize;
                while pos < new_codes.len() {
                    let (rel_addr, opcode) = match new_codes.get(pos..(pos + 2)) {
                        Some(s) => (s[0], s[1]),
                        None => break,
                    };
                    if rel_addr == func_relative {
                        let op = opcode & 0xf;
                        if op == 2 {
                            // Small alloc
                            let old = opcode >> 4;
                            let new = (old as u32).checked_add(extra_alloc_words)?;
                            if new < 0x10 {
                                // Can keep as small alloc
                                new_codes[pos + 1] = ((new as u8) << 4) | 2;
                            } else {
                                // Grow to large alloc
                                // Arrayvec doesn't have nice way to insert u16, so just
                                // inserting high byte followed by low byte.
                                // Rarely used code anyway.
                                let new = u16::try_from(new).ok()?;
                                new_codes[pos + 1] = 0x01;
                                new_codes.try_insert(pos + 2, (new >> 8) as u8).ok()?;
                                new_codes.try_insert(pos + 2, new as u8).ok()?;
                            }
                        } else if op == 1 {
                            // Large alloc
                            let old_bytes = new_codes.get_mut((pos + 2)..(pos + 4))?;
                            let old = LittleEndian::read_u16(old_bytes);
                            let new = (old as u32).checked_add(extra_alloc_words)?;
                            LittleEndian::write_u16(old_bytes, new as u16);
                            if new & 0xffff_0000 != 0 {
                                let hi_add = (new >> 16) as u16;
                                if opcode & 0xf0 == 0x10 {
                                    // Was already large alloc, just increment it by 1
                                    let old_bytes_hi = new_codes.get_mut((pos + 4)..(pos + 6))?;
                                    let new_hi = LittleEndian::read_u16(old_bytes_hi)
                                        .checked_add(hi_add)?;
                                    LittleEndian::write_u16(old_bytes_hi, new_hi);
                                } else {
                                    // Grow to large alloc
                                    new_codes[pos + 1] = 0x11;
                                    new_codes.try_insert(pos + 4, (hi_add >> 8) as u8).ok()?;
                                    new_codes.try_insert(pos + 6, hi_add as u8).ok()?;
                                }
                            } else {
                                // No need to consider large alloc u16 didn't overflow
                            }
                        } else {
                            // Don't know how to handle this opcode
                            return None;
                        }
                        changed = true;
                        break;
                    } else {
                        // Opcode is 0xf, but for opcode 1 first bit of param
                        // affects the opcode length
                        static UNWIND_OPCODE_PARAM_LENGTHS: [u8; 0x20] = [
                            1, 2, 1, 1, 2, 3, 0xff, 0xff,   2, 3, 1, 0xff, 0xff, 0xff, 0xff, 0xff,
                            1, 3, 1, 1, 2, 3, 0xff, 0xff,   2, 3, 1, 0xff, 0xff, 0xff, 0xff, 0xff,
                        ];
                        let length = UNWIND_OPCODE_PARAM_LENGTHS[opcode as usize & 0x1f];
                        pos += length as usize * 2;
                    }
                }
            }
            if changed {
                if new_codes.len() > unwind_codes.len() {
                    // If the code count was not even, there is
                    // padding u16 that can now be used. Otherwise
                    // will have to do something more complex.
                    let can_use_padding = unwind_codes.len() - new_codes.len() == 2 &&
                        unwind_code_count & 1 == 1;
                    if can_use_padding {
                        add_result(unwind_info + 2, &[unwind_code_count.checked_add(1)?], 1);
                        add_result(unwind_info + 4, &new_codes, new_codes.len());
                    } else {
                        dat_warn!(
                            self, "Can't fit new unwind codes for function {:?}", self.entry
                        );
                        return None;
                    }
                } else {
                    add_result(unwind_info + 4, &new_codes, new_codes.len());
                }
            }
            Some(())
        })().is_none();
        if failed {
            dat_warn!(self, "Unwind patch for {:?} failed", self.entry);
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
