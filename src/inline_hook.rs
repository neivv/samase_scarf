use std::fmt;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::OperandHashByAddress;
use scarf::{ArithOpType, BinaryFile, DestOperand, OperandCtx, Operand, OperandType, Operation};

use crate::hash_map::HashSet;
use crate::util::ControlExt;

#[derive(Copy, Clone)]
pub struct InlineHookState {
    /// Bits for registers that need to be read/written.
    /// Bit 4 (esp) is never set.
    pub registers: u16,
    /// How many bytes of stack after esp need to be saved.
    ///
    /// Will be rounded to word alignment.
    pub stack_size: u16,
    /// Registers that should be preserved across entry/exit.
    pub kept_registers: u16,
    /// Registers that are clobbered by the hook.
    pub clobber_registers: u16,
    pub esp_offsets: EspOffsetRegs,
}

impl InlineHookState {
    pub(crate) fn remove_entry_register(&mut self, reg: u8) {
        self.registers &= !(1 << reg);
    }
}

impl fmt::Debug for InlineHookState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut helper = f.debug_struct("InlineHookState");
        helper
            .field("enter_regs", &format_args!("{:04x}", self.registers))
            .field("stack_size", &format_args!("{:04x}", self.stack_size))
            .field("kept_regs", &format_args!("{:04x}", self.kept_registers))
            .field("clobber_regs", &format_args!("{:04x}", self.clobber_registers));
        for i in 0..self.esp_offsets.regs.len() {
            let reg = self.esp_offsets.regs[i];
            let offset = self.esp_offsets.offsets[i];
            if reg == u8::MAX {
                break;
            }
            helper.field("esp_offset_reg", &(reg, offset));
        }
        helper.finish()
    }
}

#[derive(Copy, Clone)]
pub struct EspOffsetRegs {
    /// Forms (u8, i16) pairs for (register_id, offset) for registers relative to
    /// esp, such as ebp is often on x86. (u8::MAX, 0) is used for end of list.
    regs: [u8; 4],
    offsets: [i16; 4],
}

impl EspOffsetRegs {
    pub(crate) fn from_entry_state<'e, E: ExecutionState<'e>>(
        state: &mut E,
        ctx: OperandCtx<'e>,
    ) -> Option<EspOffsetRegs> {
        let register_count = if E::VirtualAddress::SIZE == 4 { 8 } else { 16 };
        let mut pos = 0;
        let mut result = EspOffsetRegs {
            regs: [u8::MAX; 4],
            offsets: [0; 4],
        };
        for i in 0..register_count {
            if i == 4 {
                continue;
            }
            let value = state.resolve_register(i);
            if let OperandType::Arithmetic(arith) =  value.ty() {
                if arith.left == ctx.register(4) {
                    if matches!(arith.ty, ArithOpType::Add | ArithOpType::Sub) {
                        if let Some(c) = arith.right.if_constant() {
                            let c = if arith.ty == ArithOpType::Sub {
                                0i64.wrapping_sub(c as i64)
                            } else {
                                c as i64
                            };

                            if pos >= result.regs.len() {
                                return None;
                            }
                            let offset = i16::try_from(c).ok()?;
                            result.regs[pos] = i;
                            result.offsets[pos] = offset;
                            pos += 1;
                        }
                    }
                }
            }
        }
        Some(result)
    }

    pub fn iter(&self) -> impl Iterator<Item = (u8, i16)> + '_ {
        self.regs.iter().copied()
            .zip(self.offsets.iter().copied())
            .take_while(|x| x.0 != u8::MAX)
    }
}

/// esp_offsets should be created from state representing entry
pub fn inline_hook_state<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    hook_entry: E::VirtualAddress,
    hook_exit: E::VirtualAddress,
    esp_offsets: EspOffsetRegs,
) -> Option<InlineHookState> {
    let register_count = if E::VirtualAddress::SIZE == 4 { 8 } else { 16 };
    let mut analysis = FuncAnalysis::new(binary, ctx, hook_entry);
    let mut analyzer = Analyzer::<E> {
        end: hook_exit,
        registers: 0,
        call_registers: 0,
        stack_size: 0,
        checked_values: HashSet::with_capacity_and_hasher(32, Default::default()),
        ctx,
        error: false,
        is_entry: true,
        state: None,
    };
    analysis.analyze(&mut analyzer);
    if analyzer.error {
        return None;
    }
    let mut entry_registers = analyzer.registers | analyzer.call_registers;
    let entry_stack = analyzer.stack_size;
    // If None, the end was not reached at all
    let mut entry_end_state = analyzer.state?;
    let mut clobber_registers = 0;
    for i in 0..register_count {
        let reg = ctx.register(i);
        if entry_end_state.resolve_register(i) != reg {
            clobber_registers |= 1 << i;
        }
    }
    if clobber_registers & 0x10 != 0 {
        // Clobbering rsp is not supported
        // But since 32bit assumes it to be unknown on every call,
        // assume it to be fine there anyway..
        if E::VirtualAddress::SIZE == 4 {
            clobber_registers &= !0x10;
        } else {
            return None;
        }
    }

    let mut analysis = FuncAnalysis::new(binary, ctx, hook_exit);
    let mut analyzer = Analyzer::<E> {
        end: hook_entry,
        registers: 0,
        call_registers: 0,
        stack_size: 0,
        checked_values: analyzer.checked_values,
        ctx,
        error: false,
        is_entry: false,
        state: None,
    };
    analyzer.checked_values.clear();
    analysis.analyze(&mut analyzer);
    if analyzer.error {
        return None;
    }
    let mut exit_registers = analyzer.registers | analyzer.call_registers;

    // -- Verify that any exit_registers don't get changed by the inline part
    for i in 0..register_count {
        let mask = 1 << i;
        if exit_registers & mask != 0 {
            let reg = ctx.register(i);
            let end_reg = entry_end_state.resolve_register(i);
            if end_reg != reg {
                if analyzer.registers & mask == 0 {
                    // This register was only used in call param guess, assume that it isn't
                    // actually needed to be preserved.
                    exit_registers &= !mask;
                } else {
                    // If this still was not-undefined, it could be made to work
                    // by having the hook return point assign this value to the reg,
                    // but this doesn't seem to be a case that will happen ever.
                    debug!("Register didn't stay stable across hook: {}", end_reg);
                    return None;
                }
            }
        }
    }

    // -- Keep only esp offsets which are in entry_registers --
    // Also clear those bits from entry_registers
    let mut write_pos = 0;
    let mut read_pos = 0;
    let mut esp_offsets = esp_offsets;
    while read_pos < esp_offsets.regs.len() {
        let reg = esp_offsets.regs[read_pos];
        if reg >= 16 {
            break;
        }
        let mask = 1 << reg;
        if entry_registers & mask != 0 {
            entry_registers &= !mask;
            // This register has to be kept for esp offset
            if read_pos != write_pos {
                let offset = esp_offsets.offsets[read_pos];
                esp_offsets.regs[write_pos] = reg;
                esp_offsets.offsets[write_pos] = offset;
            }
            write_pos += 1;
        }
        read_pos += 1;
    }
    while write_pos < esp_offsets.regs.len() {
        esp_offsets.regs[write_pos] = u8::MAX;
        write_pos += 1;
    }

    Some(InlineHookState {
        registers: entry_registers,
        stack_size: entry_stack,
        kept_registers: exit_registers,
        clobber_registers,
        esp_offsets,
    })
}

struct Analyzer<'e, E: ExecutionState<'e>> {
    end: E::VirtualAddress,
    registers: u16,
    /// Since registers used in call arguments is a guess here, have
    /// looser rules for these.
    call_registers: u16,
    stack_size: u16,
    checked_values: HashSet<OperandHashByAddress<'e>>,
    ctx: OperandCtx<'e>,
    error: bool,
    is_entry: bool,
    state: Option<E>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() == self.end {
            if self.is_entry {
                if let Some(ref mut old) = self.state {
                    let exec_state = ctrl.exec_state();
                    if let Some(new) = E::merge_states(
                        old,
                        exec_state,
                        &mut scarf::exec_state::MergeStateCache::new(),
                    ) {
                        self.state = Some(new);
                    }
                } else {
                    self.state = Some(ctrl.exec_state().clone());
                }
            }
            ctrl.end_branch();
            return;
        }
        match *op {
            Operation::Move(ref dest, value, cond) => {
                if let Some(cond) = cond {
                    self.check_unresolved_value(ctrl, cond, false);
                }
                if matches!(*dest, DestOperand::Memory(..)) {
                    self.check_unresolved_value(ctrl, value, false);
                }
            }
            Operation::SetFlags(ref flags) => {
                self.check_unresolved_value(ctrl, flags.left, false);
                self.check_unresolved_value(ctrl, flags.right, false);
            }
            Operation::Jump { condition, .. } => {
                self.check_unresolved_value(ctrl, condition, false);
            }
            Operation::Return(..) => {
                if self.is_entry {
                    debug!("Reached return during inline part");
                    self.error = true;
                }
            }
            Operation::Call(..) => {
                // Assuming that all register arguments are used
                // (conservative guess, shouldn't hurt, probably false positives on 64bit)
                let ctx = ctrl.ctx();
                if E::VirtualAddress::SIZE == 4 {
                    self.check_unresolved_value(ctrl, ctx.register(1), true);
                } else {
                    for i in [1, 2, 8, 9] {
                        self.check_unresolved_value(ctrl, ctx.register(i), true);
                    }
                }
                if E::VirtualAddress::SIZE == 4 && self.is_entry {
                    ctrl.skip_call_preserve_esp();
                    ctrl.move_resolved(&DestOperand::Register64(4), ctx.custom(0));
                }
            }
            _ => (),
        }
    }
}

impl<'e, E: ExecutionState<'e>> Analyzer<'e, E> {
    fn check_unresolved_value(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        value: Operand<'e>,
        is_call: bool,
    ) {
        let value = ctrl.resolve(value);
        self.check_resolved_value(value, is_call);
    }

    fn check_resolved_value(
        &mut self,
        value: Operand<'e>,
        is_call: bool,
    ) {
        match *value.ty() {
            OperandType::Register(reg) => {
                if reg != 4 {
                    if is_call {
                        self.call_registers |= 1 << (reg & 15);
                    } else {
                        self.registers |= 1 << (reg & 15);
                    }
                }
            }
            OperandType::Memory(ref mem) => {
                if !self.checked_values.insert(value.hash_by_address()) {
                    return;
                }
                let (base, offset) = mem.address();
                if base == self.ctx.register(4) {
                    if let Some(offset) = offset.checked_add(mem.size.bytes().into())
                        .and_then(|x| u16::try_from(x).ok())
                        // Round to word size
                        .and_then(|x| (x | (E::VirtualAddress::SIZE - 1) as u16).checked_add(1))
                    {
                        self.stack_size = self.stack_size.max(offset);
                    } else {
                        debug!("Too large esp offset {:x}", offset);
                        self.error = true;
                        return;
                    }
                } else if E::VirtualAddress::SIZE == 4 && base.if_custom() == Some(0) {
                    // Accessed esp after call, and handling for correct esp
                    // offsets after call (Would require analyzing them once and caching
                    // return offset) isn't implemented :/
                    debug!("Esp access after call");
                    self.error = true;
                    return;
                } else {
                    self.check_resolved_value(base, is_call);
                }
            }
            OperandType::Arithmetic(ref arith) => {
                if !self.checked_values.insert(value.hash_by_address()) {
                    return;
                }
                self.check_resolved_value(arith.left, is_call);
                self.check_resolved_value(arith.right, is_call);
            }
            _ => (),
        }
    }
}
