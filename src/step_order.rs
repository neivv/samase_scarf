use std::rc::Rc;

use scarf::{DestOperand, ExecutionStateX86, Operand, Operation, VirtualAddress};
use scarf::analysis::{self, AnalysisState,Cfg, Control};
use scarf::exec_state::{InternMap};
use scarf::operand::OperandContext;

use crate::{Analysis, Error, to_default_base, OptionExt};

use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};
type BinaryFile = scarf::BinaryFile<VirtualAddress>;
type FuncAnalysis<'a, T> = analysis::FuncAnalysis<'a, ExecutionStateX86<'a>, T>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepOrderHiddenHook {
    Inlined {
        entry: VirtualAddress,
        exit: VirtualAddress,
        // Unresolved at entry
        unit: Rc<Operand>,
    },
    Separate(VirtualAddress),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SecondaryOrderHook {
    Inlined {
        entry: VirtualAddress,
        exit: VirtualAddress,
        // Unresolved at entry
        unit: Rc<Operand>,
    },
    Separate(VirtualAddress),
}

pub fn step_secondary_order_inner(
    binary: &BinaryFile,
    addr: VirtualAddress,
    mut state: ExecutionStateX86,
    ctx: &OperandContext,
    mut interner: InternMap,
    errors: &mut Vec<Error>,
) -> Option<SecondaryOrderHook> {
    use scarf::operand_helpers::*;
    let esp = ctx.register(4);
    state.move_to(&DestOperand::from_oper(&esp), operand_sub(esp, ctx.const_4()), &mut interner);
    let mut analysis = FuncAnalysis::with_state(binary, &ctx, addr, state, interner);
    let mut secondary_order_hallu_check = None;
    'outer: while let Some(mut branch) = analysis.next_branch() {
        let mut operations = branch.operations();
        while let Some((op, state, ins_address, i)) = operations.next() {
            match *op {
                Operation::Jump { ref condition, .. } => {
                    let condition = state.resolve(condition, i);
                    let unit = step_secondary_order_hallu_jump_check(&condition);
                    if let Some(unit) = unit.and_then(|u| state.unresolve(&u, i)) {
                        secondary_order_hallu_check = Some((ins_address, unit));
                        break 'outer;
                    }
                }
                _ => (),
            }
        }
    }
    errors.extend(analysis.errors.drain(..).map(|(a, b)| {
        Error::Scarf(to_default_base(binary, a), b)
    }));
    if let Some((jump_addr, unit)) = secondary_order_hallu_check {
        let (cfg, errs) = analysis.finish();
        errors.extend(errs.into_iter().map(|(a, b)| {
            Error::Scarf(to_default_base(binary, a), b)
        }));
        step_secondary_order_hook_info(binary, ctx, cfg, addr, jump_addr, &unit)
    } else {
        None
    }
}

// Checks for comparing secondary_order to 0x95 (Hallucination)
// Returns the unit operand
pub fn step_secondary_order_hallu_jump_check(condition: &Rc<Operand>) -> Option<Rc<Operand>> {
    let condition = Operand::simplified(condition.clone());
    let hallucinated_id_found = condition.iter_no_mem_addr().any(|x| {
        x.if_constant().map(|x| x == 0x95).unwrap_or(false)
    });
    if !hallucinated_id_found {
        return None;
    }
    condition.iter_no_mem_addr()
        .filter_map(|x| x.if_memory())
        .filter_map(|mem| mem.address.if_arithmetic_add())
        .filter_map(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
        .filter(|&(c, _)| c == 0xa6)
        .map(|(_, other)| other.clone())
        .next()
}

// Unit needs to be unresolved
pub fn step_secondary_order_hook_info<'exec>(
    binary: &'exec BinaryFile,
    ctx: &'exec OperandContext,
    mut cfg: Cfg<'exec, ExecutionStateX86<'exec>, analysis::DefaultState>,
    func_entry: VirtualAddress,
    jump_addr: VirtualAddress,
    unit: &Rc<Operand>,
) -> Option<SecondaryOrderHook> {
    fn resolve_at_addr(
        binary: &BinaryFile,
        ctx: &OperandContext,
        start: VirtualAddress,
        unresolved: &Rc<Operand>,
        resolve_pos: VirtualAddress,
    ) -> Option<Rc<Operand>> {
        let mut analysis = FuncAnalysis::new(binary, ctx, start);
        let mut branch = analysis.next_branch()
            .expect("New analysis should always have a branch.");
        let mut ops = branch.operations();
        while let Some((op, state, address, i)) = ops.next() {
            if address == resolve_pos {
                return Some(state.resolve(unresolved, i));
            } else {
                match *op {
                    Operation::Jump { .. } | Operation::Return(_) => return None,
                    _ => (),
                }
            }
        }
        None
    }

    // Return address and unresolved unit at address
    fn find_secondary_order_access(
        binary: &BinaryFile,
        ctx: &OperandContext,
        start: VirtualAddress,
        unit: &Rc<Operand>,
    ) -> Option<(VirtualAddress, Rc<Operand>)> {
        use scarf::operand_helpers::*;

        let check = |val: &Rc<Operand>, state: &mut ExecutionStateX86, i: &mut _| -> Option<Rc<Operand>> {
            let result = val.if_memory()
                .and_then(|mem| mem.address.if_arithmetic_add())
                .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                .and_then(|(c, other)| if c == 0xa6 && other == unit {
                    Some(other)
                } else {
                    None
                });
            if let Some(unit) = result.and_then(|x| state.unresolve(x, i)) {
                return Some(unit);
            }
            let result = val.if_arithmetic_eq()
                .map(|(l, r)| {
                    // Strip == 0 from comparisions
                    Operand::either(l, r, |x| x.if_constant().filter(|&c| c == 0))
                        .and_then(|x| x.1.if_arithmetic_eq())
                        .unwrap_or((l, r))
                })
                .and_then(|(l, r)| Operand::either(l, r, |x| x.if_memory()))
                .filter(|&(_, c)| c.if_constant() == Some(0x95))
                .and_then(|(mem, _)| mem.address.if_arithmetic_add())
                .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                .and_then(|(c, other)| if c == 0xa6 && other == unit {
                    Some(other)
                } else {
                    None
                });
            if let Some(unit) = result.and_then(|x| state.unresolve(x, i)) {
                return Some(unit);
            }
            None
        };

        let mut analysis = FuncAnalysis::new(binary, ctx, start);
        let mut branch = analysis.next_branch()
            .expect("New analysis should always have a branch.");
        let mut ops = branch.operations();
        while let Some((op, state, address, i)) = ops.next() {
            match op {
                Operation::Move(_, val, _) => {
                    let val = state.resolve(val, i);
                    if let Some(result) = check(&val, state, i) {
                        return Some((address, result));
                    }
                }
                Operation::SetFlags(arith, _) => {
                    let op = operand_eq(arith.left.clone(), arith.right.clone());
                    let val = state.resolve(&op, i);
                    if let Some(result) = check(&val, state, i) {
                        return Some((address, result));
                    }
                }
                _ => (),
            }
        }
        None
    }

    cfg.calculate_node_indices();
    let node = cfg.nodes()
        .find(|n| n.address < jump_addr && n.node.end_address >= jump_addr)?;
    let addr = node.address;
    if addr == func_entry {
        // Can't hook it inline since a separate func tail calls the orders.
        Some(SecondaryOrderHook::Separate(addr))
    } else {
        let resolved = resolve_at_addr(binary, ctx, addr, &unit, jump_addr)?;
        let (entry, unit_at_hook) = find_secondary_order_access(binary, ctx, addr, &resolved)?;
        let end = cfg.immediate_postdominator(node.index)?;

        Some(SecondaryOrderHook::Inlined {
            entry,
            exit: end.address,
            unit: unit_at_hook,
        })
    }
}

pub fn find_order_nuke_track<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> Option<VirtualAddress> {
    find_order_function(analysis, ctx, 0x81)
}

pub fn find_order_function<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
    order: u32,
) -> Option<VirtualAddress> {
    use scarf::operand_helpers::*;

    // Just take the last call when [ecx+4d] has been set to correct order.
    // Also guess long jumps as tail calls
    struct Analyzer<'a> {
        result: Option<VirtualAddress>,
        start: VirtualAddress,
        ctx: &'a OperandContext,
    }
    #[derive(Eq, Copy, Clone, PartialEq)]
    enum State {
        HasSwitchJumped,
        NotSwitchJumped,
    }
    impl AnalysisState for State {
        fn merge(&mut self, newer: Self) {
            if newer == State::NotSwitchJumped {
                *self = newer;
            }
        }
    }
    impl<'a> scarf::Analyzer<'a> for Analyzer<'a> {
        type State = State;
        type Exec = ExecutionStateX86<'a>;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Jump { condition, to } => {
                    let condition = ctrl.resolve(&condition);
                    if *ctrl.user_state() == State::HasSwitchJumped {
                        if let Some(1) = condition.if_constant() {
                            if let Some(dest) = ctrl.resolve(&to).if_constant() {
                                let seems_tail_call = (dest < self.start.as_u64()) ||
                                    (
                                        dest > ctrl.address().as_u64() + 0x400 &&
                                        dest > self.start.as_u64() + 0x800
                                    );

                                if seems_tail_call {
                                    let ecx = self.ctx.register(1);
                                    // Tail call needs to have this == orig this
                                    if ctrl.resolve(&ecx) == ecx {
                                        self.result = Some(VirtualAddress::from_u64(dest));
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                    if to.if_memory().is_some() {
                        *ctrl.user_state() = State::HasSwitchJumped;
                    } else {
                        *ctrl.user_state() = State::NotSwitchJumped;
                    }
                }
                Operation::Call(dest) => {
                    if *ctrl.user_state() == State::HasSwitchJumped {
                        if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                            self.result = Some(VirtualAddress::from_u64(dest));
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let step_order = analysis.step_order()?;
    let mut analyzer = Analyzer {
        result: None,
        start: step_order,
        ctx,
    };
    let binary = analysis.binary;
    let mut interner = InternMap::new();
    let mut state = ExecutionStateX86::with_binary(binary, &ctx, &mut interner);
    let dest = DestOperand::from_oper(&mem8(operand_add(ctx.register(1), ctx.constant(0x4d))));
    state.move_to(&dest, ctx.constant(order as u64), &mut interner);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        step_order,
        state,
        State::NotSwitchJumped,
        interner,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub fn step_order_hook_info<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    func_entry: VirtualAddress,
    ctx: &OperandContext,
) -> Option<StepOrderHiddenHook> {
    /// Finds `cmp order, 0xb0` jump that is the first thing done in step_order_hidden,
    /// `addr` being the function that step_order_hidden has been inlined to.
    struct Analyzer {
        // Jump addr, unit unresolved
        result: Option<(VirtualAddress, Rc<Operand>)>,
    }

    impl<'a> scarf::Analyzer<'a> for Analyzer {
        type State = analysis::DefaultState;
        type Exec = ExecutionStateX86<'a>;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            if self.result.is_some() {
                return;
            }
            match op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(&condition);
                    let unit_resolved = condition.iter_no_mem_addr()
                        .find_map(|x| {
                            // b1 > mem8[x + 4d]
                            x.if_arithmetic_gt()
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 0xb1))
                                .and_then(|x| x.if_mem8())
                                .and_then(|x| x.if_arithmetic_add())
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 0x4d))
                        });
                    if let Some(unit) = unit_resolved {
                        if let Some(unresolved) = ctrl.unresolve(&unit) {
                            self.result = Some((ctrl.address(), unresolved));
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let mut analyzer = Analyzer {
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, func_entry);
    analysis.analyze(&mut analyzer);
    let (mut cfg, _errs) = analysis.finish();

    let (jump_addr, unit_at_hook) = analyzer.result?;
    cfg.calculate_node_indices();
    let node = cfg.nodes()
        .find(|n| n.address < jump_addr && n.node.end_address >= jump_addr)?;
    let addr = node.address;
    if addr == func_entry {
        Some(StepOrderHiddenHook::Separate(addr))
    } else {
        let end = cfg.immediate_postdominator(node.index)?;

        Some(StepOrderHiddenHook::Inlined {
            entry: skip_past_calls(addr, ctx, binary),
            exit: end.address,
            unit: unit_at_hook,
        })
    }
}

/// Given
/// start:
///     mov eax, 4
///     call x
///     mov ecx, 8
///     cmp eax, ecx
///     je somewhere
///
/// returns the address after call
fn skip_past_calls(
    start: VirtualAddress,
    ctx: &OperandContext,
    binary: &BinaryFile,
) -> VirtualAddress {
    struct Analyzer {
        result: VirtualAddress,
    }

    impl<'a> scarf::Analyzer<'a> for Analyzer {
        type State = analysis::DefaultState;
        type Exec = ExecutionStateX86<'a>;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Jump { .. } => ctrl.end_analysis(),
                Operation::Call(..) => {
                    self.result = ctrl.current_instruction_end();
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer {
        result: start,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, start);
    analysis.analyze(&mut analyzer);
    analyzer.result
}
