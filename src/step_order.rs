use std::rc::Rc;

use scarf::{BinaryFile, DestOperand, Operand, Operation};
use scarf::analysis::{self, FuncAnalysis, AnalysisState,Cfg, Control};
use scarf::exec_state::{InternMap};
use scarf::operand::OperandContext;

use crate::{
    Analysis, OptionExt, find_callers, entry_of_until, single_result_assign, EntryOf,
};
use crate::switch::{full_switch_info};

use scarf::exec_state::{ExecutionState, VirtualAddress};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepOrderHiddenHook<Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Rc<Operand>,
    },
    Separate(Va),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SecondaryOrderHook<Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Rc<Operand>,
    },
    Separate(Va),
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
pub fn step_secondary_order_hook_info<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: &'e OperandContext,
    mut cfg: Cfg<'e, E, analysis::DefaultState>,
    func_entry: E::VirtualAddress,
    jump_addr: E::VirtualAddress,
    unit: &Rc<Operand>,
) -> Option<SecondaryOrderHook<E::VirtualAddress>> {
    fn resolve_at_addr<'f, F: ExecutionState<'f>>(
        binary: &'f BinaryFile<F::VirtualAddress>,
        ctx: &'f OperandContext,
        start: F::VirtualAddress,
        unresolved: &Rc<Operand>,
        resolve_pos: F::VirtualAddress,
    ) -> Option<Rc<Operand>> {
        struct Analyzer<'c, 'g, G: ExecutionState<'g>> {
            resolve_pos: G::VirtualAddress,
            unresolved: &'c Rc<Operand>,
            result: Option<Rc<Operand>>,
        }
        impl<'c, 'g, G: ExecutionState<'g>> scarf::Analyzer<'g> for Analyzer<'c, 'g, G> {
            type State = analysis::DefaultState;
            type Exec = G;
            fn operation(&mut self, ctrl: &mut Control<'g, '_, '_, Self>, op: &Operation) {
                if ctrl.address() == self.resolve_pos {
                    self.result = Some(ctrl.resolve(self.unresolved));
                    ctrl.end_analysis();
                }
                match op {
                    Operation::Jump { .. } | Operation::Return(_) => ctrl.end_analysis(),
                    _ => (),
                }
            }
        }

        let mut analysis = FuncAnalysis::<F, _>::new(binary, ctx, start);
        let mut analyzer = Analyzer {
            resolve_pos,
            unresolved,
            result: None,
        };
        analysis.analyze(&mut analyzer);
        analyzer.result
    }

    // Return address and unresolved unit at address
    fn find_secondary_order_access<'f, F: ExecutionState<'f>>(
        binary: &'f BinaryFile<F::VirtualAddress>,
        ctx: &'f OperandContext,
        start: F::VirtualAddress,
        unit: &Rc<Operand>,
    ) -> Option<(F::VirtualAddress, Rc<Operand>)> {
        struct Analyzer<'c, 'g, G: ExecutionState<'g>> {
            result: Option<(G::VirtualAddress, Rc<Operand>)>,
            unit: &'c Rc<Operand>,
        }
        impl<'c, 'g, G: ExecutionState<'g>> scarf::Analyzer<'g> for Analyzer<'c, 'g, G> {
            type State = analysis::DefaultState;
            type Exec = G;
            fn operation(&mut self, ctrl: &mut Control<'g, '_, '_, Self>, op: &Operation) {
                let ctx = ctrl.ctx();
                match op {
                    Operation::Move(_, val, _) => {
                        let val = ctrl.resolve(val);
                        if let Some(result) = self.check(&val, ctrl) {
                            self.result = Some((ctrl.address(), result));
                            ctrl.end_analysis();
                        }
                    }
                    Operation::SetFlags(arith, _) => {
                        let op = ctx.eq(&arith.left, &arith.right);
                        let val = ctrl.resolve(&op);
                        if let Some(result) = self.check(&val, ctrl) {
                            self.result = Some((ctrl.address(), result));
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
        }
        impl<'c, 'g, G: ExecutionState<'g>> Analyzer<'c, 'g, G> {
            fn check(
                &mut self,
                val: &Rc<Operand>,
                ctrl: &mut Control<'g, '_, '_, Self>,
            ) -> Option<Rc<Operand>> {
                let (state, i) = ctrl.exec_state();
                let result = val.if_memory()
                    .and_then(|mem| mem.address.if_arithmetic_add())
                    .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                    .and_then(|(c, other)| if c == 0xa6 && other == self.unit {
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
                    .and_then(|(c, other)| if c == 0xa6 && other == self.unit {
                        Some(other)
                    } else {
                        None
                    });
                if let Some(unit) = result.and_then(|x| state.unresolve(x, i)) {
                    return Some(unit);
                }
                None
            }
        }

        let mut analysis = FuncAnalysis::<F, _>::new(binary, ctx, start);
        let mut analyzer = Analyzer {
            result: None,
            unit,
        };
        analysis.analyze(&mut analyzer);
        analyzer.result
    }

    cfg.calculate_node_indices();
    let node = cfg.nodes()
        .find(|n| n.address < jump_addr && n.node.end_address >= jump_addr)?;
    let addr = node.address;
    if addr == func_entry {
        // Can't hook it inline since a separate func tail calls the orders.
        Some(SecondaryOrderHook::Separate(addr))
    } else {
        let resolved = resolve_at_addr::<E>(binary, ctx, addr, &unit, jump_addr)?;
        let (entry, unit_at_hook) =
            find_secondary_order_access::<E>(binary, ctx, addr, &resolved)?;
        let end = cfg.immediate_postdominator(node.index)?;

        Some(SecondaryOrderHook::Inlined {
            entry,
            exit: end.address,
            unit: unit_at_hook,
        })
    }
}

pub fn find_order_nuke_track<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>
) -> Option<E::VirtualAddress> {
    find_order_function(analysis, 0x81)
}

pub fn find_order_function<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    order: u32,
) -> Option<E::VirtualAddress> {
    // Just take the last call when [ecx+4d] has been set to correct order.
    // Also guess long jumps as tail calls
    struct Analyzer<'f, F: ExecutionState<'f>> {
        result: Option<F::VirtualAddress>,
        start: F::VirtualAddress,
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
    impl<'a, F: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, F> {
        type State = State;
        type Exec = F;
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
                                    let ecx = ctrl.ctx().register_ref(1);
                                    // Tail call needs to have this == orig this
                                    if ctrl.resolve(ecx) == *ecx {
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
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut interner = InternMap::new();
    let mut state = E::initial_state(ctx, binary, &mut interner);
    let dest = DestOperand::from_oper(
        &ctx.mem8(&ctx.add(ctx.register_ref(1), &ctx.constant(0x4d)))
    );
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

fn step_order_hook_info<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    func_entry: E::VirtualAddress,
) -> Option<StepOrderHiddenHook<E::VirtualAddress>> {
    /// Finds `cmp order, 0xb0` jump that is the first thing done in step_order_hidden,
    /// `addr` being the function that step_order_hidden has been inlined to.
    struct Analyzer<'f, F: ExecutionState<'f>> {
        // Jump addr, unit unresolved
        result: Option<(F::VirtualAddress, Rc<Operand>)>,
    }

    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation) {
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

    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut analyzer = Analyzer::<E> {
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
            entry: skip_past_calls::<E>(addr, ctx, binary),
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
fn skip_past_calls<'e, E: ExecutionState<'e>>(
    start: E::VirtualAddress,
    ctx: &'e OperandContext,
    binary: &'e BinaryFile<E::VirtualAddress>,
) -> E::VirtualAddress {
    struct Analyzer<'f, F: ExecutionState<'f>> {
        result: F::VirtualAddress,
    }

    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Jump { .. } => ctrl.end_analysis(),
                Operation::Call(..) => {
                    self.result = ctrl.current_instruction_end();
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: start,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, start);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub fn step_order<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let order_issuing = analysis.order_issuing();
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let ctx = analysis.ctx;
    let switches = analysis.switch_tables();

    let init_arbiter_callers = order_issuing.order_init_arbiter.iter().flat_map(|&o| {
        find_callers(analysis, o)
    }).collect::<Vec<_>>();
    let mut result = None;
    for caller in init_arbiter_callers {
        let val = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = IsStepOrder {
                ok: false,
                call_found: false,
                caller,
                switches: &switches,
                analysis,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if analyzer.ok {
                EntryOf::Ok(entry)
            } else if analyzer.call_found {
                EntryOf::Stop
            } else {
                EntryOf::Retry
            }
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}


struct IsStepOrder<'a, 'e, E: ExecutionState<'e>> {
    ok: bool,
    call_found: bool,
    caller: E::VirtualAddress,
    switches: &'a [crate::SwitchTable<E::VirtualAddress>],
    analysis: &'a mut Analysis<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for IsStepOrder<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(_) => {
                if ctrl.address() == self.caller {
                    self.call_found = true;
                }
            }
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                self.ok = to.if_mem32()
                    .and_then(|x| x.if_arithmetic_add())
                    .and_either(|x| x.if_constant())
                    .map(|(c, _)| E::VirtualAddress::from_u64(c))
                    .and_then(|addr| {
                        self.switches.binary_search_by_key(&addr, |x| x.address).ok()
                            .map(|x| &self.switches[x])
                    })
                    .and_then(|switch| {
                        full_switch_info(self.analysis, switch)
                    })
                    .filter(|(switch, _)| switch.cases.len() >= 0xad)
                    .is_some();
                if self.ok {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub fn step_order_hidden<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Vec<StepOrderHiddenHook<E::VirtualAddress>> {
    let switches = analysis.switch_tables();

    let result = switches.iter().filter_map(|switch| {
        if switch.cases.len() < 11 || switch.cases.len() > 12 {
            None
        } else {
            full_switch_info(analysis, switch)
        }
    }).filter(|&(ref switch, _entry)| {
        if switch.cases.len() < 0xa8 {
            return false;
        }
        let default_case = switch.cases[0x1];
        switch.cases.iter().take(0x90).enumerate().all(|(i, &x)| {
            match i {
                0x0 | 0x3 | 0x4 | 0x11 | 0x16 | 0x17 | 0x18 | 0x1d | 0x53 | 0x5c | 0x61 |
                    0x7d =>
                {
                    x != default_case
                }
                _ => x == default_case,
            }
        })
    }).map(|(_, entry)| {
        entry
    }).collect::<Vec<_>>();
    let result = result.iter().filter_map(|&addr| {
        step_order_hook_info(analysis, addr)
    }).collect();
    result
}

pub fn step_secondary_order<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Vec<SecondaryOrderHook<E::VirtualAddress>> {
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let ctx = analysis.ctx;

    let step_order = analysis.step_order();
    let mut callers = step_order.iter()
        .flat_map(|&x| find_callers(analysis, x))
        .collect::<Vec<_>>();
    callers.sort();
    callers.dedup();
    let mut checked_funcs = Vec::new();
    let result = callers.into_iter().filter_map(|caller| {
        entry_of_until(binary, &funcs, caller, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = StepSecondaryOrderAnalyzer::<E> {
                result: None,
                pre_result: None,
                call_found: false,
                inlining: false,
                caller,
                checked_funcs: &mut checked_funcs,
                binary,
                ctx,
            };
            analysis.analyze(&mut analyzer);
            if let Some(res) = analyzer.result {
                return EntryOf::Ok(res);
            }
            if let Some((jump_addr, unit)) = analyzer.pre_result {
                let (cfg, _) = analysis.finish();
                let res = step_secondary_order_hook_info(
                    binary,
                    &ctx,
                    cfg,
                    entry,
                    jump_addr,
                    &unit,
                );
                if let Some(res) = res {
                    return EntryOf::Ok(res);
                }
            }
            if analyzer.call_found {
                EntryOf::Stop
            } else {
                EntryOf::Retry
            }
        }).into_option()
    }).collect::<Vec<_>>();
    result
}

struct StepSecondaryOrderAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<SecondaryOrderHook<E::VirtualAddress>>,
    pre_result: Option<(E::VirtualAddress, Rc<Operand>)>,
    call_found: bool,
    inlining: bool,
    caller: E::VirtualAddress,
    checked_funcs: &'a mut Vec<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: &'e OperandContext,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    StepSecondaryOrderAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        if self.pre_result.is_some() {
            return;
        }
        // step_secondary_order is supposed to begin with a check if the order
        // is 0x95 (Hallucinated unit)
        match op {
            Operation::Call(dest) => {
                if ctrl.address() == self.caller {
                    self.call_found = true;
                }
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if !self.inlining && !self.checked_funcs.iter().any(|&x| x == dest) {
                        self.inlining = true;
                        self.checked_funcs.push(dest);
                        let mut analysis = FuncAnalysis::new(self.binary, self.ctx, dest);
                        analysis.analyze(self);
                        if let Some((jump_addr, unit)) = self.pre_result.take() {
                            let (cfg, _) = analysis.finish();
                            self.result = step_secondary_order_hook_info(
                                self.binary,
                                self.ctx,
                                cfg,
                                dest,
                                jump_addr,
                                &unit,
                            );
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                        self.inlining = false;
                    }
                }
            }
            Operation::Jump { ref condition, .. } => {
                let condition = ctrl.resolve(condition);
                let unit = step_secondary_order_hallu_jump_check(&condition);
                let (state, i) = ctrl.exec_state();
                if let Some(unit) = unit.and_then(|u| state.unresolve(&u, i)) {
                    self.pre_result = Some((ctrl.address(), unit));
                }
            }
            _ => (),
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.pre_result.is_some() {
            ctrl.end_analysis();
        }
    }
}
