use bumpalo::collections::Vec as BumpVec;

use scarf::{BinaryFile, DestOperand, Operand, Operation};
use scarf::analysis::{self, FuncAnalysis, AnalysisState,Cfg, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::OperandCtx;

use crate::{
    AnalysisCtx, OptionExt, entry_of_until, single_result_assign, EntryOf, ArgCache,
    bumpvec_with_capacity, FunctionFinder, OperandExt, ControlExt,
};
use crate::struct_layouts;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepOrderHiddenHook<'e, Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Operand<'e>,
    },
    Separate(Va),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SecondaryOrderHook<'e, Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Operand<'e>,
    },
    Separate(Va),
}

#[derive(Clone, Copy)]
pub struct DoAttack<'e, Va: VirtualAddress> {
    pub do_attack: Va,
    pub do_attack_main: Va,
    pub last_bullet_spawner: Operand<'e>,
}

// Checks for comparing secondary_order to 0x95 (Hallucination)
// Returns the unit operand
fn step_secondary_order_hallu_jump_check<'e, Va: VirtualAddress>(
    condition: Operand<'e>,
) -> Option<Operand<'e>> {
    let hallucinated_id_found = condition.iter_no_mem_addr().any(|x| {
        x.if_constant().map(|x| x == 0x95).unwrap_or(false)
    });
    if !hallucinated_id_found {
        return None;
    }
    condition.iter_no_mem_addr()
        .filter_map(|x| {
            x.if_mem8()?
                .if_arithmetic_add_const(struct_layouts::unit_secondary_order::<Va>())
        })
        .next()
}

// Unit needs to be unresolved
pub fn step_secondary_order_hook_info<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    mut cfg: Cfg<'e, E, analysis::DefaultState>,
    func_entry: E::VirtualAddress,
    jump_addr: E::VirtualAddress,
    unit: Operand<'e>,
) -> Option<SecondaryOrderHook<'e, E::VirtualAddress>> {
    fn resolve_at_addr<'e, F: ExecutionState<'e>>(
        binary: &'e BinaryFile<F::VirtualAddress>,
        ctx: OperandCtx<'e>,
        start: F::VirtualAddress,
        unresolved: Operand<'e>,
        resolve_pos: F::VirtualAddress,
    ) -> Option<Operand<'e>> {
        struct Analyzer<'e, G: ExecutionState<'e>> {
            resolve_pos: G::VirtualAddress,
            unresolved: Operand<'e>,
            result: Option<Operand<'e>>,
        }
        impl<'g, G: ExecutionState<'g>> scarf::Analyzer<'g> for Analyzer<'g, G> {
            type State = analysis::DefaultState;
            type Exec = G;
            fn operation(&mut self, ctrl: &mut Control<'g, '_, '_, Self>, op: &Operation<'g>) {
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
    fn find_secondary_order_access<'e, F: ExecutionState<'e>>(
        binary: &'e BinaryFile<F::VirtualAddress>,
        ctx: OperandCtx<'e>,
        start: F::VirtualAddress,
        unit: Operand<'e>,
    ) -> Option<(F::VirtualAddress, Operand<'e>)> {
        struct Analyzer<'e, G: ExecutionState<'e>> {
            result: Option<(G::VirtualAddress, Operand<'e>)>,
            unit: Operand<'e>,
        }
        impl<'g, G: ExecutionState<'g>> scarf::Analyzer<'g> for Analyzer<'g, G> {
            type State = analysis::DefaultState;
            type Exec = G;
            fn operation(&mut self, ctrl: &mut Control<'g, '_, '_, Self>, op: &Operation<'g>) {
                let ctx = ctrl.ctx();
                match *op {
                    Operation::Move(_, val, _) => {
                        let val = ctrl.resolve(val);
                        if let Some(result) = self.check(val, ctrl) {
                            self.result = Some((ctrl.address(), result));
                            ctrl.end_analysis();
                        }
                    }
                    Operation::SetFlags(ref arith) => {
                        let op = ctx.eq(arith.left, arith.right);
                        let val = ctrl.resolve(op);
                        if let Some(result) = self.check(val, ctrl) {
                            self.result = Some((ctrl.address(), result));
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
        }
        impl<'e, G: ExecutionState<'e>> Analyzer<'e, G> {
            fn check(
                &mut self,
                val: Operand<'e>,
                ctrl: &mut Control<'e, '_, '_, Self>,
            ) -> Option<Operand<'e>> {
                let result = val.if_mem8()
                    .and_then(|x| {
                        x.if_arithmetic_add_const(
                            struct_layouts::unit_secondary_order::<G::VirtualAddress>()
                        )
                    })
                    .filter(|&x| x == self.unit);
                if let Some(unit) = result.and_then(|x| ctrl.unresolve(x)) {
                    return Some(unit);
                }
                let result = val.if_arithmetic_eq()
                    .map(|(l, r)| {
                        // Strip == 0 from comparisions
                        Operand::either(l, r, |x| x.if_constant().filter(|&c| c == 0))
                            .and_then(|x| x.1.if_arithmetic_eq())
                            .unwrap_or((l, r))
                    })
                    .and_then(|(l, r)| Operand::either(l, r, |x| x.if_mem8()))
                    .filter(|&(_, c)| c.if_constant() == Some(0x95))
                    .and_then(|(addr, _)| {
                        addr.if_arithmetic_add_const(
                            struct_layouts::unit_secondary_order::<G::VirtualAddress>()
                        )
                    })
                    .filter(|&x| x == self.unit);
                if let Some(unit) = result.and_then(|x| ctrl.unresolve(x)) {
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
        let resolved = resolve_at_addr::<E>(binary, ctx, addr, unit, jump_addr)?;
        let (entry, unit_at_hook) =
            find_secondary_order_access::<E>(binary, ctx, addr, resolved)?;
        let end = cfg.immediate_postdominator(node.index)?;

        Some(SecondaryOrderHook::Inlined {
            entry,
            exit: end.address,
            unit: unit_at_hook,
        })
    }
}

pub(crate) fn find_order_nuke_track<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_order: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    find_order_function(analysis, step_order, 0x81)
}

pub(crate) fn find_order_function<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_order: E::VirtualAddress,
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
    impl<'e, F: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, F> {
        type State = State;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Jump { condition, to } => {
                    let condition = ctrl.resolve(condition);
                    if *ctrl.user_state() == State::HasSwitchJumped {
                        if let Some(1) = condition.if_constant() {
                            if let Some(dest) = ctrl.resolve(to).if_constant() {
                                let seems_tail_call = (dest < self.start.as_u64()) ||
                                    (
                                        dest > ctrl.address().as_u64() + 0x400 &&
                                        dest > self.start.as_u64() + 0x800
                                    );

                                if seems_tail_call {
                                    let ecx = ctrl.ctx().register(1);
                                    // Tail call needs to have this == orig this
                                    if ctrl.resolve(ecx) == ecx {
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
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            self.result = Some(VirtualAddress::from_u64(dest));
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer {
        result: None,
        start: step_order,
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut state = E::initial_state(ctx, binary);
    let dest = DestOperand::from_oper(
        ctx.mem8(ctx.add_const(
            ctx.register(1),
            struct_layouts::unit_order::<E::VirtualAddress>(),
        ))
    );
    state.move_to(&dest, ctx.constant(order as u64));
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        step_order,
        state,
        State::NotSwitchJumped,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn step_order_hook_info<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    func_entry: E::VirtualAddress,
) -> Option<StepOrderHiddenHook<'e, E::VirtualAddress>> {
    /// Finds `cmp order, 0xb0` jump that is the first thing done in step_order_hidden,
    /// `addr` being the function that step_order_hidden has been inlined to.
    struct Analyzer<'e, F: ExecutionState<'e>> {
        // Jump addr, unit unresolved
        result: Option<(F::VirtualAddress, Operand<'e>)>,
    }

    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation<'f>) {
            if self.result.is_some() {
                return;
            }
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if let Some(unit) =
                        find_unit_for_step_hidden_order_cmp::<F::VirtualAddress>(condition)
                    {
                        if let Some(unresolved) = ctrl.unresolve(unit) {
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
    let mut cfg = analysis.finish();

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
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
) -> E::VirtualAddress {
    struct Analyzer<'f, F: ExecutionState<'f>> {
        result: F::VirtualAddress,
    }

    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation<'f>) {
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

pub(crate) fn step_order<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_init_arbiter: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let funcs = functions.functions();
    let ctx = analysis.ctx;

    let init_arbiter_callers = functions.find_callers(analysis, order_init_arbiter);
    let mut result = None;
    for caller in init_arbiter_callers {
        let val = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = IsStepOrder::<E> {
                ok: false,
                call_found: false,
                caller,
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

struct IsStepOrder<'e, E: ExecutionState<'e>> {
    ok: bool,
    call_found: bool,
    caller: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for IsStepOrder<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(_) => {
                if ctrl.address() == self.caller {
                    self.call_found = true;
                }
            }
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let ctx = ctrl.ctx();
                // Check for this.order comparision against const
                self.ok = condition.if_arithmetic_gt()
                    .or_else(|| condition.if_arithmetic_eq())
                    .and_either_other(Operand::if_constant)
                    .and_then(|x| {
                        x.if_mem8()?
                            .if_arithmetic_add_const(
                                struct_layouts::unit_order::<E::VirtualAddress>()
                            )
                            .filter(|&x| x == ctx.register(1))
                    })
                    .is_some();
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

fn find_unit_for_step_hidden_order_cmp<'e, Va: VirtualAddress>(
    condition: Operand<'e>,
) -> Option<Operand<'e>> {
    // mem8[x + 4d] > b0
    condition.if_arithmetic_gt()
        .filter(|x| x.1.if_constant() == Some(0xb0))
        .and_then(|x| {
            x.0.if_mem8()?
                .if_arithmetic_add_const(struct_layouts::unit_order::<Va>())
        })
}

pub(crate) fn step_order_hidden<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_hidden_frame: E::VirtualAddress,
) -> Vec<StepOrderHiddenHook<'e, E::VirtualAddress>> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        entry: E::VirtualAddress,
        result: Option<E::VirtualAddress>,
        inlining: bool,
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if find_unit_for_step_hidden_order_cmp::<E::VirtualAddress>(condition)
                        .is_some()
                    {
                        self.result = Some(self.entry);
                        ctrl.end_analysis();
                    } else if self.inlining {
                        // Should be first jump if inlining
                        ctrl.end_analysis();
                    }
                }
                Operation::Call(dest) => {
                    if !self.inlining {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inlining = true;
                            let old_entry = self.entry;
                            self.entry = dest;
                            ctrl.analyze_with_current_state(self, dest);
                            self.entry = old_entry;
                            self.inlining = false;
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, step_hidden_frame);
    let mut analyzer = Analyzer::<E> {
        entry: step_hidden_frame,
        result: None,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    let mut result = Vec::with_capacity(1);
    if let Some(entry) = analyzer.result {
        if let Some(info) = step_order_hook_info(actx, entry) {
            result.push(info);
        }
    }
    result
}

pub(crate) fn step_secondary_order<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_order: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Vec<SecondaryOrderHook<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let funcs = functions.functions();
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let callers = functions.find_callers(analysis, step_order);
    let mut callers = BumpVec::from_iter_in(callers, bump);
    callers.sort_unstable();
    callers.dedup();
    let mut checked_funcs = bumpvec_with_capacity(8, bump);
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
                let cfg = analysis.finish();
                let res = step_secondary_order_hook_info(
                    binary,
                    ctx,
                    cfg,
                    entry,
                    jump_addr,
                    unit,
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

struct StepSecondaryOrderAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: Option<SecondaryOrderHook<'e, E::VirtualAddress>>,
    pre_result: Option<(E::VirtualAddress, Operand<'e>)>,
    call_found: bool,
    inlining: bool,
    caller: E::VirtualAddress,
    checked_funcs: &'a mut BumpVec<'acx, E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    StepSecondaryOrderAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.pre_result.is_some() {
            return;
        }
        // step_secondary_order is supposed to begin with a check if the order
        // is 0x95 (Hallucinated unit)
        match *op {
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
                            let cfg = analysis.finish();
                            self.result = step_secondary_order_hook_info(
                                self.binary,
                                self.ctx,
                                cfg,
                                dest,
                                jump_addr,
                                unit,
                            );
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                        self.inlining = false;
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let unit = step_secondary_order_hallu_jump_check::<E::VirtualAddress>(condition);
                if let Some(unit) = unit.and_then(|u| ctrl.unresolve(u)) {
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

pub(crate) fn do_attack<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    attack_order: E::VirtualAddress,
) -> Option<DoAttack<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, attack_order);
    let mut analyzer = FindDoAttack {
        do_attack: None,
        do_attack_main: None,
        last_bullet_spawner: None,
        arg_cache,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    Some(DoAttack {
        do_attack: analyzer.do_attack?,
        do_attack_main: analyzer.do_attack_main?,
        last_bullet_spawner: analyzer.last_bullet_spawner?,
    })
}

struct FindDoAttack<'a, 'e, E: ExecutionState<'e>> {
    do_attack: Option<E::VirtualAddress>,
    do_attack_main: Option<E::VirtualAddress>,
    last_bullet_spawner: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDoAttack<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let step = match () {
            () if self.do_attack.is_none() => 0,
            () if self.last_bullet_spawner.is_none() => 1,
            () => 2,
        };
        match *op {
            Operation::Call(dest) => {
                if self.inlining {
                    ctrl.end_analysis();
                    return;
                }
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let ctx = ctrl.ctx();
                    let dest = E::VirtualAddress::from_u64(dest);
                    if step == 0 {
                        // Step 0: Check for do_attack(this, 0x5)
                        let ok = Some(())
                            .filter(|_| ctrl.resolve(ctx.register(1)) == ctx.register(1))
                            .and_then(|_| {
                                ctrl.resolve(self.arg_cache.on_thiscall_call(0)).if_constant()
                            })
                            .filter(|&c| c == 5)
                            .is_some();
                        if ok {
                            self.do_attack = Some(dest);
                            ctrl.analyze_with_current_state(self, dest);
                            if self.do_attack_main.is_some() {
                                ctrl.end_analysis();
                            } else {
                                self.do_attack = None;
                            }
                        }
                    } else if step == 1 {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                    } else if step == 2 {
                        // Step 2: Check for do_attack_main(this, 2, units_dat_air_weapon[x])
                        let ok = Some(())
                            .filter(|_| ctrl.resolve(ctx.register(1)) == ctx.register(1))
                            .and_then(|_| {
                                ctrl.resolve(self.arg_cache.on_thiscall_call(0)).if_constant()
                            })
                            .filter(|&c| c == 2)
                            .and_then(|_| {
                                ctrl.resolve(self.arg_cache.on_thiscall_call(1)).if_mem8()
                            })
                            .and_then(|addr| addr.if_arithmetic_add())
                            .and_then(|(_, r)| r.if_constant())
                            .is_some();
                        if ok {
                            self.do_attack_main = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None) if step == 1 => {
                // Step 1: Look for assignment of zero to global memory
                if mem.size == E::WORD_SIZE {
                    let dest = ctrl.resolve(mem.address);
                    let val = ctrl.resolve(val);
                    if val.if_constant() == Some(0) && dest.if_constant().is_some() {
                        let ctx = ctrl.ctx();
                        self.last_bullet_spawner =
                            Some(ctx.mem_variable_rc(mem.size, mem.address));
                    }
                }
            }
            Operation::Jump { .. } => {
                if self.inlining {
                    ctrl.end_analysis();
                    return;
                }
            }
            _ => (),
        }
    }
}
