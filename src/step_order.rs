use bumpalo::collections::Vec as BumpVec;

use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, Operation};
use scarf::analysis::{self, FuncAnalysis, Cfg, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::OperandCtx;

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{entry_of_until, EntryOf, FunctionFinder};
use crate::analysis_state::{AnalysisState, StateEnum, StepOrderState};
use crate::call_tracker::CallTracker;
use crate::inline_hook::{EspOffsetRegs, InlineHookState, inline_hook_state};
use crate::struct_layouts::StructLayouts;
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, ExecStateExt, MemAccessExt, OperandExt, bumpvec_with_capacity,
    single_result_assign,
};

#[derive(Clone, Debug)]
pub enum StepOrderHiddenHook<'e, Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Operand<'e>,
        state: InlineHookState,
        /// How much the stack was offset by the function prologue.
        /// Required for keeping 64bit unwind info valid-ish.
        /// May not necessarily be valid on 32bit.
        whole_stack_size: u16,
    },
    Separate(Va),
}

#[derive(Clone, Debug)]
pub enum SecondaryOrderHook<'e, Va: VirtualAddress> {
    Inlined {
        entry: Va,
        exit: Va,
        // Unresolved at entry
        unit: Operand<'e>,
        state: InlineHookState,
        /// How much the stack was offset by the function prologue.
        /// Required for keeping 64bit unwind info valid-ish.
        /// May not necessarily be valid on 32bit.
        whole_stack_size: u16,
    },
    Separate(Va),
}

#[derive(Clone, Copy)]
pub struct DoAttack<'e, Va: VirtualAddress> {
    pub ai_try_return_home: Option<Va>,
    pub update_attack_target: Option<Va>,
    pub do_attack: Option<Va>,
    pub do_attack_main: Option<Va>,
    pub last_bullet_spawner: Option<Operand<'e>>,
}

pub(crate) struct StepOrder<Va: VirtualAddress> {
    pub ai_focus_disabled: Option<Va>,
    pub ai_focus_air: Option<Va>,
}

pub(crate) struct OrderTrain<Va: VirtualAddress> {
    pub step_train: Option<Va>,
    pub add_ai_to_trained_unit: Option<Va>,
    pub cancel_queued_unit: Option<Va>,
    pub refresh_ui: Option<Va>,
}

pub(crate) struct OrderMatrix<Va: VirtualAddress> {
    pub get_sight_range: Option<Va>,
}

pub(crate) struct OrderPlayerGuard<Va: VirtualAddress> {
    pub get_target_acquisition_range: Option<Va>,
    pub pick_auto_target: Option<Va>,
    pub attack_unit: Option<Va>,
}

pub(crate) struct OrderArbiterCloak<Va: VirtualAddress> {
    pub get_attack_range: Option<Va>,
    pub find_unit_borders_rect: Option<Va>,
}

pub(crate) struct OrderTower<Va: VirtualAddress> {
    pub pick_random_target: Option<Va>,
}

pub(crate) struct OrderInfest<Va: VirtualAddress> {
    pub can_be_infested: Option<Va>,
    pub detach_addon: Option<Va>,
    pub can_rally: Option<Va>,
}

pub(crate) struct OrderZergBuildSelf<Va: VirtualAddress> {
    pub unit_set_hp: Option<Va>,
    pub transform_unit: Option<Va>,
    pub stop_creep_disappearing_at_building: Option<Va>,
    pub place_creep_rect: Option<Va>,
}

pub(crate) struct OrderNukeLaunch<Va: VirtualAddress> {
    pub show_unit: Option<Va>,
    pub hide_unit: Option<Va>,
    pub move_unit: Option<Va>,
    pub stop_moving: Option<Va>,
}

// Checks for comparing secondary_order to 0x95 (Hallucination)
// Returns the unit operand
fn step_secondary_order_hallu_jump_check<'e>(
    struct_layouts: StructLayouts,
    condition: Operand<'e>,
) -> Option<Operand<'e>> {
    let hallucinated_id_found = condition.iter_no_mem_addr().any(|x| {
        x.if_constant().map(|x| x == 0x95).unwrap_or(false)
    });
    if !hallucinated_id_found {
        return None;
    }
    condition.iter_no_mem_addr()
        .filter_map(|x| x.if_mem8_offset(struct_layouts.unit_secondary_order()))
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
    stack_pointer: Operand<'e>,
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
    ) -> Option<(F::VirtualAddress, Operand<'e>, EspOffsetRegs)> {
        struct Analyzer<'e, G: ExecutionState<'e>> {
            result: Option<(G::VirtualAddress, Operand<'e>, EspOffsetRegs)>,
            unit: Operand<'e>,
        }
        impl<'g, G: ExecutionState<'g>> scarf::Analyzer<'g> for Analyzer<'g, G> {
            type State = analysis::DefaultState;
            type Exec = G;
            fn operation(&mut self, ctrl: &mut Control<'g, '_, '_, Self>, op: &Operation<'g>) {
                let ctx = ctrl.ctx();
                match *op {
                    Operation::Move(_, val) => {
                        let val = ctrl.resolve(val);
                        if let Some(result) = self.check(val, ctrl) {
                            self.result = Some((ctrl.address(), result.0, result.1));
                        }
                    }
                    Operation::SetFlags(ref arith) => {
                        let op = ctx.eq(arith.left, arith.right);
                        let val = ctrl.resolve(op);
                        if let Some(result) = self.check(val, ctrl) {
                            self.result = Some((ctrl.address(), result.0, result.1));
                        }
                    }
                    _ => (),
                }
            }
        }
        impl<'e, G: ExecutionState<'e>> Analyzer<'e, G> {
            /// Ends analysis if this is a secondary order read, even if the value
            /// could not be unresolved.
            fn check(
                &mut self,
                val: Operand<'e>,
                ctrl: &mut Control<'e, '_, '_, Self>,
            ) -> Option<(Operand<'e>, EspOffsetRegs)> {
                if self.is_secondary_order_read(val) {
                    ctrl.end_analysis();
                    let ctx = ctrl.ctx();
                    let exec_state = ctrl.exec_state();
                    let regs = EspOffsetRegs::from_entry_state(exec_state, ctx)?;
                    let unres = crate::unresolve::unresolve(ctx, exec_state, self.unit)?;
                    Some((unres, regs))
                } else {
                    None
                }
            }

            fn is_secondary_order_read(&mut self, val: Operand<'e>) -> bool {
                let result = val.if_mem8_offset(G::struct_layouts().unit_secondary_order());
                if result == Some(self.unit) {
                    return true;
                }
                let result = val.if_arithmetic_eq_neq()
                    .filter(|x| x.1.if_constant() == Some(0x95))
                    .and_then(|x| {
                        x.0.if_mem8_offset(G::struct_layouts().unit_secondary_order())
                    });
                result == Some(self.unit)
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
    let jump_rva = scarf::Rva(binary.rva_32(jump_addr));
    let node = cfg.nodes()
        .find(|n| n.address < jump_rva && n.node.end_address >= jump_rva)?;
    let addr = binary.base() + node.address.0;
    if addr == func_entry {
        // Can't hook it inline since a separate func tail calls the orders.
        Some(SecondaryOrderHook::Separate(addr))
    } else {
        let resolved = resolve_at_addr::<E>(binary, ctx, addr, unit, jump_addr)?;
        let whole_stack_size = stack_pointer
            .if_sub_with_const()
            .filter(|x| x.0 == ctx.register(4))
            .and_then(|x| u16::try_from(x.1).ok())
            .unwrap_or(0);
        if E::VirtualAddress::SIZE == 8 && whole_stack_size & 0xf != 8 {
            return None;
        }

        let (entry, unit_at_hook, esp_offsets) =
            find_secondary_order_access::<E>(binary, ctx, addr, resolved)?;
        let end = cfg.immediate_postdominator(node.index)?;
        let end_address = binary.base() + end.address.0;
        let mut state = inline_hook_state::<E>(binary, ctx, entry, end_address, esp_offsets)?;
        if let Some(reg) = unit_at_hook.if_register() {
            state.remove_entry_register(reg);
        }

        Some(SecondaryOrderHook::Inlined {
            entry,
            exit: end_address,
            unit: unit_at_hook,
            state,
            whole_stack_size,
        })
    }
}

pub(crate) fn find_order_function<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_order: E::VirtualAddress,
    order: u8,
) -> Option<E::VirtualAddress> {
    // Just take the last call when [ecx+4d] has been set to correct order.
    // Also guess long jumps as tail calls
    let this = analysis.ctx.register(1);
    let offset = E::struct_layouts().unit_order();
    find_order_function_any(analysis, step_order, this, offset, order)
}

pub(crate) fn find_order_function_secondary<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_secondary_order: &SecondaryOrderHook<'e, E::VirtualAddress>,
    order: u8,
) -> Option<E::VirtualAddress> {
    let (entry, this) = match *step_secondary_order {
        SecondaryOrderHook::Inlined { entry, unit, .. } => (entry, unit),
        SecondaryOrderHook::Separate(entry) => (entry, analysis.ctx.register(1)),
    };
    let offset = E::struct_layouts().unit_secondary_order();
    find_order_function_any(analysis, entry, this, offset, order)
}

pub(crate) fn find_order_function_hidden<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_order_hidden: &StepOrderHiddenHook<'e, E::VirtualAddress>,
    order: u8,
) -> Option<E::VirtualAddress> {
    let (entry, this) = match *step_order_hidden {
        StepOrderHiddenHook::Inlined { entry, unit, .. } => (entry, unit),
        StepOrderHiddenHook::Separate(entry) => (entry, analysis.ctx.register(1)),
    };
    let offset = E::struct_layouts().unit_order();
    find_order_function_any(analysis, entry, this, offset, order)
}

fn find_order_function_any<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    entry: E::VirtualAddress,
    this: Operand<'e>,
    order_offset: u64,
    order: u8,
) -> Option<E::VirtualAddress> {
    let mut analyzer = FindOrderFunc {
        result: None,
        start: entry,
        phantom: Default::default(),
        order,
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;

    let mut state = E::initial_state(ctx, binary);
    let dest = ctx.mem_access8(this, order_offset);
    state.write_memory(&dest, ctx.constant(order as u64));
    let user_state =
        AnalysisState::new(bump, StateEnum::StepOrder(StepOrderState::NotSwitchJumped));
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        entry,
        state,
        user_state,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindOrderFunc<'acx, 'f, F: ExecutionState<'f>> {
    result: Option<F::VirtualAddress>,
    start: F::VirtualAddress,
    phantom: std::marker::PhantomData<&'acx ()>,
    order: u8,
}

impl<'acx, 'e: 'acx, F: ExecutionState<'e>> scarf::Analyzer<'e> for FindOrderFunc<'acx, 'e, F> {
    type State = AnalysisState<'acx, 'e>;
    type Exec = F;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition: condition_unresolved, to } => {
                let ctx = ctrl.ctx();
                let condition = ctrl.resolve(condition_unresolved);
                if let Some(c) = condition.if_constant() {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        let state = *ctrl.user_state().get::<StepOrderState>();
                        if state == StepOrderState::HasSwitchJumped && c == 1 {
                            let seems_tail_call = (dest < self.start) ||
                                (
                                    dest > ctrl.address() + 0x400 &&
                                    dest > self.start + 0x800
                                );

                            if seems_tail_call {
                                let ecx = ctx.register(1);
                                let esp = ctx.register(4);
                                // Tail call needs to have this == orig this
                                if ctrl.resolve(ecx) == ecx && ctrl.resolve(esp) == esp {
                                    self.result = Some(dest);
                                    ctrl.end_analysis();
                                }
                            }
                        } else {
                            // Assume "switch jump" if the condition is always true,
                            // as the small 4-case switch at start isn't necessarily
                            // a switch table but just chained comparisions.
                            // Also assume it be switch jump if condition is false
                            // but order is 0x95 (secondary order hallucination)
                            if (condition_unresolved != ctx.const_1() && c == 1) ||
                                self.order == 0x95
                            {
                                ctrl.user_state().set(StepOrderState::HasSwitchJumped);
                                return;
                            }
                        }
                    }
                } else {
                    // If a func return value was used for jump
                    // (unit_is_disabled), then it is not the result.
                    if let Some(result) = self.result {
                        if let Some(func_return) = condition.if_arithmetic_eq_neq()
                            .and_then(|x| Operand::and_masked(x.0).0.if_custom())
                        {
                            if func_return == result.as_u64() as u32 {
                                self.result = None;
                            }
                        }
                    }
                }
                let state = if to.if_constant().is_none() {
                    StepOrderState::HasSwitchJumped
                } else {
                    StepOrderState::NotSwitchJumped
                };
                ctrl.user_state().set(state);
            }
            Operation::Call(dest) => {
                let state = *ctrl.user_state().get::<StepOrderState>();
                ctrl.skip_call_preserve_esp();
                if state == StepOrderState::HasSwitchJumped {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.result = Some(dest);
                        let ctx = ctrl.ctx();
                        let state = ctrl.exec_state();
                        state.set_register(0, ctx.custom(dest.as_u64() as u32));
                    }
                }
            }
            _ => (),
        }
    }
}

fn step_order_hook_info<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    func_entry: E::VirtualAddress,
) -> Option<StepOrderHiddenHook<'e, E::VirtualAddress>> {
    /// Finds `cmp order, 0xb0` jump that is the first thing done in step_order_hidden,
    /// `addr` being the function that step_order_hidden has been inlined to.
    struct Analyzer<'e, F: ExecutionState<'e>> {
        // Jump addr, unit unresolved, stack resolved
        result: Option<(F::VirtualAddress, Operand<'e>, Operand<'e>, EspOffsetRegs)>,
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
                        find_unit_for_step_hidden_order_cmp(F::struct_layouts(), condition)
                    {
                        let ctx = ctrl.ctx();
                        let exec_state = ctrl.exec_state();
                        let unres = crate::unresolve::unresolve(ctx, exec_state, unit);
                        if let Some(unres) = unres {
                            let regs = EspOffsetRegs::from_entry_state(exec_state, ctx);
                            if let Some(esp_offsets) = regs {
                                let rsp = ctrl.resolve_register(4);
                                self.result = Some((ctrl.address(), unres, rsp, esp_offsets));
                            }
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

    let (jump_addr, unit_at_hook, stack_pointer, esp_offsets) = analyzer.result?;
    cfg.calculate_node_indices();
    let jump_rva = scarf::Rva(binary.rva_32(jump_addr));
    let node = cfg.nodes()
        .find(|n| n.address < jump_rva && n.node.end_address >= jump_rva)?;
    let addr = binary.base() + node.address.0;
    if addr == func_entry {
        Some(StepOrderHiddenHook::Separate(addr))
    } else {
        let end = cfg.immediate_postdominator(node.index)?;
        let end_address = binary.base() + end.address.0;
        let entry = skip_past_calls::<E>(addr, ctx, binary);
        let mut state = inline_hook_state::<E>(binary, ctx, entry, end_address, esp_offsets)?;
        if let Some(reg) = unit_at_hook.if_register() {
            state.remove_entry_register(reg);
        }

        let whole_stack_size = stack_pointer
            .if_sub_with_const()
            .filter(|x| x.0 == ctx.register(4))
            .and_then(|x| u16::try_from(x.1).ok())
            .unwrap_or(0);
        if E::VirtualAddress::SIZE == 8 && whole_stack_size & 0xf != 8 {
            return None;
        }

        Some(StepOrderHiddenHook::Inlined {
            entry,
            exit: end_address,
            unit: unit_at_hook,
            state,
            whole_stack_size,
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
                    .filter(|x| x.1.if_constant().is_some())
                    .filter(|x| {
                        x.0.if_mem8_offset(E::struct_layouts().unit_order()) ==
                            Some(ctx.register(1))
                    })
                    .is_some();
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

fn find_unit_for_step_hidden_order_cmp<'e>(
    struct_layouts: StructLayouts,
    condition: Operand<'e>,
) -> Option<Operand<'e>> {
    // mem8[x + 4d] > b0
    condition.if_arithmetic_gt()
        .filter(|x| x.1.if_constant() == Some(0xb0))
        .and_then(|x| {
            x.0.if_mem8_offset(struct_layouts.unit_order())
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
                    if find_unit_for_step_hidden_order_cmp(E::struct_layouts(), condition)
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
            if let Some((jump_addr, unit, stack_pointer)) = analyzer.pre_result {
                let cfg = analysis.finish();
                let res = step_secondary_order_hook_info(
                    binary,
                    ctx,
                    cfg,
                    entry,
                    jump_addr,
                    unit,
                    stack_pointer,
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
    pre_result: Option<(E::VirtualAddress, Operand<'e>, Operand<'e>)>,
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
                        if let Some((jump_addr, unit, stack_pointer)) = self.pre_result.take() {
                            let cfg = analysis.finish();
                            self.result = step_secondary_order_hook_info(
                                self.binary,
                                self.ctx,
                                cfg,
                                dest,
                                jump_addr,
                                unit,
                                stack_pointer,
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
                let unit = step_secondary_order_hallu_jump_check(E::struct_layouts(), condition);
                if let Some(unit) = unit.and_then(|u| ctrl.unresolve(u)) {
                    let rsp = ctrl.resolve_register(4);
                    self.pre_result = Some((ctrl.address(), unit, rsp));
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
) -> DoAttack<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, attack_order);
    let mut analyzer = FindDoAttack::<E> {
        ai_try_return_home: None,
        update_attack_target: None,
        do_attack: None,
        do_attack_main: None,
        last_bullet_spawner: None,
        inlining: false,
        entry_esp: ctx.register(4),
        state: DoAttackState::AiTryReturnHome,
    };
    analysis.analyze(&mut analyzer);
    DoAttack {
        ai_try_return_home: analyzer.ai_try_return_home,
        update_attack_target: analyzer.update_attack_target,
        do_attack: analyzer.do_attack,
        do_attack_main: analyzer.do_attack_main,
        last_bullet_spawner: analyzer.last_bullet_spawner,
    }
}

struct FindDoAttack<'e, E: ExecutionState<'e>> {
    ai_try_return_home: Option<E::VirtualAddress>,
    update_attack_target: Option<E::VirtualAddress>,
    do_attack: Option<E::VirtualAddress>,
    do_attack_main: Option<E::VirtualAddress>,
    last_bullet_spawner: Option<Operand<'e>>,
    inlining: bool,
    entry_esp: Operand<'e>,
    state: DoAttackState,
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum DoAttackState {
    // ai_try_return_home(arg1 = this, arg2 = 0)
    AiTryReturnHome,
    // update_attack_target(this = this), right after ai_try_return_home
    // Verify by the function starting with flags & 0x0800_0000 check
    UpdateAttackTarget,
    VerifyUpdateAttackTarget,
    // do_attack(this = this, arg1 = 5)
    DoAttack,
    LastBulletSpawner,
    DoAttackMain,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDoAttack<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let state = self.state;
        match state {
            DoAttackState::AiTryReturnHome => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
                        let ok = arg1 == ctx.register(1) &&
                            ctx.and_const(arg2, 0xff) == ctx.const_0();
                        if ok {
                            self.ai_try_return_home = Some(dest);
                            self.state = DoAttackState::UpdateAttackTarget;
                            ctrl.clear_all_branches();
                        }
                    }
                }
            }
            DoAttackState::UpdateAttackTarget => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        if this == ctx.register(1) {
                            self.state = DoAttackState::VerifyUpdateAttackTarget;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.update_attack_target.is_some() {
                                self.update_attack_target = Some(dest);
                                self.state = DoAttackState::DoAttack;
                            } else {
                                self.state = DoAttackState::UpdateAttackTarget;
                            }
                        }
                    }
                }
            }
            DoAttackState::VerifyUpdateAttackTarget => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|x| {
                            x.0.if_arithmetic_and_const(0x8)?
                                .if_mem8_offset(E::struct_layouts().unit_flags() + 3)
                        }) == Some(ctx.register(1));
                    if ok {
                        self.update_attack_target = Some(E::VirtualAddress::from_u64(0));
                    }
                    ctrl.end_analysis();
                }
            }
            DoAttackState::DoAttack | DoAttackState::LastBulletSpawner |
                DoAttackState::DoAttackMain =>
            {
                match *op {
                    Operation::Call(dest) => {
                        if self.inlining {
                            ctrl.end_analysis();
                            return;
                        }
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            if state == DoAttackState::DoAttack {
                                // Check for do_attack(this, 0x5)
                                if self.is_do_attack_call(ctrl) {
                                    self.do_attack = Some(dest);
                                    self.state = DoAttackState::LastBulletSpawner;
                                    ctrl.analyze_with_current_state(self, dest);
                                    if self.do_attack_main.is_some() {
                                        ctrl.end_analysis();
                                    } else {
                                        self.do_attack = None;
                                    }
                                }
                            } else if state == DoAttackState::LastBulletSpawner {
                                self.inlining = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inlining = false;
                            } else if state == DoAttackState::DoAttackMain {
                                // Step 2: Check for do_attack_main(this, 2, units_dat_air_weapon[x])
                                let ok = Some(())
                                    .filter(|_| ctrl.resolve_register(1) == ctx.register(1))
                                    .and_then(|_| ctrl.resolve_arg_thiscall(0).if_constant())
                                    .filter(|&c| c == 2)
                                    .and_then(|_| ctrl.resolve_arg_thiscall(1).if_mem8())
                                    .filter(|x| {
                                        let (base, offset) = x.address();
                                        base != ctx.const_0() && offset != 0
                                    })
                                    .is_some();
                                if ok {
                                    self.do_attack_main = Some(dest);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                    Operation::Move(DestOperand::Memory(ref mem), val)
                        if state == DoAttackState::LastBulletSpawner =>
                    {
                        // Step 1: Look for assignment of zero to global memory
                        if mem.size == E::WORD_SIZE {
                            let dest = ctrl.resolve_mem(mem);
                            let val = ctrl.resolve(val);
                            if val == ctx.const_0() && dest.is_global() {
                                let ctx = ctrl.ctx();
                                self.last_bullet_spawner = Some(ctx.memory(&dest));
                                self.state = DoAttackState::DoAttackMain;
                            }
                        }
                    }
                    Operation::Jump { condition, to } => {
                        if self.inlining {
                            ctrl.end_analysis();
                            return;
                        }
                        if state == DoAttackState::DoAttack {
                            if condition == ctx.const_1() {
                                // Step 0 check can also be a tail call
                                if ctrl.resolve_register(4) == self.entry_esp {
                                    if let Some(to) = ctrl.resolve_va(to) {
                                        if self.is_do_attack_call(ctrl) {
                                            self.do_attack = Some(to);
                                            self.state = DoAttackState::LastBulletSpawner;
                                            ctrl.analyze_with_current_state(self, to);
                                            if self.do_attack_main.is_some() {
                                                ctrl.end_analysis();
                                            } else {
                                                self.do_attack = None;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => (),
                }
            }
        }
    }
}

impl<'e, E: ExecutionState<'e>> FindDoAttack<'e, E> {
    fn is_do_attack_call(&self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        let ecx = ctrl.ctx().register(1);
        let this = ctrl.resolve_register(1);
        this == ecx && ctrl.resolve_arg_thiscall_u8(0).if_constant() == Some(5)
    }
}

/// Analysis for non-order-specific functions of step_order
/// (So ai focusing)
pub(crate) fn step_order_analysis<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_order: E::VirtualAddress,
) -> StepOrder<E::VirtualAddress> {
    let mut result = StepOrder {
        ai_focus_air: None,
        ai_focus_disabled: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = AnalyzeStepOrder::<E> {
        result: &mut result,
        state: AnalyzeStepOrderState::FocusDisabled,
        inline_depth: 0,
        inline_depth_at_interceptor: 0,
        inline_result: None,
        entry_esp: ctx.register(4),
    };
    let mut exec = E::initial_state(ctx, binary);
    // Assign order = ff (Don't go to any order func)
    // mael, lockdown, stasis timer = 0; flags = 0x8000 (Not disabled, dweb)
    let writes: &[(u16, u16, MemAccessSize)] = &[
        (E::struct_layouts().unit_order() as u16, 0xff, MemAccessSize::Mem8),
        (E::struct_layouts().unit_lockdown_timer() as u16, 0, MemAccessSize::Mem8),
        (E::struct_layouts().unit_stasis_timer() as u16, 0, MemAccessSize::Mem8),
        (E::struct_layouts().unit_maelstrom_timer() as u16, 0, MemAccessSize::Mem8),
        (E::struct_layouts().unit_acid_spore_count() as u16, 0, MemAccessSize::Mem8),
        (E::struct_layouts().unit_flags() as u16, 0x8000, MemAccessSize::Mem32),
    ];
    let ecx = ctx.register(1);
    for &(offset, value, size) in writes {
        let mem = ctx.mem_access(ecx, offset.into(), size);
        exec.write_memory(&mem, ctx.constant(value.into()));
    }
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, step_order, exec, Default::default());
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeStepOrder<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepOrder<E::VirtualAddress>,
    state: AnalyzeStepOrderState,
    inline_depth: u8,
    inline_depth_at_interceptor: u8,
    inline_result: Option<Operand<'e>>,
    entry_esp: Operand<'e>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AnalyzeStepOrderState {
    /// Inline calls, find call where first check is for unit.order_timer
    FocusDisabled,
    /// Inline to depth 2, find unit_id == 49 check
    FindInterceptorCheck,
    /// Find call of ai_focus_air(this.unit_specific_union.interceptor.parent)
    FocusAir,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeStepOrder<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if let Operation::Jump { condition, .. } = *op {
            if condition == ctx.const_1() && ctrl.resolve_register(4) == self.entry_esp {
                // Don't follow tail calls
                ctrl.end_branch();
                return;
            }
        }
        if let Operation::Return(..) = *op {
            let result = ctrl.resolve_register(0);
            if let Some(old) = self.inline_result {
                if old != result {
                    self.inline_result = Some(ctx.new_undef());
                }
            } else {
                self.inline_result = Some(result);
            }
        }
        let state = self.state;
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if state == AnalyzeStepOrderState::FocusAir {
                    let arg1 = ctrl.resolve_arg(0);
                    let unit_specific = E::struct_layouts().unit_specific();
                    let ok = ctrl.if_mem_word_offset(arg1, unit_specific)
                        .filter(|&x| x == ctx.register(1))
                        .is_some();
                    if ok {
                        self.result.ai_focus_air = Some(dest);
                        ctrl.end_analysis();
                        return;
                    }
                }
                // Inlining
                let inline_limit = match state {
                    AnalyzeStepOrderState::FocusDisabled => 1,
                    AnalyzeStepOrderState::FindInterceptorCheck |
                        AnalyzeStepOrderState::FocusAir => 2,
                };
                if self.inline_depth < inline_limit {
                    self.inline_depth += 1;
                    let old_esp = self.entry_esp;
                    self.entry_esp = ctrl.get_new_esp_for_call();
                    let old_inline_result = self.inline_result;
                    ctrl.analyze_with_current_state(self, dest);
                    let inline_result = self.inline_result;
                    self.entry_esp = old_esp;
                    self.inline_result = old_inline_result;
                    self.inline_depth -= 1;
                    match state {
                        AnalyzeStepOrderState::FocusDisabled => {
                            if let Some(result) = self.result.ai_focus_disabled {
                                if result.as_u64() == 0 {
                                    self.result.ai_focus_disabled = Some(dest);
                                }
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                        AnalyzeStepOrderState::FindInterceptorCheck => {
                            if self.state != state {
                                ctrl.end_analysis();
                            }
                        }
                        AnalyzeStepOrderState::FocusAir => {
                            if let Some(_) = self.result.ai_focus_air {
                                ctrl.end_analysis();
                            }
                        }
                    }
                    ctrl.do_call_with_result(inline_result.unwrap_or_else(|| ctx.new_undef()));
                    return;
                }
            }
        }
        match state {
            AnalyzeStepOrderState::FocusDisabled => {
                if self.inline_depth != 0 {
                    if let Operation::Jump { condition, .. } = *op {
                        let condition = ctrl.resolve(condition);
                        let order_timer = E::struct_layouts().unit_order_timer();
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| x.0.if_mem8_offset(order_timer))
                            .filter(|&x| x == ctx.register(1))
                            .is_some();
                        if ok {
                            self.result.ai_focus_disabled = Some(E::VirtualAddress::from_u64(0));
                            self.state = AnalyzeStepOrderState::FindInterceptorCheck;
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            AnalyzeStepOrderState::FindInterceptorCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let unit_id = E::struct_layouts().unit_id();
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(0x49))
                        .and_then(|x| {
                            x.0.if_mem16_offset(unit_id).filter(|&x| x == ctx.register(1))?;
                            Some(x.2)
                        });
                    if let Some(jump_if_eq) = ok {
                        let dest = match jump_if_eq {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_address(dest);
                        self.state = AnalyzeStepOrderState::FocusAir;
                        self.inline_depth_at_interceptor = self.inline_depth;
                    }
                }
            }
            AnalyzeStepOrderState::FocusAir => (),
        }
    }
}

pub(crate) fn analyze_order_train<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_train: E::VirtualAddress,
) -> OrderTrain<E::VirtualAddress> {
    let mut result = OrderTrain {
        step_train: None,
        add_ai_to_trained_unit: None,
        cancel_queued_unit: None,
        refresh_ui: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = AnalyzeOrderTrain::<E> {
        result: &mut result,
        state: OrderTrainState::StepTrain,
        cancel_queued_branch: None,
    };
    let mut exec = E::initial_state(ctx, binary);
    // Use secondary order state 2
    let mem = ctx.mem_access8(
        ctx.register(1),
        E::struct_layouts().unit_secondary_order_state(),
    );
    exec.write_memory(&mem, ctx.constant(2));
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, order_train, exec, Default::default());
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderTrain<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderTrain<E::VirtualAddress>,
    state: OrderTrainState,
    cancel_queued_branch: Option<(E::VirtualAddress, E)>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderTrainState {
    /// Find step_train(this = this.currently_building, _, 1).
    /// Returns bool that is branched on immediately.
    StepTrain,
    /// After step_train, branch ret != 0, calls
    /// add_ai_to_trained_unit(a1 = this, a2 = this.currently_building)
    AddAiToTrainedUnit,
    /// step_train ret == 0 branch calls immediately cancel_queued_unit(this = this, 0),
    /// followed by refresh_ui() and nothing else.
    CancelQueuedUnit,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeOrderTrain<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderTrainState::StepTrain => {
                if self.result.step_train.is_none() {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let ecx = ctx.register(1);
                            let this = ctrl.resolve(ecx);
                            let arg2 = ctrl.resolve_arg_thiscall(1);
                            let currently_building = E::struct_layouts().unit_currently_building();
                            let ok = ctrl.if_mem_word_offset(this, currently_building) ==
                                    Some(ecx) &&
                                ctx.and_const(arg2, 0xff) == ctx.const_1();
                            if ok {
                                self.result.step_train = Some(dest);
                                ctrl.do_call_with_result(ctx.custom(0));
                            } else {
                                ctrl.skip_call_preserve_esp();
                            }
                        }
                    }
                } else {
                    if let Operation::Jump { condition, to } = *op {
                        if let Some(to) = ctrl.resolve_va(to) {
                            let condition = ctrl.resolve(condition);
                            if let Some(jump_if_zero) = condition.if_arithmetic_eq_neq_zero(ctx)
                                .filter(|x| Operand::and_masked(x.0).0.if_custom() == Some(0))
                                .map(|x| x.1)
                            {
                                let no_jump = ctrl.current_instruction_end();
                                let (zero_branch, nonzero_branch) = match jump_if_zero {
                                    true => (to, no_jump),
                                    false => (no_jump, to),
                                };
                                let state = ctrl.exec_state();
                                self.cancel_queued_branch = Some((zero_branch, state.clone()));
                                self.state = OrderTrainState::AddAiToTrainedUnit;
                                ctrl.continue_at_address(nonzero_branch);
                            } else {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            OrderTrainState::AddAiToTrainedUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
                        let ecx = ctx.register(1);
                        let currently_building = E::struct_layouts().unit_currently_building();
                        let ok = arg1 == ecx &&
                            ctrl.if_mem_word_offset(arg2, currently_building) == Some(ecx);
                        if ok {
                            self.result.add_ai_to_trained_unit = Some(dest);
                            ctrl.clear_unchecked_branches();
                            ctrl.end_branch();
                            if let Some((addr, state)) = self.cancel_queued_branch.take() {
                                ctrl.add_branch_with_state(addr, state, Default::default());
                                self.state = OrderTrainState::CancelQueuedUnit;
                            }
                        }
                    }
                }
            }
            OrderTrainState::CancelQueuedUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.result.cancel_queued_unit.is_none() {
                            let this = ctrl.resolve_register(1);
                            let ok = this == ctx.register(1) &&
                                ctrl.resolve_arg_thiscall_u8(0) == ctx.const_0();
                            if ok {
                                self.result.cancel_queued_unit = Some(dest);
                            }
                        } else if self.result.refresh_ui.is_none() {
                            self.result.refresh_ui = Some(dest);
                        } else {
                            self.result.refresh_ui = None;
                            ctrl.end_analysis();
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), _) = *op {
                    if self.result.cancel_queued_unit.is_some() {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            // refresh_ui got inlined, cannot find it
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_matrix<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_matrix: E::VirtualAddress,
    units_dat: (E::VirtualAddress, u32),
) -> OrderMatrix<E::VirtualAddress> {
    let mut result = OrderMatrix {
        get_sight_range: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let units_dat_sight_range = match binary.read_address(units_dat.0 + units_dat.1 * 0x18) {
        Ok(o) => o,
        Err(_) => return result,
    };

    let mut analyzer = AnalyzeOrderMatrix::<E> {
        result: &mut result,
        state: OrderMatrixState::GetSightRange,
        units_dat_sight_range,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_matrix);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderMatrix<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderMatrix<E::VirtualAddress>,
    state: OrderMatrixState,
    units_dat_sight_range: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderMatrixState {
    /// Find get_sight_range(this = this.currently_building, 1).
    GetSightRange,
    /// get_sight_range should read units_dat_sight_range
    VerifyGetSightRange,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeOrderMatrix<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderMatrixState::GetSightRange => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        let ok = this == ctx.register(1) &&
                            ctrl.resolve_arg_thiscall_u8(0) == ctx.const_1();
                        if ok {
                            self.state = OrderMatrixState::VerifyGetSightRange;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.get_sight_range.is_some() {
                                self.result.get_sight_range = Some(dest);
                                ctrl.end_analysis();
                            } else {
                                self.state = OrderMatrixState::GetSightRange;
                            }
                        }
                    }
                }
            }
            OrderMatrixState::VerifyGetSightRange => {
                if let Operation::Move(_, value) = *op {
                    if let Some(mem) = value.if_mem8() {
                        let mem = ctrl.resolve_mem(mem);
                        let (_index, base) = mem.address();
                        if base == self.units_dat_sight_range.as_u64() {
                            self.result.get_sight_range = Some(E::VirtualAddress::from_u64(0));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_player_guard<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_player_guard: E::VirtualAddress,
) -> OrderPlayerGuard<E::VirtualAddress> {
    let mut result = OrderPlayerGuard {
        get_target_acquisition_range: None,
        pick_auto_target: None,
        attack_unit: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = AnalyzeOrderPlayerGuard::<E> {
        result: &mut result,
        state: OrderPlayerGuardState::GetTargetAcqRange,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x8),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_player_guard);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderPlayerGuard<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderPlayerGuard<E::VirtualAddress>,
    state: OrderPlayerGuardState,
    call_tracker: CallTracker<'acx, 'e, E>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderPlayerGuardState {
    /// Find get_target_acq_range(this = this)
    /// Assume unit.ai != 0 to skip past some code
    GetTargetAcqRange,
    /// get_target_acq_range should jump based on unit.order == 6b
    VerifyGetTargetAcqRange,
    /// attack_unit(a1 = this, a2 = pick_auto_target(), a3 = 1, a4 = 0)
    AttackUnit,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeOrderPlayerGuard<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderPlayerGuardState::GetTargetAcqRange => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ecx = ctx.register(1);
                        if ctrl.resolve(ecx) == ecx {
                            self.state = OrderPlayerGuardState::VerifyGetTargetAcqRange;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.get_target_acquisition_range.is_some() {
                                self.result.get_target_acquisition_range = Some(dest);
                                self.state = OrderPlayerGuardState::AttackUnit;
                            } else {
                                self.state = OrderPlayerGuardState::GetTargetAcqRange;
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    if let Some(to) = ctrl.resolve_va(to) {
                        let condition = ctrl.resolve(condition);
                        let jump_if_ai_zero = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| {
                                let ai = E::struct_layouts().unit_ai();
                                ctrl.if_mem_word_offset(x.0, ai)
                                    .filter(|&x| x == ctx.register(1))?;
                                Some(x.1)
                            });
                        if let Some(jump) = jump_if_ai_zero {
                            let nonzero = match jump {
                                true => ctrl.current_instruction_end(),
                                false => to,
                            };
                            ctrl.continue_at_address(nonzero);
                        }
                    }
                }
            }
            OrderPlayerGuardState::VerifyGetTargetAcqRange => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(0x6b))
                        .and_then(|x| x.0.if_mem8_offset(E::struct_layouts().unit_order()))
                        .filter(|&x| x == ctx.register(1))
                        .is_some();
                    if ok {
                        self.result.get_target_acquisition_range =
                            Some(E::VirtualAddress::from_u64(0));
                        ctrl.end_analysis();
                    }
                }
            }
            OrderPlayerGuardState::AttackUnit => {
                let dest = match *op {
                    Operation::Call(dest) => dest,
                    Operation::Jump { condition, to } if condition == ctx.const_1() &&
                        ctrl.resolve_register(4) == ctx.register(4) => to,
                    _ => return,
                };
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg2 = ctrl.resolve_arg(1);
                    let ok = ctrl.resolve_arg(0) == ctx.register(1) &&
                        arg2.if_custom().is_some() &&
                        ctrl.resolve_arg_u8(2) == ctx.const_1() &&
                        ctrl.resolve_arg_u8(3) == ctx.const_0();
                    if ok {
                        self.result.attack_unit = Some(dest);
                        self.result.pick_auto_target = arg2.if_custom()
                            .and_then(|c| self.call_tracker.custom_id_to_func(c));
                        ctrl.end_analysis();
                    } else {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_arbiter_cloak<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_arbiter_cloak: E::VirtualAddress,
    units_dat: (E::VirtualAddress, u32),
) -> OrderArbiterCloak<E::VirtualAddress> {
    let mut result = OrderArbiterCloak {
        get_attack_range: None,
        find_unit_borders_rect: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let units_dat_air_weapon = match binary.read_address(units_dat.0 + units_dat.1 * 0x13) {
        Ok(o) => o,
        Err(_) => return result,
    };

    let mut analyzer = AnalyzeOrderArbiterCloak::<E> {
        result: &mut result,
        state: OrderArbiterCloakState::GetAttackRange,
        units_dat_air_weapon,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_arbiter_cloak);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderArbiterCloak<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderArbiterCloak<E::VirtualAddress>,
    state: OrderArbiterCloakState,
    units_dat_air_weapon: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderArbiterCloakState {
    /// get_attack_range(this = this, a1 = units_dat_air_weapon[x])
    GetAttackRange,
    /// find_unit_borders_rect(&rect), where rect.left and rect.top are `x/y - attack_range`.
    UnitBorders,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeOrderArbiterCloak<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderArbiterCloakState::GetAttackRange => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ecx = ctx.register(1);
                        let this = ctrl.resolve_register(1);
                        let arg1 = ctrl.resolve_arg_thiscall(0);
                        let ok = this == ecx &&
                            arg1.if_mem8_offset(self.units_dat_air_weapon.as_u64()).is_some();
                        if ok {
                            self.state = OrderArbiterCloakState::UnitBorders;
                            self.result.get_attack_range = Some(dest);
                            ctrl.do_call_with_result(ctx.custom(0));
                            ctrl.clear_unchecked_branches();
                        }
                    }
                }
            }
            OrderArbiterCloakState::UnitBorders => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let mem = ctx.mem_access(arg1, 0, MemAccessSize::Mem16);
                        let left = ctrl.read_memory(&mem);
                        let top =
                            ctrl.read_memory(&mem.with_offset_size(2, MemAccessSize::Mem16));
                        let ok = left.if_arithmetic_and_const(0xffff)
                                .and_then(|x| x.if_arithmetic_sub())
                                .filter(|x| x.1.if_custom() == Some(0)).is_some() &&
                            top.if_arithmetic_and_const(0xffff)
                                .and_then(|x| x.if_arithmetic_sub())
                                .filter(|x| x.1.if_custom() == Some(0)).is_some();
                        if ok {
                            self.result.find_unit_borders_rect = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    // Assume that i16 subtraction won't be less than 0
                    // Makes sure that left/top rect fields aren't just undefined
                    // at call.
                    let jump_if_pos = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| x.0.if_arithmetic_and_const(0x8000).is_some())
                        .map(|x| x.1);
                    if let Some(jump) = jump_if_pos {
                        let dest = match jump {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.continue_at_address(dest);
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_tower<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_tower: E::VirtualAddress,
    get_target_acquisition_range: E::VirtualAddress,
) -> OrderTower<E::VirtualAddress> {
    let mut result = OrderTower {
        pick_random_target: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = AnalyzeOrderTower::<E> {
        result: &mut result,
        state: OrderTowerState::PickRandomTarget,
        order_timer_store_seen: false,
        get_target_acquisition_range,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_tower);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderTower<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderTower<E::VirtualAddress>,
    state: OrderTowerState,
    order_timer_store_seen: bool,
    get_target_acquisition_range: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderTowerState {
    /// First call after 0xf store to order_timer
    PickRandomTarget,
    /// pick_random_target should call get_target_acquisition_range
    VerifyPickRandomTarget,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeOrderTower<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderTowerState::PickRandomTarget => {
                if self.order_timer_store_seen {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let ecx = ctx.register(1);
                            let this = ctrl.resolve(ecx);
                            if this == ecx {
                                self.state = OrderTowerState::VerifyPickRandomTarget;
                                ctrl.analyze_with_current_state(self, dest);
                                if self.result.pick_random_target.is_some() {
                                    self.result.pick_random_target = Some(dest);
                                    ctrl.end_analysis();
                                } else {
                                    self.state = OrderTowerState::VerifyPickRandomTarget;
                                }
                            }
                        }
                    }
                } else {
                    if let Operation::Move(DestOperand::Memory(..), value) = *op {
                        if ctrl.resolve(value).if_constant() == Some(0xf) {
                            self.order_timer_store_seen = true;
                        }
                    }
                }
            }
            OrderTowerState::VerifyPickRandomTarget => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ecx = ctx.register(1);
                        let this = ctrl.resolve(ecx);
                        if this == ecx && dest == self.get_target_acquisition_range {
                            self.result.pick_random_target = Some(E::VirtualAddress::from_u64(0));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_infest<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_infest: E::VirtualAddress,
) -> OrderInfest<E::VirtualAddress> {
    let mut result = OrderInfest {
        can_be_infested: None,
        detach_addon: None,
        can_rally: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = AnalyzeOrderInfest::<E> {
        result: &mut result,
        state: OrderInfestState::CanBeInfested,
        inline_limit: 0,
        inline_depth: 0,
        verify_func: E::VirtualAddress::from_u64(0),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_infest);
    analysis.analyze(&mut analyzer);
    // Can get false positive since can_rally also checks command center unit id
    if result.can_rally.is_none() {
        result.can_be_infested = None;
    }
    result
}

struct AnalyzeOrderInfest<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderInfest<E::VirtualAddress>,
    state: OrderInfestState,
    inline_limit: u8,
    inline_depth: u8,
    verify_func: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderInfestState {
    /// Call with this = this, verify by inlining
    CanBeInfested,
    /// Should check unit_id == 0x6a
    VerifyCanBeInfested,
    /// Call with this = this, verify by inlining
    DetachAddon,
    /// Should write this.addon = 0
    VerifyDetachAddon,
    /// Call with this = this, verify by inlining
    CanRally,
    /// Should compare unit_id == 0x6f
    VerifyCanRally,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeOrderInfest<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let state = self.state;
        if self.inline_limit != 0 {
            if matches!(*op, Operation::Call(..) | Operation::Jump { .. }) {
                self.inline_limit -= 1;
                if self.inline_limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
            }
        }
        match state {
            OrderInfestState::CanBeInfested | OrderInfestState::DetachAddon |
                OrderInfestState::CanRally =>
            {
                if let Operation::Call(dest) = *op {
                    if ctrl.resolve_register(1) == ctx.register(1) {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let new_state = match state {
                                OrderInfestState::CanBeInfested =>
                                    OrderInfestState::VerifyCanBeInfested,
                                OrderInfestState::DetachAddon =>
                                    OrderInfestState::VerifyDetachAddon,
                                OrderInfestState::CanRally | _ => OrderInfestState::VerifyCanRally,
                            };
                            self.verify_func = dest;
                            self.state = new_state;
                            self.inline_depth = 1;
                            self.inline_limit = 9;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            self.inline_limit = 0;
                            if self.state == new_state {
                                self.state = state;
                            } else if self.result.can_rally.is_some() {
                                ctrl.end_analysis();
                            } else {
                                ctrl.clear_unchecked_branches();
                            }
                        }
                    }
                }
            }
            OrderInfestState::VerifyCanBeInfested | OrderInfestState::VerifyDetachAddon |
                OrderInfestState::VerifyCanRally =>
            {
                if self.inline_depth > 1 {
                    return;
                }
                // Inline for this.unit_id() in case
                if let Operation::Call(dest) = *op {
                    if ctrl.resolve_register(1) == ctx.register(1) {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let old_limit = self.inline_limit;
                            self.inline_depth += 1;
                            self.inline_limit = 1;
                            ctrl.inline(self, dest);
                            if self.inline_limit == 1 {
                                ctrl.skip_operation();
                            }
                            self.inline_depth -= 1;
                            self.inline_limit = old_limit;
                        }
                    }
                } else {
                    if state == OrderInfestState::VerifyDetachAddon {
                        if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                            if mem.size == E::WORD_SIZE {
                                let mem = ctrl.resolve_mem(mem);
                                let (base, offset) = mem.address();
                                let addon_offset = E::struct_layouts().unit_specific();
                                if base == ctx.register(1) && offset == addon_offset {
                                    if ctrl.resolve(value) == ctx.const_0() {
                                        self.result.detach_addon = Some(self.verify_func);
                                        self.state = OrderInfestState::CanRally;
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    } else {
                        // Check jump for unit_id == constant
                        if let Operation::Jump { condition, .. } = *op {
                            let condition = ctrl.resolve(condition);
                            let constant = match state {
                                OrderInfestState::VerifyCanBeInfested => 0x6a,
                                _ => 0x6f,
                            };
                            let mut ok = condition.if_arithmetic_eq_neq()
                                .filter(|x| x.1.if_constant() == Some(constant))
                                .and_then(|x| {
                                    x.0.if_mem16_offset(E::struct_layouts().unit_id())
                                }) == Some(ctx.register(1));
                            if !ok && state == OrderInfestState::VerifyCanRally {
                                // 64bit switch uses more likely bit test and not
                                // multiple comparisons
                                ok = condition.if_arithmetic_eq_const(0).unwrap_or(condition)
                                    .if_arithmetic_and_const(1)
                                    .and_then(|x| x.if_arithmetic_rsh())
                                    .filter(|x| x.0.if_constant() == Some(0x204300000f0001a1))
                                    .is_some();
                            }
                            if ok {
                                if state == OrderInfestState::VerifyCanBeInfested {
                                    self.result.can_be_infested = Some(self.verify_func);
                                    self.state = OrderInfestState::DetachAddon;
                                } else {
                                    self.result.can_rally = Some(self.verify_func);
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_zerg_build_self<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_zerg_build: E::VirtualAddress,
) -> OrderZergBuildSelf<E::VirtualAddress> {
    let mut result = OrderZergBuildSelf {
        unit_set_hp: None,
        transform_unit: None,
        stop_creep_disappearing_at_building: None,
        place_creep_rect: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = AnalyzeOrderZergBuildSelf::<E> {
        result: &mut result,
        state: ZergBuildSelfState::ClearCompletedFlag,
        func_candidate: E::VirtualAddress::from_u64(0),
        units_dat_flag_jump_seen: false,
        funcs_seen: 0,
        any_jumps_seen: false,
    };
    let mut exec = E::initial_state(ctx, binary);
    exec.write_memory(
        &ctx.mem_access(
            ctx.register(1),
            E::struct_layouts().unit_order_state(),
            MemAccessSize::Mem8,
        ),
        ctx.constant(6),
    );
    let mut analysis = FuncAnalysis::with_state(binary, ctx, order_zerg_build, exec);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderZergBuildSelf<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderZergBuildSelf<E::VirtualAddress>,
    state: ZergBuildSelfState,
    func_candidate: E::VirtualAddress,
    funcs_seen: u32,
    any_jumps_seen: bool,
    units_dat_flag_jump_seen: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum ZergBuildSelfState {
    /// Start with order_state = 6.
    /// Find write of this.flags & !0x1.
    /// Clear other branches after that.
    ClearCompletedFlag,
    /// Should be next call with this = this
    TransformUnit,
    /// Should be next call after that, followed by writing 0 to this.remaining_build_time
    SetUnitHp,
    /// stop_creep_disappearing_at_building(arg1 = this), followed by
    /// set_iscript_anim(arg1 = 0xf, 1)
    /// Note: there is also finish_unit(this = this) before stop_creep_disappearing_at_building
    StopCreepDisappearAtBuilding,
    /// place_building_creep_rect(unit_id, x, y) (sometimes inlined)
    /// -> place_creep_rect(x_tile, y_tile, w_tile, h_tile, skip_borders)
    ///
    /// Find jump with units_dat_flags[unit_id] & 8000_0000, follow nonzero branch,
    /// should be next function with arg5 = 1
    /// If there is only 1 function before return and no units_dat_flags[unit_id], inline there
    ///
    /// Somewhat unsure if always can be found, one call to place_creep_rect(arg5 = 0) is being
    /// inlined right next to arg5 = 1 call sometimes.
    PlaceCreepRect,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeOrderZergBuildSelf<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            ZergBuildSelfState::ClearCompletedFlag => {
                if let Operation::Move(DestOperand::Memory(ref dest_mem), value) = *op {
                    let value = ctrl.resolve(value);
                    let ok = value.if_and_with_const()
                        .filter(|x| x.1 & 0xff == 0xfe)
                        .and_then(|x| {
                            let mem = x.0.if_memory()?;
                            let dest_mem = ctrl.resolve_mem(dest_mem);
                            let flags_offset = E::struct_layouts().unit_flags();
                            (*mem == dest_mem && mem.address() == (ctx.register(1), flags_offset))
                                .then_some(())
                        })
                        .is_some();
                    if ok {
                        self.state = ZergBuildSelfState::TransformUnit;
                        ctrl.clear_unchecked_branches();
                    }
                }
            }
            ZergBuildSelfState::TransformUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        if this == ctx.register(1) {
                            self.result.transform_unit = Some(dest);
                            self.state = ZergBuildSelfState::SetUnitHp;
                        }
                    }
                }
            }
            ZergBuildSelfState::SetUnitHp => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        if this == ctx.register(1) {
                            self.func_candidate = dest;
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == MemAccessSize::Mem16 {
                        if ctrl.resolve(value) == ctx.const_0() {
                            let mem = ctrl.resolve_mem(&mem);
                            let build_time_offset =
                                E::struct_layouts().unit_remaining_build_time();
                            if mem.address() == (ctx.register(1), build_time_offset) {
                                if self.func_candidate.as_u64() != 0 {
                                    self.result.unit_set_hp = Some(self.func_candidate);
                                    self.func_candidate = E::VirtualAddress::from_u64(0);
                                    self.state = ZergBuildSelfState::StopCreepDisappearAtBuilding;
                                }
                            }
                        }
                    }
                }
            }
            ZergBuildSelfState::StopCreepDisappearAtBuilding => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.func_candidate.as_u64() != 0 {
                            let arg1 = ctrl.resolve_arg_thiscall_u8(0);
                            if arg1.if_constant() == Some(0xf) {
                                self.result.stop_creep_disappearing_at_building =
                                    Some(self.func_candidate);
                                self.state = ZergBuildSelfState::PlaceCreepRect;
                                ctrl.clear_unchecked_branches();
                                return;
                            }
                        }
                        let arg1 = ctrl.resolve_arg(0);
                        if arg1 == ctx.register(1) {
                            self.func_candidate = dest;
                        }
                    }
                }
            }
            ZergBuildSelfState::PlaceCreepRect => {
                if !self.units_dat_flag_jump_seen {
                    if let Operation::Jump { condition, to } = *op {
                        if condition != ctx.const_1() {
                            self.any_jumps_seen = true;
                        }
                        let condition = ctrl.resolve(condition);
                        // Check units_dat_flags[unit_id * 4] & 0x8000_0000
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| {
                                let mem = x.0.if_arithmetic_and_const(0x80)?
                                    .if_mem8()?;
                                mem.address().0.if_arithmetic_mul_const(4)?;
                                Some(x.1)
                            });
                        if let Some(eq_zero) = ok {
                            self.units_dat_flag_jump_seen = true;
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq_zero, to);
                        }
                    } else {
                        if !self.any_jumps_seen {
                            if let Operation::Call(dest) = *op {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.func_candidate = dest;
                                }
                                self.funcs_seen = self.funcs_seen.wrapping_add(1);
                            } else if let Operation::Return(..) = *op {
                                if self.funcs_seen == 1 || self.funcs_seen == 3 {
                                    // Inline to place_building_creep_rect
                                    // Analysis shouldn't depend on arguments, so just
                                    // creating empty exec state for that
                                    // Just place_building_creep_rect() call or
                                    // place_building_creep_rect(id, x(), y()) 3 calls
                                    self.any_jumps_seen = true;
                                    let binary = ctrl.binary();
                                    let mut analysis = FuncAnalysis::new(binary, ctx, self.func_candidate);
                                    analysis.analyze(self);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                } else {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let arg5 = ctrl.resolve_arg_u8(4);
                            if arg5 == ctx.const_1() {
                                self.result.place_creep_rect = Some(dest);
                            }
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_nuke_launch<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_nuke_launch: E::VirtualAddress,
) -> OrderNukeLaunch<E::VirtualAddress> {
    let mut result = OrderNukeLaunch {
        show_unit: None,
        hide_unit: None,
        move_unit: None,
        stop_moving: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = AnalyzeOrderNukeLaunch::<E> {
        result: &mut result,
        state: NukeLaunchState::OrderStateSwitch,
        last_call: E::VirtualAddress::from_u64(0),
        order_targets_read: 0,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_nuke_launch);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOrderNukeLaunch<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderNukeLaunch<E::VirtualAddress>,
    state: NukeLaunchState,
    last_call: E::VirtualAddress,
    order_targets_read: u8,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum NukeLaunchState {
    /// Find switch jump based on self.order_state
    OrderStateSwitch,
    /// On order_state == 2 branch
    /// Should be a call before setting this.related.related = this
    HideUnit,
    /// Should be a call after hide_unit but before setting this.order_state = 3
    StopMoving,
    /// On order state == 4 branch, find move_unit(this, this.order_target.x, this.order_target.y)
    /// Assume that it is the next call after both order_target.x and y are read.
    MoveUnit,
    /// Should be a call after move_unit but before setting this.order_state = 5
    ShowUnit,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeOrderNukeLaunch<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        ctrl.aliasing_memory_fix(op);
        let ctx = ctrl.ctx();
        match self.state {
            NukeLaunchState::OrderStateSwitch => {
                if let Operation::Call(..) = *op {
                    ctrl.check_stack_probe();
                } else if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() && to.if_constant().is_none() {
                        let to = ctrl.resolve(to);
                        let exec = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                            let binary = ctrl.binary();
                            let branches = [
                                (2u8, NukeLaunchState::HideUnit),
                                (4, NukeLaunchState::MoveUnit),
                            ];
                            for (n, state) in branches {
                                if let Some(branch) = switch.branch(binary, ctx, n as u32) {
                                    self.state = state;
                                    ctrl.analyze_with_current_state(self, branch);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            NukeLaunchState::HideUnit => {
                self.track_last_call_with_this(ctrl, op);
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    // Check [[this + C] + C] = this with C being unit.related offset
                    if mem.size == E::WORD_SIZE && ctrl.resolve(value) == ctx.register(1) {
                        let mem = ctrl.resolve_mem(mem);
                        let (base, offset) = mem.address();
                        if ctrl.if_mem_word_offset(base, offset) == Some(ctx.register(1)) {
                            self.result.hide_unit = Some(self.last_call);
                            self.state = NukeLaunchState::StopMoving;
                            ctrl.clear_unchecked_branches();
                        }
                    }
                }
            }
            NukeLaunchState::StopMoving => {
                if let Some(result) = self.check_call_before_order_state_set(ctrl, op, 3) {
                    self.result.stop_moving = Some(result);
                    ctrl.end_analysis();
                }
            }
            NukeLaunchState::MoveUnit => {
                if self.order_targets_read == 3 {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            let ok = this == ctx.register(1);
                            if ok {
                                self.result.move_unit = Some(dest);
                                self.state = NukeLaunchState::ShowUnit;
                                ctrl.clear_unchecked_branches();
                            }
                        }
                    }
                } else {
                    if let Operation::Move(_, value) = *op {
                        if let Some(mem) = value.unwrap_sext().if_mem16() {
                            let mem = ctrl.resolve_mem(mem);
                            let (base, offset) = mem.address();
                            if base == ctx.register(1) {
                                let order_target = E::struct_layouts().unit_order_target_pos();
                                if offset == order_target {
                                    self.order_targets_read |= 1;
                                } else if offset == order_target + 2{
                                    self.order_targets_read |= 2;
                                }
                            }
                        }
                    }
                }
            }
            NukeLaunchState::ShowUnit => {
                if let Some(result) = self.check_call_before_order_state_set(ctrl, op, 5) {
                    self.result.show_unit = Some(result);
                    ctrl.end_analysis();
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> AnalyzeOrderNukeLaunch<'a, 'e, E> {
    /// thiscall(this = this) to be exact.
    fn track_last_call_with_this(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        if let Operation::Call(dest) = *op {
            if ctrl.resolve_register(1) == ctrl.ctx().register(1) {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.last_call = dest;
                }
            }
        }
    }

    fn check_call_before_order_state_set(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
        state: u8,
    ) -> Option<E::VirtualAddress> {
        self.track_last_call_with_this(ctrl, op);
        if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
            if mem.size == MemAccessSize::Mem8 {
                if ctrl.resolve(value).if_constant() == Some(state as u64) {
                    // Could also check mem offset to be this.order_state,
                    // but going to be lazy and say that Mem8 constant is enough..
                    if self.last_call.as_u64() != 0 {
                        return Some(self.last_call);
                    }
                }
            }
        }
        None
    }
}
