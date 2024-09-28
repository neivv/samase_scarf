use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{MemAccessSize, Operand, Operation, DestOperand};

use bumpalo::collections::Vec as BumpVec;

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::call_tracker::CallTracker;
use crate::switch::simple_switch_branch;
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, ExecStateExt, OperandExt, OptionExt, bumpvec_with_capacity, single_result_assign,
};

#[derive(Clone, Debug)]
pub struct RegionRelated<'e, Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Operand<'e>>,
    pub change_ai_region_state: Option<Va>,
}

pub(crate) struct StepUnitMovement<Va: VirtualAddress> {
    pub make_path: Option<Va>,
}

pub(crate) struct MakePath<Va: VirtualAddress> {
    pub calculate_path: Option<Va>,
}

pub(crate) fn regions<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_hook: &crate::AiScriptHook<'e, E::VirtualAddress>,
) -> RegionRelated<'e, E::VirtualAddress> {
    let mut result = RegionRelated {
        get_region: None,
        ai_regions: None,
        change_ai_region_state: None,
    };

    // Find things through aiscript value_area
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let value_area = match simple_switch_branch(binary, aiscript_hook.switch_table, 0x2a) {
        Some(s) => s,
        None => return result,
    };
    // Set script->player to 0, x to 999 and y to 998
    let mut state = E::initial_state(ctx, binary);
    let player = ctx.mem_access32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_player(),
    );
    let x = ctx.mem_access32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_center(),
    );
    let y = x.with_offset(4);
    state.write_memory(&player, ctx.const_0());
    state.write_memory(&x, ctx.constant(999));
    state.write_memory(&y, ctx.constant(998));
    let mut analysis = FuncAnalysis::with_state(
        binary,
        ctx,
        value_area,
        state,
    );
    let mut analyzer = RegionsAnalyzer {
        result: &mut result,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct RegionsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut RegionRelated<'e, E::VirtualAddress>,
    inlining: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for RegionsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let handled = self.check_call(dest, ctrl);
                    if !handled && !self.inlining{
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                    }
                }
            }
            Operation::Jump { to, .. } => {
                if !self.inlining {
                    let to = ctrl.resolve(to);
                    if to.if_constant().is_none() {
                        // Avoid switch
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> RegionsAnalyzer<'a, 'e, E> {
    /// Return true if something was added to result
    fn check_call(
        &mut self,
        dest: E::VirtualAddress,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> bool {
        let ctx = ctrl.ctx();
        match ctrl.resolve_arg_u16(1).if_constant() {
            // GetRegion(x, y) call?
            Some(998) => {
                if ctrl.resolve_arg_u16(0).if_constant() == Some(999) {
                    self.result.get_region = Some(dest);
                    return true;
                }
            }
            // SetAiRegionState call?
            Some(5) => {
                let arg1 =  ctrl.resolve_arg(0);
                let ai_regions = arg1.if_arithmetic_add()
                    .and_either_other(|x| {
                        x.if_arithmetic_mul_const(E::struct_layouts().ai_region_size())
                            .filter(|x| x.contains_undefined())
                    })
                    .and_then(|x| ctrl.if_mem_word(x));
                if let Some(ai_regions_mem) = ai_regions {
                    self.result.ai_regions = Some(ai_regions_mem.address_op(ctx));
                    self.result.change_ai_region_state = Some(dest);
                }
            }
            _ => (),
        }
        false
    }
}

pub(crate) fn pathing<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    get_region: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, get_region);
    let mut analyzer = FindPathing::<E> {
        result: None,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindPathing<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindPathing<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                // Match against u16 arr pathing.map_tile_regions[]
                // So `(pathing + x * 2) + const_regions_offset`
                let addr = condition.iter_no_mem_addr()
                    .flat_map(|x| {
                        x.if_mem16_offset(E::struct_layouts().pathing_map_tile_regions())
                    })
                    .next();
                if let Some(addr) = addr {
                    let val = addr.if_arithmetic_add()
                        .and_either_other(|x| x.if_arithmetic_mul_const(2));
                    if single_result_assign(val, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_step_unit_movement<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_unit_movement: E::VirtualAddress,
) -> StepUnitMovement<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = StepUnitMovement {
        make_path: None,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, step_unit_movement);
    let mut analyzer = StepUnitMovementAnalyzer::<E> {
        result: &mut result,
        state: StepUnitMovementState::Switch,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct StepUnitMovementAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepUnitMovement<E::VirtualAddress>,
    inline_depth: u8,
    state: StepUnitMovementState,
}

enum StepUnitMovementState {
    /// Find switch on this.movement_state
    Switch,
    /// On branch 0x11, inline once to movement_state_11(this) if needed,
    /// and first call should be make_path(a1 = this, a2 = this.move_target)
    ///
    /// There can be extra calls with this = this and jumps if assertions are enabled.
    MakePath,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepUnitMovementAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepUnitMovementState::Switch => {
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        let exec = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x11) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = StepUnitMovementState::MakePath;
                            }
                        }
                    }
                }
            }
            StepUnitMovementState::MakePath => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg(0);
                        let a2 = ctrl.resolve_arg(1);
                        let ok = a1 == ctx.register(1) &&
                            a2.if_mem32_offset(E::struct_layouts().flingy_move_target()) ==
                                Some(ctx.register(1));
                        if ok {
                            self.result.make_path = Some(dest);
                        } else {
                            if ctrl.resolve_register(1) == ctx.register(1) &&
                                self.inline_depth == 0
                            {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                if self.result.make_path.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_make_path<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    make_path: E::VirtualAddress,
) -> MakePath<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let mut result = MakePath {
        calculate_path: None,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, make_path);
    let mut analyzer = MakePathAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: MakePathState::CollisionFlag,
        inline_depth: 0,
        call_tracker: CallTracker::with_capacity(actx, 0, 32),
        path_null_jump_seen: false,
        this_is_a1: bump.alloc_slice_copy(
            &[(DestOperand::register(1), actx.arg_cache.on_entry(0))]
        ),
        maybe_region_ids: bumpvec_with_capacity(0x20, bump),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct MakePathAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut MakePath<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    state: MakePathState,
    call_tracker: CallTracker<'acx, 'e, E>,
    path_null_jump_seen: bool,
    /// For call_tracker(this = a1) calls
    this_is_a1: &'acx [(DestOperand<'e>, Operand<'e>)],
    maybe_region_ids: BumpVec<'acx, Operand<'e>>,
}

enum MakePathState {
    /// Find jump on a1.flags & 0010_0000, follow neq
    CollisionFlag,
    /// Inline once to create_complex_path(a1 = a1, a2, _)
    /// find at least one (usually two) a1.path == 0 jump, follow zero branches
    /// After that inline to calculate_path_for_unit(a1 = path_ctx), with
    /// path_ctx.x0 == a1
    /// Then find path_ctx.start_region != path_ctx.end_region jump, follow neq branch
    PathIsNullJumps,
    /// Should be next call with func(a1 = path_ctx)
    CalculatePath,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    MakePathAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            MakePathState::CollisionFlag => {
                self.track_call_if_this_unit(ctrl, op);
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let condition =
                        self.call_tracker.resolve_calls_with_branch_limit(condition, 4);
                    let ok = condition.if_and_mask_eq_neq(0x10)
                        .filter(|x| {
                            x.0.if_mem8_offset(E::struct_layouts().unit_flags() + 2) ==
                                Some(self.arg_cache.on_entry(0))
                        })
                        .map(|x| x.1);
                    if let Some(eq) = ok {
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_neq_address(eq, to);
                        self.state = MakePathState::PathIsNullJumps;
                    }
                }
            }
            MakePathState::PathIsNullJumps => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let condition =
                        self.call_tracker.resolve_calls_with_branch_limit(condition, 4);
                    let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| {
                            ctrl.if_mem_word_offset(x.0, E::struct_layouts().unit_path()) ==
                                Some(self.arg_cache.on_entry(0))
                        })
                        .map(|x| x.1);
                    if let Some(eq) = ok {
                        self.path_null_jump_seen = true;
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_eq_address(eq, to);
                        return;
                    }
                }
                if !self.path_null_jump_seen {
                    if self.inline_depth == 0 {
                        if let Operation::Call(dest) = *op {
                            let inline = ctrl.resolve_arg(0) ==
                                self.arg_cache.on_entry(0) &&
                                ctrl.resolve_arg_u32(1) ==
                                    ctx.and_const(self.arg_cache.on_entry(1), 0xffff_ffff);
                            if inline {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.inline_depth = 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth = 0;
                                    if self.result.calculate_path.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else {
                    if self.inline_depth < 2 {
                        if let Operation::Call(dest) = *op {
                            let a1 = ctrl.resolve_arg(0);
                            let mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                            let is_path_ctx = ctrl.read_memory(&mem) ==
                                self.arg_cache.on_entry(0);
                            if is_path_ctx {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.inline_depth += 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                    if self.result.calculate_path.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                    if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                        // Skip past potential u16 stores from func returns to path_ctx so that
                        // it's simpler to check the jump condition
                        if mem.size == MemAccessSize::Mem16 {
                            let value = ctrl.resolve(value).unwrap_and_mask();
                            if value.is_undefined() || value.if_custom().is_some() {
                                ctrl.skip_operation();
                                if value.is_undefined() {
                                    self.maybe_region_ids.push(value);
                                }
                            }
                        }
                    } else if let Operation::Jump { condition, to } = *op {
                        let condition = ctrl.resolve(condition);
                        let ok = condition.if_arithmetic_eq_neq()
                            .and_then(|x| {
                                (|| {
                                    let a = x.0.if_mem16()?;
                                    let b = x.1.if_mem16()?;
                                    let (a_base, a_offset) = a.address();
                                    let (b_base, b_offset) = b.address();
                                    if a_base == b_base && (
                                        a_offset.wrapping_add(2) == b_offset ||
                                        b_offset.wrapping_add(2) == a_offset
                                    ) {
                                        Some(x.2)
                                    } else {
                                        None
                                    }
                                })().or_else(|| {
                                    if self.maybe_region_ids.is_empty() {
                                        return None;
                                    }
                                    // Allow one be undef due to codegen doing
                                    // ctx.start_region = func()
                                    // register = func()
                                    // ctx.end_region = register
                                    // if ctx.start_region == register
                                    let first = x.0.unwrap_and_mask();
                                    if first.is_undefined() &&
                                        self.maybe_region_ids.contains(&first)
                                    {
                                        x.1.if_mem16()?;
                                        return Some(x.2);
                                    }
                                    let first = x.1.unwrap_and_mask();
                                    if first.is_undefined() &&
                                        self.maybe_region_ids.contains(&first)
                                    {
                                        x.0.if_mem16()?;
                                        return Some(x.2);
                                    }
                                    None
                                })
                            });
                        if let Some(eq) = ok {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq, to);
                            self.state = MakePathState::CalculatePath;
                        }
                    }
                }
                self.track_call_if_this_unit(ctrl, op);
            }
            MakePathState::CalculatePath => {
                if let Operation::Call(dest) = *op {
                    let a1 = ctrl.resolve_arg(0);
                    let mem = ctrl.mem_access_word(a1, 0);
                    let is_path_ctx = ctrl.read_memory(&mem) == self.arg_cache.on_entry(0);
                    if is_path_ctx {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.result.calculate_path = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> MakePathAnalyzer<'a, 'acx, 'e, E> {
    fn track_call_if_this_unit(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        if let Operation::Call(dest) = *op {
            if ctrl.resolve_register(1) == self.arg_cache.on_entry(0) {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.call_tracker.add_call_with_state(ctrl, dest, self.this_is_a1);
                }
            }
        }
    }
}
