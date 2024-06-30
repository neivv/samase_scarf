use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation, DestOperand};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::switch::simple_switch_branch;
use crate::switch::CompleteSwitch;
use crate::util::{ControlExt, ExecStateExt, OperandExt, OptionExt, single_result_assign};

#[derive(Clone, Debug)]
pub struct RegionRelated<'e, Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Operand<'e>>,
    pub change_ai_region_state: Option<Va>,
}

pub(crate) struct StepUnitMovement<Va: VirtualAddress> {
    pub make_path: Option<Va>,
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
    let arg_cache = &analysis.arg_cache;

    let value_area = match simple_switch_branch(binary, aiscript_hook.switch_table, 0x2a) {
        Some(s) => s,
        None => return result,
    };
    // Set script->player to 0, x to 999 and y to 998
    let mut state = E::initial_state(ctx, binary);
    let player = ctx.mem32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_player(),
    );
    let x = ctx.mem32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_center(),
    );
    let y = ctx.mem32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_center() + 4,
    );
    state.move_to(&DestOperand::from_oper(player), ctx.const_0());
    state.move_to(&DestOperand::from_oper(x), ctx.constant(999));
    state.move_to(&DestOperand::from_oper(y), ctx.constant(998));
    let mut analysis = FuncAnalysis::with_state(
        binary,
        ctx,
        value_area,
        state,
    );
    let mut analyzer = RegionsAnalyzer {
        result: &mut result,
        inlining: false,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct RegionsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut RegionRelated<'e, E::VirtualAddress>,
    inlining: bool,
    arg_cache: &'a ArgCache<'e, E>,
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
        match ctx.and_const(ctrl.resolve(self.arg_cache.on_call(1)), 0xffff).if_constant() {
            // GetRegion(x, y) call?
            Some(998) => {
                if ctx.and_const(
                    ctrl.resolve(self.arg_cache.on_call(0)),
                    0xffff,
                ).if_constant() == Some(999) {
                    self.result.get_region = Some(dest);
                    return true;
                }
            }
            // SetAiRegionState call?
            Some(5) => {
                let arg1 =  ctrl.resolve(self.arg_cache.on_call(0));
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
        arg_cache: &actx.arg_cache,
        state: StepUnitMovementState::Switch,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct StepUnitMovementAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepUnitMovement<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
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
                        let a1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let a2 = ctrl.resolve(self.arg_cache.on_call(1));
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
