use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation, DestOperand};

use crate::{AnalysisCtx, ArgCache, ControlExt, OperandExt, OptionExt, single_result_assign};
use crate::struct_layouts;
use crate::switch::simple_switch_branch;

#[derive(Clone, Debug)]
pub struct RegionRelated<'e, Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Operand<'e>>,
    pub change_ai_region_state: Option<Va>,
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
    let player = ctx.mem32(ctx.add_const(
        aiscript_hook.script_operand_at_switch,
        struct_layouts::ai_script_player::<E::VirtualAddress>(),
    ));
    let x = ctx.mem32(ctx.add_const(
        aiscript_hook.script_operand_at_switch,
        struct_layouts::ai_script_center::<E::VirtualAddress>(),
    ));
    let y = ctx.mem32(ctx.add_const(
        aiscript_hook.script_operand_at_switch,
        struct_layouts::ai_script_center::<E::VirtualAddress>() + 4,
    ));
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
            Operation::Jump { condition, to } => {
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
                        x.if_arithmetic_mul_const(
                            struct_layouts::ai_region_size::<E::VirtualAddress>()
                        ).filter(|x| x.contains_undefined())
                    })
                    .and_then(|x| ctrl.if_mem_word(x));
                if let Some(ai_regions_addr) = ai_regions {
                    self.result.ai_regions = Some(ai_regions_addr);
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
        // Finds `x` in `x + 0xc + 0x2 * y`
        fn find_base<'e>(addr: Operand<'e>) -> Option<Operand<'e>> {
            struct State {
                const_c_seen: bool,
                mul_2_seen: bool,
            }

            fn recurse<'e>(state: &mut State, addr: Operand<'e>) -> Option<Operand<'e>> {
                fn check_offset_oper<'e>(state: &mut State, op: Operand<'e>) -> Option<()> {
                    let offset = op.if_constant().filter(|&x| x == 0xc).is_some();
                    let index = op.if_arithmetic_mul()
                        .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                        .filter(|&(c, _)| c == 2).is_some();
                    if offset {
                        state.const_c_seen = true;
                        Some(())
                    } else if index {
                        state.mul_2_seen = true;
                        Some(())
                    } else {
                        None
                    }
                }

                addr.if_arithmetic_add().and_then(|(l, r)| {
                    let either = Operand::either(l, r, |x| check_offset_oper(state, x));
                    match either {
                        None => {
                            let left = recurse(state, l);
                            let right = recurse(state, r);
                            match (left, right) {
                                (Some(x), None) | (None, Some(x)) => Some(x),
                                _ => None,
                            }
                        }
                        Some(((), other)) => {
                            if check_offset_oper(state, other).is_some() {
                                None
                            } else {
                                Some(recurse(state, other).unwrap_or_else(|| other))
                            }
                        }
                    }
                })
            }
            let mut state = State {
                const_c_seen: false,
                mul_2_seen: false,
            };
            recurse(&mut state, addr)
                .filter(|_| state.const_c_seen && state.mul_2_seen)
        }

        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let addr = condition.iter_no_mem_addr()
                    .flat_map(|x| x.if_mem16())
                    .next();
                if let Some(addr) = addr {
                    let val = find_base(addr);
                    if single_result_assign(val, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
