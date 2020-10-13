use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation, DestOperand};

use crate::{AnalysisCtx, ArgCache, OptionExt, single_result_assign};

#[derive(Clone, Debug)]
pub struct RegionRelated<'e, Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Operand<'e>>,
    pub change_ai_region_state: Option<Va>,
}

impl<'e, Va: VirtualAddress> RegionRelated<'e, Va> {
    fn any_empty(&self) -> bool {
        self.get_region.is_none() ||
            self.ai_regions.is_none() ||
            self.change_ai_region_state.is_none()
    }
}

pub(crate) fn regions<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> RegionRelated<'e, E::VirtualAddress> {
    let mut result = RegionRelated {
        get_region: None,
        ai_regions: None,
        change_ai_region_state: None,
    };

    // Find things through aiscript value_area
    let aiscript_hook = analysis.aiscript_hook();
    let aiscript_hook = match aiscript_hook.as_ref() {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = analysis.arg_cache;

    let value_area = match binary.read_u32(aiscript_hook.switch_table + 0x2a * 4) {
        Ok(o) => E::VirtualAddress::from_u64(o as u64),
        Err(_) => return result,
    };
    // Set script->player to 0, x to 999 and y to 998
    let mut state = E::initial_state(ctx, binary);
    let player = ctx.mem32(ctx.add(
        aiscript_hook.script_operand_at_switch,
        ctx.constant(0x10),
    ));
    let x = ctx.mem32(ctx.add(
        aiscript_hook.script_operand_at_switch,
        ctx.constant(0x24),
    ));
    let y = ctx.mem32(ctx.add(
        aiscript_hook.script_operand_at_switch,
        ctx.constant(0x28),
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
                let dest = ctrl.resolve(dest);
                if let Some(dest) = dest.if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
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
                    let cond = ctrl.resolve(condition);
                    let to = ctrl.resolve(to);
                    // Early break on nonconditional backwards jumps
                    let seems_switch_loop = {
                        cond.if_constant()
                            .filter(|&c| c != 0)
                            .is_some()
                    } && {
                        to.if_constant()
                            .filter(|&c| c < ctrl.address().as_u64())
                            .is_some()
                    };
                    if !self.result.any_empty() && seems_switch_loop {
                        ctrl.end_analysis();
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
        fn is_undef_mul_34(op: Operand<'_>) -> bool {
            op.if_arithmetic_mul()
                .and_either_other(|x| x.if_constant().filter(|&c| c == 0x34))
                .filter(|y| {
                    y.iter().any(|y| y.is_undefined())
                })
                .is_some()
        }

        match ctrl.resolve(self.arg_cache.on_call(1)).if_constant() {
            // GetRegion(x, y) call?
            Some(998) => {
                if ctrl.resolve(self.arg_cache.on_call(0)).if_constant() == Some(999) {
                    self.result.get_region = Some(dest);
                    return true;
                }
            }
            // SetAiRegionState call?
            Some(5) => {
                let arg1 =  ctrl.resolve(self.arg_cache.on_call(0));
                let ai_regions = arg1.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        if is_undef_mul_34(l) {
                            r.if_mem32()
                        } else if is_undef_mul_34(r) {
                            l.if_mem32()
                        } else {
                            None
                        }
                    });
                if let Some(ai_regions_addr) = ai_regions {
                    self.result.ai_regions = Some(ai_regions_addr.clone());
                    self.result.change_ai_region_state = Some(dest);
                }
            }
            _ => (),
        }
        false
    }
}

pub(crate) fn pathing<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let get_region = analysis.regions().get_region?;

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
