use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress, InternMap};
use scarf::{Operand, OperandType, Operation, DestOperand};

use crate::{Analysis, ArgCache, OptionExt, single_result_assign};

#[derive(Clone, Debug)]
pub struct RegionRelated<Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Rc<Operand>>,
    pub change_ai_region_state: Option<Va>,
}

impl<Va: VirtualAddress> RegionRelated<Va> {
    fn any_empty(&self) -> bool {
        self.get_region.is_none() ||
            self.ai_regions.is_none() ||
            self.change_ai_region_state.is_none()
    }
}

pub fn regions<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> RegionRelated<E::VirtualAddress> {
    use scarf::operand_helpers::*;

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
    let arg_cache = &analysis.arg_cache;

    let value_area = match binary.read_u32(aiscript_hook.switch_table + 0x2a * 4) {
        Ok(o) => E::VirtualAddress::from_u64(o as u64),
        Err(_) => return result,
    };
    // Set script->player to 0, x to 999 and y to 998
    let mut interner = InternMap::new();
    let mut state = E::initial_state(ctx, binary, &mut interner);
    let player = mem32(operand_add(
        aiscript_hook.script_operand_at_switch.clone(),
        ctx.constant(0x10),
    ));
    let x = mem32(operand_add(
        aiscript_hook.script_operand_at_switch.clone(),
        ctx.constant(0x24),
    ));
    let y = mem32(operand_add(
        aiscript_hook.script_operand_at_switch.clone(),
        ctx.constant(0x28),
    ));
    state.move_to(&DestOperand::from_oper(&player), ctx.const_0(), &mut interner);
    state.move_to(&DestOperand::from_oper(&x), ctx.constant(999), &mut interner);
    state.move_to(&DestOperand::from_oper(&y), ctx.constant(998), &mut interner);
    let mut analysis = FuncAnalysis::with_state(
        binary,
        ctx,
        value_area,
        state,
        interner,
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
    result: &'a mut RegionRelated<E::VirtualAddress>,
    inlining: bool,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for RegionsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
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
            Operation::Jump { ref condition, ref to } => {
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
        fn is_undef_mul_34(op: &Operand) -> bool {
            op.if_arithmetic_mul()
                .and_either_other(|x| x.if_constant().filter(|&c| c == 0x34))
                .filter(|y| {
                    y.iter().any(|y| match y.ty {
                        OperandType::Undefined(_) => true,
                        _ => false,
                    })
                })
                .is_some()
        }

        match ctrl.resolve(&self.arg_cache.on_call(1)).if_constant() {
            // GetRegion(x, y) call?
            Some(998) => {
                if ctrl.resolve(&self.arg_cache.on_call(0)).if_constant() == Some(999) {
                    self.result.get_region = Some(dest);
                    return true;
                }
            }
            // SetAiRegionState call?
            Some(5) => {
                let arg1 =  ctrl.resolve(&self.arg_cache.on_call(0));
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

pub fn pathing<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Rc<Operand>> {
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
    result: Option<Rc<Operand>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindPathing<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        // Finds `x` in `x + 0xc + 0x2 * y`
        fn find_base(addr: &Rc<Operand>) -> Option<&Rc<Operand>> {
            struct State {
                const_c_seen: bool,
                mul_2_seen: bool,
            }

            fn recurse<'a>(state: &mut State, addr: &'a Rc<Operand>) -> Option<&'a Rc<Operand>> {
                fn check_offset_oper(state: &mut State, op: &Rc<Operand>) -> Option<()> {
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

        match op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let addr = condition.iter_no_mem_addr()
                    .flat_map(|x| x.if_mem16())
                    .next();
                if let Some(addr) = addr {
                    let val = find_base(addr).cloned();
                    if single_result_assign(val, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
