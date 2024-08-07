use std::mem;

use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, FuncAnalysis, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operation, Operand, OperandCtx, MemAccessSize, DestOperand};

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::util::{single_result_assign, ControlExt, OperandExt};

#[derive(Clone, Debug)]
pub struct Rng<'e> {
    pub enable: Option<Operand<'e>>,
    pub seed: Option<Operand<'e>>,
}

pub(crate) fn rng<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> Rng<'e> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    // Find the rng from searching the code that checks if unit spawn direction == 0x20 and
    // random direction

    let mut spawn_direction_refs = {
        let (dat, dat_table_size) = units_dat;
        Some(()).and_then(|()| {
            let spawn_directions = binary.read_address(dat + 5 * dat_table_size).ok()?;
            Some(functions.find_functions_using_global(analysis, spawn_directions))
        }).unwrap_or_else(|| BumpVec::new_in(bump))
    };
    spawn_direction_refs.sort_unstable_by_key(|x| x.func_entry);
    spawn_direction_refs.dedup_by_key(|x| x.func_entry);
    let functions = functions.functions();

    let mut result = None;
    for global_ref in spawn_direction_refs.iter() {
        let val = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = FindRng::<E> {
                jump_conds: BumpVec::new_in(bump),
                result: EntryOf::Retry,
                no_jump_cond: None,
                bump,
                is_inlining: false,
                use_address: global_ref.use_address,
                branch_start: E::VirtualAddress::from_u64(0),
            };
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    match result {
        Some((s, e)) => Rng {
            seed: Some(s),
            enable: Some(e),
        },
        None => Rng {
            seed: None,
            enable: None,
        },
    }
}

struct FindRng<'a, 'e, E: ExecutionState<'e>> {
    bump: &'a bumpalo::Bump,
    result: EntryOf<(Operand<'e>, Operand<'e>)>,
    no_jump_cond: Option<Operand<'e>>,
    jump_conds: BumpVec<'a, (E::VirtualAddress, Operand<'e>)>,
    is_inlining: bool,
    use_address: E::VirtualAddress,
    branch_start: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindRng<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            if !self.result.is_ok() {
                self.result = EntryOf::Stop;
            }
        }
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg1 = ctrl.resolve_arg(0);
                    if arg1.if_constant() == Some(0x24) {
                        if !self.is_inlining {
                            let jump_conds =
                                mem::replace(&mut self.jump_conds, BumpVec::new_in(self.bump));
                            self.is_inlining = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.is_inlining = false;
                            self.jump_conds = jump_conds;
                            if let EntryOf::Ok(..) = self.result {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if let Some(to) = ctrl.resolve_apply_constraints(to).if_constant() {
                    let ctx = ctrl.ctx();
                    if let Some(enable) = is_rng_enable_condition(condition, ctx) {
                        self.jump_conds.push((E::VirtualAddress::from_u64(to), enable));
                        self.no_jump_cond = Some(enable);
                    }
                }
            }
            Operation::Move(ref dest, val) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem32 {
                        let val = ctrl.resolve(val);
                        if val.iter().any(|x| x.if_constant() == Some(0x015A_4E35)) {
                            let jump_cond = self.jump_conds.iter()
                                .filter(|x| x.0 == self.branch_start)
                                .map(|x| x.1)
                                .next();
                            if let Some(rng_enable) = jump_cond {
                                let dest = ctrl.resolve_mem(mem);
                                let ctx = ctrl.ctx();
                                let val = (ctx.memory(&dest), rng_enable);
                                self.result = EntryOf::Ok(val);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.no_jump_cond = None;
        self.branch_start = ctrl.address();
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if let Some(no_jump_cond) = self.no_jump_cond.take() {
            self.jump_conds.push((ctrl.address(), no_jump_cond));
        }
    }
}

fn is_rng_enable_condition<'e>(cond: Operand<'e>, ctx: OperandCtx<'e>) -> Option<Operand<'e>> {
    cond.if_arithmetic_eq_neq_zero(ctx)
        .map(|x| x.0)
        .filter(|x| {
            x.if_mem32()
                .filter(|x| !x.address().0.contains_undefined())
                .is_some()
        })
}
