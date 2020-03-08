use std::mem;
use std::rc::Rc;

use scarf::analysis::{self, FuncAnalysis, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Operation, Operand, OperandType, MemAccessSize, DestOperand};

use crate::{
    Analysis, ArgCache, DatType, OptionExt, find_functions_using_global, single_result_assign,
    if_callable_const,
};

#[derive(Clone, Debug)]
pub struct Rng {
    pub enable: Option<Rc<Operand>>,
    pub seed: Option<Rc<Operand>>,
}

pub fn rng<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Rc<Rng> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    // Find the rng from searching the code that checks if unit spawn direction == 0x20 and
    // random direction

    let mut spawn_direction_refs = {
        let units_dat = analysis.dat_virtual_address(DatType::Units);
        units_dat.and_then(|(dat, dat_table_size)| {
            binary.read_address(dat + 5 * dat_table_size).ok().map(|spawn_directions| {
                find_functions_using_global(analysis, spawn_directions)
            })
        }).unwrap_or_else(|| Vec::new())
    };
    spawn_direction_refs.sort_by_key(|x| x.func_entry);
    spawn_direction_refs.dedup_by_key(|x| x.func_entry);
    let arg_cache = &analysis.arg_cache;

    let mut result = None;
    for global_ref in spawn_direction_refs.iter() {
        let mut analysis = FuncAnalysis::new(binary, &ctx, global_ref.func_entry);
        let mut analyzer = FindRng {
            jump_conds: Vec::new(),
            result: None,
            no_jump_cond: None,
            arg_cache,
            is_inlining: false,
            binary,
            branch_start: E::VirtualAddress::from_u64(0),
        };
        analysis.analyze(&mut analyzer);
        if single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    Rc::new(match result {
        Some((s, e)) => Rng {
            seed: Some(s),
            enable: Some(e),
        },
        None => Rng {
            seed: None,
            enable: None,
        },
    })
}

struct FindRng<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    result: Option<(Rc<Operand>, Rc<Operand>)>,
    no_jump_cond: Option<Rc<Operand>>,
    jump_conds: Vec<(E::VirtualAddress, Rc<Operand>)>,
    is_inlining: bool,
    binary: &'e BinaryFile<E::VirtualAddress>,
    branch_start: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindRng<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        use scarf::operand_helpers::*;
        match op {
            Operation::Call(dest) => {
                if let Some(dest) = if_callable_const(self.binary, dest, ctrl) {
                    let arg1 = ctrl.resolve(&self.arg_cache.on_call(0));
                    if arg1.if_constant() == Some(0x24) {
                        if !self.is_inlining {
                            let jump_conds = mem::replace(&mut self.jump_conds, Vec::new());
                            self.is_inlining = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.is_inlining = false;
                            self.jump_conds = jump_conds;
                            if self.result.is_some() && !crate::test_assertions() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if let Some(to) = ctrl.resolve_apply_constraints(to).if_constant() {
                    if let Some(enable) = is_rng_enable_condition(&condition) {
                        self.jump_conds.push((E::VirtualAddress::from_u64(to), enable.clone()));
                        self.no_jump_cond = Some(enable);
                    }
                }
            }
            Operation::Move(dest, val, _cond) => {
                if let DestOperand::Memory(ref mem) = dest {
                    if mem.size == MemAccessSize::Mem32 {
                        let val = ctrl.resolve(&val);
                        if val.iter().any(|x| x.if_constant() == Some(0x015A_4E35)) {
                            let jump_cond = self.jump_conds.iter()
                                .filter(|x| x.0 == self.branch_start)
                                .map(|x| &x.1)
                                .next();
                            if let Some(rng_enable) = jump_cond {
                                let dest = ctrl.resolve(&mem.address);
                                let val = (mem32(dest), rng_enable.clone());
                                if single_result_assign(Some(val), &mut self.result) {
                                    ctrl.end_analysis();
                                }
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

fn is_rng_enable_condition(cond: &Rc<Operand>) -> Option<Rc<Operand>> {
    crate::if_arithmetic_eq_neq(cond)
        .map(|(l, r, _)| (l, r))
        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
        .filter(|x| {
            x.if_mem32()
                .filter(|x| {
                    x.iter().all(|part| match part.ty {
                        OperandType::Undefined(_) => false,
                        _ => true,
                    })
                })
                .is_some()
        })
        .cloned()
}
