use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, OperandType, Operation};

use crate::{
    Analysis, DatType, OptionExt, EntryOf, ArgCache, single_result_assign,
    find_functions_using_global, entry_of_until,
};

#[derive(Clone, Debug)]
pub struct ActiveHiddenUnits {
    pub first_active_unit: Option<Rc<Operand>>,
    pub first_hidden_unit: Option<Rc<Operand>>,
}

#[derive(Clone, Debug)]
pub struct OrderIssuing<Va: VirtualAddress> {
    pub order_init_arbiter: Option<Va>,
    pub prepare_issue_order: Option<Va>,
    pub do_next_queued_order: Option<Va>,
}

pub fn active_hidden_units<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> ActiveHiddenUnits {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = analysis.functions();
    // There's a function which accesses orders_dat_use_weapon_targeting, and loops through
    // both active and hidden units.

    let mut weapon_order_refs = {
        let orders_dat = analysis.dat_virtual_address(DatType::Orders);
        orders_dat.and_then(|(dat, dat_table_size)| {
            binary.read_address(dat + 1 * dat_table_size).ok().map(|weapon_orders| {
                find_functions_using_global(analysis, weapon_orders)
                    .into_iter()
                    .map(|x| (weapon_orders, x))
                    .collect::<Vec<_>>()
            })
        }).unwrap_or_else(|| Vec::new())
    };
    weapon_order_refs.sort_by_key(|x| x.1.func_entry);
    weapon_order_refs.dedup_by_key(|x| x.1.func_entry);
    let mut result = None;
    for (global_addr, global_ref) in weapon_order_refs {
        let val = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = ActiveHiddenAnalyzer::<E> {
                candidates: Vec::new(),
                inlining: None,
                memref_found: false,
                memref_address: global_addr,
            };
            analysis.analyze(&mut analyzer);
            if analyzer.candidates.len() == 2 {
                let (a1, unit1) = analyzer.candidates.pop().unwrap();
                let (a2, unit2) = analyzer.candidates.pop().unwrap();
                if unit1 != unit2 {
                    if a1 > a2 {
                        return EntryOf::Ok((unit2, unit1));
                    } else {
                        return EntryOf::Ok((unit1, unit2));
                    }
                }
            }
            if analyzer.memref_found {
                EntryOf::Stop
            } else {
                EntryOf::Retry
            }
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    match result {
        Some((a, h)) => ActiveHiddenUnits {
            first_active_unit: Some(a),
            first_hidden_unit: Some(h),
        },
        None => ActiveHiddenUnits {
            first_active_unit: None,
            first_hidden_unit: None,
        },
    }
}

struct ActiveHiddenAnalyzer<'e, E: ExecutionState<'e>> {
    /// To sort correctly with inlining, store (call ins address, ins address)
    candidates: Vec<((E::VirtualAddress, E::VirtualAddress), Rc<Operand>)>,
    /// call instruction address
    inlining: Option<E::VirtualAddress>,
    memref_found: bool,
    memref_address: E::VirtualAddress,
}

fn check_active_hidden_cond(condition: &Operand) -> Option<Rc<Operand>> {
    // It's doing something comparing to subunit ptr, should have written a comment :l
    // Mem32[unit + 70] == 0
    condition.if_arithmetic_eq()
        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
        .and_then(|x| x.if_memory())
        .and_then(|mem| mem.address.if_arithmetic_add())
        .and_either_other(|x| x.if_constant().filter(|&c| c == 0x70))
        .filter(|unit| {
            // Ignore if contains undef
            unit.iter().all(|x| match x.ty {
                OperandType::Undefined(_) => false,
                _ => true,
            })
        })
        .cloned()
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for ActiveHiddenAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Move(_, val, _cond) => {
                if !self.memref_found {
                    let val = ctrl.resolve(val);
                    if let Some(mem) = val.if_memory() {
                        self.memref_found = mem.address.iter().any(|x| match x.if_constant() {
                            Some(c) => c == self.memref_address.as_u64(),
                            None => false,
                        });
                    }
                }
            }
            Operation::Call(dest) => {
                if self.inlining.is_none() {
                    let dest = ctrl.resolve(dest);
                    if let Some(dest) = dest.if_constant() {
                        self.inlining = Some(ctrl.address());
                        ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                        ctrl.skip_operation();
                        self.inlining = None;
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                if let Some(addr) = check_active_hidden_cond(&condition) {
                    // A way to work around duplicates from loops.
                    // Could also check to only accept constant addr,
                    // but I'm scared that it'll change one day.
                    let address = ctrl.address();
                    let parent_address = self.inlining.unwrap_or_else(|| address);
                    if !self.candidates.iter().any(|x| x.0 == (parent_address, address)) {
                        self.candidates.push(((parent_address, address), addr));
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn order_issuing<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> OrderIssuing<E::VirtualAddress> {
    use scarf::operand_helpers::*;
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    // Search for units_dat_idle_order[arbiter] to find Order_CloakingNearbyUnits

    let mut arbiter_idle_orders = {
        let units_dat = analysis.dat_virtual_address(DatType::Units);
        units_dat.and_then(|(dat, dat_table_size)| {
            binary.read_address(dat + 0xe * dat_table_size).ok().map(|idle_orders| {
                let address = idle_orders + 0x47;
                let order = mem8(ctx.constant(address.as_u64()));
                find_functions_using_global(analysis, address)
                    .into_iter()
                    .map(move |global_ref| (global_ref, order.clone()))
                    .collect::<Vec<_>>()
            })
        }).unwrap_or_else(|| Vec::new())
    };
    arbiter_idle_orders.sort_by_key(|x| (x.0.func_entry, x.1.clone()));
    arbiter_idle_orders.dedup_by_key(|x| (x.0.func_entry, x.1.clone()));
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    for (global_ref, order) in arbiter_idle_orders {
        let order_init_arbiter = global_ref.func_entry;
        let mut analysis = FuncAnalysis::new(binary, &ctx, order_init_arbiter);
        let mut analyzer = OrderIssuingAnalyzer {
            func_results: Vec::new(),
            inlining: false,
            order,
            arg_cache,
        };
        analysis.analyze(&mut analyzer);
        if analyzer.func_results.len() == 2 {
            let dnqo = analyzer.func_results.pop().unwrap();
            let prepare = analyzer.func_results.pop().unwrap();
            if single_result_assign(Some((prepare, dnqo, order_init_arbiter)), &mut result) {
                break;
            }
        }
    }

    OrderIssuing {
        prepare_issue_order: result.as_ref().map(|&x| x.0),
        do_next_queued_order: result.as_ref().map(|&x| x.1),
        order_init_arbiter: result.as_ref().map(|&x| x.2),
    }
}

struct OrderIssuingAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    func_results: Vec<E::VirtualAddress>,
    inlining: bool,
    order: Rc<Operand>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for OrderIssuingAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.func_results.len() == 0 {
                        let ok = Some(ctrl.resolve(&self.arg_cache.on_call(0)))
                            .filter(|x| *x == self.order)
                            .map(|_| ctrl.resolve(&self.arg_cache.on_call(1)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(&self.arg_cache.on_call(2)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(&self.arg_cache.on_call(3)))
                            .filter(|x| x.if_constant() == Some(0xe4))
                            .is_some();
                        if ok {
                            self.func_results.push(dest);
                            return;
                        }
                    } else if self.func_results.len() == 1 {
                        self.func_results.push(dest);
                        ctrl.end_analysis();
                        return;
                    }

                    if !self.inlining {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.func_results.len() == 2 {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}
