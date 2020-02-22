use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, OperandType, Operation};

use crate::{
    Analysis, DatType, OptionExt, EntryOf, ArgCache, StringRefs, single_result_assign,
    find_functions_using_global, entry_of_until, string_refs,
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

pub fn units<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Rc<Operand>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let init_units = analysis.init_units()?;

    let arg_cache = &analysis.arg_cache;
    let mut analyzer = UnitsAnalyzer {
        result: None,
        arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_units);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct UnitsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<Rc<Operand>>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for UnitsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                if ctrl.resolve(dest).if_constant().is_some() {
                    let new = self.check_memcpy(ctrl);
                    if single_result_assign(new, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> UnitsAnalyzer<'a, 'e, E> {
    fn check_memcpy(&self, ctrl: &mut Control<'e, '_, '_, Self>) -> Option<Rc<Operand>> {
        let arg2 = ctrl.resolve(&self.arg_cache.on_call(1));
        if arg2.ty != OperandType::Constant(0) {
            return None;
        }
        let arg3 = ctrl.resolve(&self.arg_cache.on_call(2));
        let unit_size = if E::VirtualAddress::SIZE == 4 {
            0x150
        } else {
            0x1e8
        };
        let arg3_ok = (
            arg3.if_arithmetic_mul()
                .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                .map(|(c, _)| c == unit_size)
                .unwrap_or(false)
            ) || (
                arg3.if_constant().map(|c| c == unit_size * 1700).unwrap_or(false)
            );
        if arg3_ok {
            Some(ctrl.resolve(&self.arg_cache.on_call(0)))
        } else {
            None
        }
    }

}

pub fn init_units<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let units = analysis.dat(DatType::Units)?;
    let orders = analysis.dat(DatType::Orders)?;
    let mut unit_refs = Vec::new();
    let mut order_refs = Vec::new();
    {
        let mut arr = [(&units, &mut unit_refs), (&orders, &mut order_refs)];
        for &mut (ref dat, ref mut out) in &mut arr {
            **out = dat.address.iter()
                .filter_map(|x| x.if_constant())
                .flat_map(|x| {
                    find_functions_using_global(analysis, E::VirtualAddress::from_u64(x))
                }).collect::<Vec<_>>()
        }
    }
    let str_refs = string_refs(binary, analysis, b"arr\\units.dat\0");

    let mut common = unit_refs.iter()
        .filter(|x| order_refs.iter().any(|y| x.func_entry == y.func_entry))
        .filter(|x| str_refs.iter().any(|y| x.func_entry == y.func_entry))
        .map(|x| x.func_entry)
        .next();
    if common.is_none() {
        // Different strategy if a fake call happens to be in between orders and units
        struct Analyzer<'a, 'f, F: ExecutionState<'f>> {
            units_dat_seen: bool,
            units_dat: &'a Rc<Operand>,
            units_dat_str_seen: bool,
            units_dat_str_refs: &'a [StringRefs<F::VirtualAddress>],
        }
        impl<'a, 'f: 'a, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'a, 'f, F> {
            type State = analysis::DefaultState;
            type Exec = F;
            fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation) {
                match *op {
                    Operation::Move(_, ref from, None) => {
                        let from = ctrl.resolve(from);
                        for oper in from.iter() {
                            if *oper == **self.units_dat {
                                self.units_dat_seen = true;
                            }
                        }
                        let str_ref_addr = self.units_dat_str_refs.iter().any(|x| {
                            x.use_address >= ctrl.address() &&
                                x.use_address < ctrl.current_instruction_end()
                        });
                        if str_ref_addr {
                            self.units_dat_str_seen = true;
                        }
                        if self.units_dat_seen && self.units_dat_str_seen {
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
        }

        common = order_refs.iter().filter(|order_ref| {
            let mut analyzer = Analyzer::<E> {
                units_dat_seen: false,
                units_dat: &units.address,
                units_dat_str_seen: false,
                units_dat_str_refs: &str_refs[..],
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, order_ref.func_entry);
            analysis.analyze(&mut analyzer);
            analyzer.units_dat_seen && analyzer.units_dat_str_seen
        }).map(|x| x.func_entry).next();
    }

    common
}
