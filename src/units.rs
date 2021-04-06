use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, Operation};

use crate::{
    AnalysisCtx, ControlExt, OptionExt, OperandExt, EntryOf, ArgCache, single_result_assign,
    entry_of_until, unwrap_sext, bumpvec_with_capacity, FunctionFinder, if_arithmetic_eq_neq,
};

#[derive(Clone, Debug)]
pub struct ActiveHiddenUnits<'e> {
    pub first_active_unit: Option<Operand<'e>>,
    pub first_hidden_unit: Option<Operand<'e>>,
}

#[derive(Clone, Debug)]
pub struct OrderIssuing<Va: VirtualAddress> {
    pub order_init_arbiter: Option<Va>,
    pub prepare_issue_order: Option<Va>,
    pub do_next_queued_order: Option<Va>,
}

#[derive(Clone, Debug)]
pub struct InitUnits<Va: VirtualAddress> {
    pub init_units: Option<Va>,
    pub load_dat: Option<Va>,
}

pub(crate) fn active_hidden_units<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    orders_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> ActiveHiddenUnits<'e> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    // There's a function which accesses orders_dat_use_weapon_targeting, and loops through
    // both active and hidden units.

    let mut weapon_order_refs = {
        let (dat, dat_table_size) = orders_dat;
        Some(()).and_then(|()| {
            binary.read_address(dat + 1 * dat_table_size).ok().map(|weapon_orders| {
                let funcs = functions.find_functions_using_global(analysis, weapon_orders)
                    .into_iter()
                    .map(move |x| (weapon_orders, x));
                BumpVec::from_iter_in(funcs, bump)
            })
        }).unwrap_or_else(|| BumpVec::new_in(bump))
    };
    weapon_order_refs.sort_unstable_by_key(|x| x.1.func_entry);
    weapon_order_refs.dedup_by_key(|x| x.1.func_entry);
    let mut result = None;
    let functions = functions.functions();
    for (global_addr, global_ref) in weapon_order_refs {
        let val = entry_of_until(binary, functions, global_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = ActiveHiddenAnalyzer::<E> {
                candidates: bumpvec_with_capacity(8, bump),
                inlining: None,
                memref_found: false,
                memref_address: global_addr,
            };
            analysis.analyze(&mut analyzer);
            if analyzer.candidates.len() == 2 {
                let (a1, unit1) = analyzer.candidates[0];
                let (a2, unit2) = analyzer.candidates[1];
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

struct ActiveHiddenAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    /// To sort correctly with inlining, store (call ins address, ins address)
    candidates: BumpVec<'acx, ((E::VirtualAddress, E::VirtualAddress), Operand<'e>)>,
    /// call instruction address
    inlining: Option<E::VirtualAddress>,
    memref_found: bool,
    memref_address: E::VirtualAddress,
}

fn check_active_hidden_cond<'e>(condition: Operand<'e>) -> Option<Operand<'e>> {
    // It's doing something comparing to subunit ptr, should have written a comment :l
    // Mem32[unit + 70] == 0
    condition.if_arithmetic_eq()
        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
        .and_then(|x| x.if_memory())
        .and_then(|mem| mem.address.if_arithmetic_add())
        .and_either_other(|x| x.if_constant().filter(|&c| c == 0x70))
        .filter(|unit| {
            // Ignore if contains undef
            unit.iter().all(|x| !x.is_undefined())
        })
}

impl<'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    ActiveHiddenAnalyzer<'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
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
                if let Some(addr) = check_active_hidden_cond(condition) {
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

pub(crate) fn order_issuing<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> OrderIssuing<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    // Search for units_dat_idle_order[arbiter] to find Order_CloakingNearbyUnits

    let mut arbiter_idle_orders = {
        let (dat, dat_table_size) = units_dat;
        let idle_orders = binary.read_address(dat + 0xe * dat_table_size)
            .unwrap_or_else(|_| E::VirtualAddress::from_u64(0));
        let address = idle_orders + 0x47;
        let order = ctx.mem8(ctx.constant(address.as_u64()));
        let funcs = functions.find_functions_using_global(analysis, address)
            .into_iter()
            .map(move |global_ref| (global_ref, order.clone()));
        BumpVec::from_iter_in(funcs, bump)
    };
    arbiter_idle_orders.sort_unstable_by_key(|x| (x.0.func_entry, x.1.clone()));
    arbiter_idle_orders.dedup_by_key(|x| (x.0.func_entry, x.1.clone()));
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    for (global_ref, order) in arbiter_idle_orders {
        let order_init_arbiter = global_ref.func_entry;
        let mut analysis = FuncAnalysis::new(binary, ctx, order_init_arbiter);
        let mut analyzer = OrderIssuingAnalyzer {
            func_results: bumpvec_with_capacity(8, bump),
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
    func_results: BumpVec<'a, E::VirtualAddress>,
    inlining: bool,
    order: Operand<'e>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for OrderIssuingAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.func_results.len() == 0 {
                        let ok = Some(ctrl.resolve(self.arg_cache.on_call(0)))
                            .filter(|x| *x == self.order)
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
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

pub(crate) fn units<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    init_units: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

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
    result: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for UnitsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if ctrl.resolve(dest).if_constant().is_some() {
                    let new = self.check_memset(ctrl);
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
    fn check_memset(&self, ctrl: &mut Control<'e, '_, '_, Self>) -> Option<Operand<'e>> {
        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
        if arg2.if_constant() != Some(0) {
            return None;
        }
        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
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
            Some(ctrl.resolve(self.arg_cache.on_call(0)))
        } else {
            None
        }
    }

}

pub(crate) fn init_units<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units: (E::VirtualAddress, u32),
    orders: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> InitUnits<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = InitUnits {
        init_units: None,
        load_dat: None,
    };

    let mut order_refs = BumpVec::new_in(bump);
    {
        let mut arr = [(&orders, &mut order_refs)];
        for &mut (ref dat, ref mut out) in &mut arr {
            out.extend(
                functions.find_functions_using_global(analysis, dat.0)
            );
        }
    }

    struct Analyzer<'a, 'e, F: ExecutionState<'e>> {
        units_dat: Operand<'e>,
        arg_cache: &'a ArgCache<'e, F>,
        binary: &'e BinaryFile<F::VirtualAddress>,
        limit: u8,
        result: &'a mut InitUnits<F::VirtualAddress>,
    }
    impl<'a, 'f: 'a, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'a, 'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation<'f>) {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = F::VirtualAddress::from_u64(dest);
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        let compare_str = b"arr\\units.dat\0";
                        let ok = arg1.if_constant()
                            .map(|x| F::VirtualAddress::from_u64(x))
                            .and_then(|addr| {
                                self.binary.slice_from_address(addr, compare_str.len() as u32)
                                    .ok()
                            })
                            .filter(|slice| slice.eq_ignore_ascii_case(compare_str))
                            .filter(|_| arg2 == self.units_dat)
                            .is_some();
                        if ok {
                            self.result.load_dat = Some(dest);
                            ctrl.end_analysis();
                        }
                        self.limit -= 1;
                        if self.limit == 0 {
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let arg_cache = &analysis.arg_cache;
    let mut checked = bumpvec_with_capacity(8, bump);
    for order_ref in &order_refs {
        if checked.iter().any(|&x| x == order_ref.func_entry) {
            continue;
        }
        let mut analyzer = Analyzer::<E> {
            units_dat: ctx.constant(units.0.as_u64()),
            arg_cache,
            binary,
            result: &mut result,
            limit: 8,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, order_ref.func_entry);
        analysis.analyze(&mut analyzer);
        if result.load_dat.is_some() {
            result.init_units = Some(order_ref.func_entry);
            break;
        }
        checked.push(order_ref.func_entry);
    }
    result
}

#[derive(Debug, Clone)]
pub struct UnitCreation<Va: VirtualAddress> {
    pub create_unit: Option<Va>,
    pub finish_unit_pre: Option<Va>,
    pub finish_unit_post: Option<Va>,
}

pub(crate) fn unit_creation<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_scan: E::VirtualAddress,
) -> UnitCreation<E::VirtualAddress> {
    let mut result = UnitCreation {
        create_unit: None,
        finish_unit_pre: None,
        finish_unit_post: None,
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // create_unit(id, x, y, player, skin)
    // Search for create_unit(0x21, Mem16[..], Mem16[..], Mem8[..], ..)

    let arg_cache = &analysis.arg_cache;
    let mut analyzer = UnitCreationAnalyzer::<E> {
        result: &mut result,
        arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_scan);
    analysis.analyze(&mut analyzer);
    if let Some(pre) = result.finish_unit_pre {
        if result.finish_unit_post.is_none() {
            // finish_unit_pre is actually finish_unit, analyze that,
            // hopefully it's just 2 function calls
            result.finish_unit_pre = None;
            let mut analyzer = FinishUnitAnalyzer::<E> {
                result: &mut result,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, pre);
            analysis.analyze(&mut analyzer);
        }
    }
    result
}

struct FinishUnitAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut UnitCreation<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FinishUnitAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let this = ctx.register(1);
                    if ctrl.resolve(this) == this {
                        if self.result.finish_unit_pre.is_none() {
                            self.result.finish_unit_pre = Some(dest);
                        } else if self.result.finish_unit_post.is_none() {
                            self.result.finish_unit_post = Some(dest);
                        } else {
                            self.result.finish_unit_pre = None;
                            self.result.finish_unit_post = None;
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if ctrl.resolve(condition).if_constant().filter(|&c| c != 0).is_some() {
                    // Tail call finish_unit_post
                    if {
                        self.result.finish_unit_pre.is_some() &&
                            self.result.finish_unit_post.is_none()
                    } {
                        if let Some(to) = ctrl.resolve(to).if_constant() {
                            let to = E::VirtualAddress::from_u64(to);
                            self.result.finish_unit_post = Some(to);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
                self.result.finish_unit_pre = None;
                self.result.finish_unit_post = None;
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

struct UnitCreationAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut UnitCreation<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitCreationAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.result.create_unit.is_none() {
                        let ok = Some(ctrl.resolve(self.arg_cache.on_call(0)))
                            .filter(|&x| x.if_constant() == Some(0x21))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                            .filter(|&x| unwrap_sext(x).if_mem16().is_some())
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                            .filter(|&x| unwrap_sext(x).if_mem16().is_some())
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
                            .filter(|&x| x.if_mem8().is_some())
                            .is_some();
                        if ok {
                            self.result.create_unit = Some(dest);
                            ctrl.skip_operation();
                            let exec_state = ctrl.exec_state();
                            exec_state.move_to(
                                &DestOperand::Register64(scarf::operand::Register(0)),
                                ctx.custom(0),
                            );
                        }
                    } else {
                        if ctrl.resolve(ctx.register(1)) == ctx.custom(0) {
                            if self.result.finish_unit_pre.is_none() {
                                self.result.finish_unit_pre = Some(dest);
                            } else if self.result.finish_unit_post.is_none() {
                                self.result.finish_unit_post = Some(dest);
                                if crate::test_assertions() == false {
                                    ctrl.end_analysis();
                                }
                            } else if crate::test_assertions() {
                                panic!(
                                    "Calling a third function with ecx == unit @ {:x}",
                                    ctrl.address(),
                                );
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn strength<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    init_game: E::VirtualAddress,
    init_units: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut analyzer = StrengthAnalyzer::<E> {
        result: None,
        init_units,
        init_units_seen: false,
        candidate: None,
        inline_depth: 0,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_game);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct StrengthAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    init_units: E::VirtualAddress,
    init_units_seen: bool,
    candidate: Option<Operand<'e>>,
    inline_depth: u8,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StrengthAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if !self.init_units_seen {
                        if dest == self.init_units {
                            self.init_units_seen = true;
                        }
                        return;
                    }
                    if self.inline_depth < 2 {
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), _, None) => {
                if self.init_units_seen && mem.size == MemAccessSize::Mem32 {
                    let dest = ctrl.resolve(mem.address);
                    let base = dest.if_arithmetic_add()
                        .and_either_other(|x| x.if_arithmetic_mul_const(4));
                    if let Some(base) = base {
                        if let Some(old) = self.candidate {
                            let ctx = ctrl.ctx();
                            // Ground strength is guaranteed to be 0xe4 * 4 bytes after air
                            if ctx.add_const(old, 0xe4 * 4) == base {
                                self.result = Some(old);
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        self.candidate = Some(base);
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn give_unit<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    trigger_actions: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    // search for trigger_find_units(&rect, func, &params)
    // give_unit is at params offset 0xc
    let ctx = actx.ctx;
    let binary = actx.binary;
    let action_give_ptr = trigger_actions + E::VirtualAddress::SIZE * 0x30;
    let action_give = binary.read_address(action_give_ptr).ok()?;

    let mut analysis = FuncAnalysis::new(binary, ctx, action_give);
    let mut analyzer = FindGiveUnit::<E> {
        arg_cache: &actx.arg_cache,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindGiveUnit<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindGiveUnit<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(_) = *op {
            let arg2_ok = ctrl.resolve_va(self.arg_cache.on_call(1)).is_some();
            if arg2_ok {
                let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                let ctx = ctrl.ctx();
                let func = ctrl.read_memory(ctx.add_const(arg3, 0xc), E::WORD_SIZE);
                if let Some(func) = func.if_constant() {
                    if func >= ctrl.binary().base().as_u64() {
                        self.result = Some(E::VirtualAddress::from_u64(func));
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

pub(crate) fn set_unit_player<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    give_unit: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    // search for set_unit_player(this = a1, a2)
    let ctx = actx.ctx;
    let binary = actx.binary;

    let mut analysis = FuncAnalysis::new(binary, ctx, give_unit);
    let mut analyzer = FindSetUnitPlayer::<E> {
        arg_cache: &actx.arg_cache,
        result: None,
        skipped_branch: E::VirtualAddress::from_u64(0),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindSetUnitPlayer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    skipped_branch: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSetUnitPlayer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ctx = ctrl.ctx();
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let player = self.arg_cache.on_entry(1);
                    let arg1_ok = arg1 == player ||
                        arg1.if_arithmetic_or()
                            .and_either_other(|x| x.if_arithmetic_and())
                            .filter(|&x| x == ctx.and_const(player, 0xff))
                            .is_some();
                    if arg1_ok {
                        let this = ctrl.resolve(ctx.register(1));
                        if this == self.arg_cache.on_entry(0) {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                // Assume that player isn't 0xd (trigger current player),
                // so that later player comparision isn't undef
                let condition = ctrl.resolve(condition);
                let is_player_cmp_d = if_arithmetic_eq_neq(condition)
                    .map(|x| (x.0, x.1))
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0xd))
                    .filter(|&x| x == self.arg_cache.on_entry(1))
                    .is_some();
                if is_player_cmp_d {
                    self.skipped_branch = ctrl.current_instruction_end();
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if ctrl.address() == self.skipped_branch {
            ctrl.end_branch();
        }
    }
}
