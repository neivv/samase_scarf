use std::convert::TryInto;

use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, OperandCtx, Operation};

use crate::{
    AnalysisCtx, ControlExt, OptionExt, OperandExt, EntryOf, ArgCache, single_result_assign,
    entry_of_until, bumpvec_with_capacity, FunctionFinder, if_arithmetic_eq_neq,
};
use crate::struct_layouts;

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

pub(crate) struct SetUnitPlayerFns<Va: VirtualAddress> {
    pub remove_from_selections: Option<Va>,
    pub remove_from_client_selection: Option<Va>,
    pub clear_build_queue: Option<Va>,
    pub unit_changing_player: Option<Va>,
    pub player_gained_upgrade: Option<Va>,
}

pub(crate) struct UnitSpeed<Va: VirtualAddress> {
    pub apply_speed_upgrades: Option<Va>,
    pub update_speed: Option<Va>,
    pub update_speed_iscript: Option<Va>,
    pub buffed_flingy_speed: Option<Va>,
    pub buffed_acceleration: Option<Va>,
    pub buffed_turn_speed: Option<Va>,
}

pub(crate) struct StepActiveUnitAnalysis<'e, Va: VirtualAddress> {
    pub step_unit_movement: Option<Va>,
    pub should_vision_update: Option<Operand<'e>>,
}

pub(crate) struct PrepareIssueOrderAnalysis<'e> {
    pub first_free_order: Option<Operand<'e>>,
    pub last_free_order: Option<Operand<'e>>,
    pub allocated_order_count: Option<Operand<'e>>,
    pub replay_bfix: Option<Operand<'e>>,
    pub replay_gcfg: Option<Operand<'e>>,
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

fn check_active_hidden_cond<'e, Va: VirtualAddress>(
    condition: Operand<'e>,
    ctx: OperandCtx<'e>,
) -> Option<Operand<'e>> {
    // It's doing something comparing to subunit ptr, should have written a comment :l
    // Mem32[unit + 70] == 0
    condition.if_arithmetic_eq()
        .filter(|&(_, r)| r == ctx.const_0())
        .and_then(|(l, _)| {
            l.if_memory()?
                .address.if_arithmetic_add_const(struct_layouts::unit_subunit_linked::<Va>())
                .filter(|x| !x.contains_undefined())
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
                let ctx = ctrl.ctx();
                if let Some(addr) =
                    check_active_hidden_cond::<E::VirtualAddress>(condition, ctx)
                {
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
            .map(move |global_ref| (global_ref, order));
        BumpVec::from_iter_in(funcs, bump)
    };
    arbiter_idle_orders.sort_unstable_by_key(|x| (x.0.func_entry, x.1));
    arbiter_idle_orders.dedup_by_key(|x| (x.0.func_entry, x.1));
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
            entry_esp: ctx.register(4),
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
    entry_esp: Operand<'e>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for OrderIssuingAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.func_results.len() == 0 {
                        if self.is_prepare_issue_order_call(ctrl) {
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
                        let esp = ctrl.resolve(ctx.register(4));
                        self.entry_esp = ctx.sub_const(esp, E::VirtualAddress::SIZE.into());
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.func_results.len() == 2 {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { to, condition } => {
                // Accept second call as tailcall if inlining
                if self.func_results.len() == 1 && condition == ctx.const_1() && self.inlining {
                    if let Some(to) = ctrl.resolve_va(to) {
                        if ctrl.resolve(ctx.register(4)) == self.entry_esp {
                            self.func_results.push(to);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> OrderIssuingAnalyzer<'a, 'e, E> {
    fn is_prepare_issue_order_call(&self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        // On x86 position_xy and target are passed by value in arg2 / 3,
        // x86_64 passes them in arg2 as struct
        let ctx = ctrl.ctx();
        if E::VirtualAddress::SIZE == 4 {
            ctrl.resolve(self.arg_cache.on_thiscall_call(0)) == self.order &&
                ctrl.resolve(self.arg_cache.on_thiscall_call(1)) == ctx.const_0() &&
                ctrl.resolve(self.arg_cache.on_thiscall_call(2)) == ctx.const_0() &&
                ctrl.resolve(self.arg_cache.on_thiscall_call(3)).if_constant() == Some(0xe4)
        } else {
            if ctrl.resolve(self.arg_cache.on_thiscall_call(0)) != self.order {
                return false;
            }
            let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
            if ctrl.read_memory(arg1, MemAccessSize::Mem32) != ctx.const_0() {
                return false;
            }
            let unit_pointer = ctx.add_const(arg1, 8);
            if ctrl.read_memory(unit_pointer, MemAccessSize::Mem64) != ctx.const_0() {
                return false;
            }
            if ctrl.resolve(self.arg_cache.on_thiscall_call(2)).if_constant() != Some(0xe4) {
                return false;
            }
            true
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
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
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
                if ctrl.resolve(condition) == ctx.const_1() {
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
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
                            .and_then(|x| {
                                x.if_mem8()?
                                    .if_arithmetic_add_const(
                                        struct_layouts::unit_player::<E::VirtualAddress>()
                                    )
                            })
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
                        if Some(dest) == self.result.create_unit {
                            ctrl.skip_operation();
                            let exec_state = ctrl.exec_state();
                            exec_state.move_to(
                                &DestOperand::Register64(scarf::operand::Register(0)),
                                ctx.custom(0),
                            );
                            return;
                        }
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
        inlining: false,
        inline_limit: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindSetUnitPlayer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    skipped_branch: E::VirtualAddress,
    inlining: bool,
    inline_limit: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSetUnitPlayer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inlining {
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                    }
                    self.inline_limit -= 1;
                }
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ctx = ctrl.ctx();
                    let tc_arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                    let player = self.arg_cache.on_entry(1);
                    let arg1_ok = tc_arg1 == player ||
                        tc_arg1.if_arithmetic_or()
                            .and_either_other(|x| x.if_arithmetic_and())
                            .filter(|&x| x == ctx.and_const(player, 0xff))
                            .is_some();
                    if arg1_ok {
                        let this = ctrl.resolve(ctx.register(1));
                        if this == self.arg_cache.on_entry(0) {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    if !self.inlining {
                        // There's possibly almost-empty single-assert function
                        // in middle, taking a1 = unit, a2 = player
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1 == self.arg_cache.on_entry(0) &&
                            ctrl.resolve(self.arg_cache.on_call(1)) == self.arg_cache.on_entry(1)
                        {
                            self.inlining = true;
                            self.inline_limit = 8;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inlining = false;
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.inlining {
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                    }
                    self.inline_limit -= 1;
                }
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

pub(crate) fn analyze_set_unit_player<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    set_unit_player: E::VirtualAddress,
    selections: Operand<'e>,
) -> SetUnitPlayerFns<E::VirtualAddress> {
    let mut result = SetUnitPlayerFns {
        remove_from_selections: None,
        remove_from_client_selection: None,
        clear_build_queue: None,
        unit_changing_player: None,
        player_gained_upgrade: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;

    let mut analysis = FuncAnalysis::new(binary, ctx, set_unit_player);
    let mut analyzer = SetUnitPlayerAnalyzer::<E> {
        arg_cache: &actx.arg_cache,
        result: &mut result,
        state: SetUnitPlayerState::RemoveFromSelections,
        inline_depth: 0,
        inline_limit: 0,
        stop_inlining: false,
        selections,
        current_entry: E::VirtualAddress::from_u64(0),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SetUnitPlayerState {
    // Found by checking for a function accessing selections
    RemoveFromSelections,
    // Found by checking for a function doing unit.sprite.flags & 0x8
    // (Or (unit.sprite.flags >> 3) & 0x1)
    RemoveFromClientSelection,
    // Found by checking for a function writing 0xe4 to unit_build_queue[0]
    ClearBuildQueue,
    // Found from call site: unit_changing_player(this = this, a1, 1)
    UnitChangingPlayer,
    // Found by following into callback at transfer_upgrades(this, callback, 0)
    // callback is expected to do just player_gained_upgrade(this = a1, a2)
    // (With check for a3 != 0 first)
    PlayerGainedUpgrade,
}

struct SetUnitPlayerAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SetUnitPlayerFns<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: SetUnitPlayerState,
    inline_depth: u8,
    // Limit depth 2 inline length to small functions
    inline_limit: u8,
    stop_inlining: bool,
    selections: Operand<'e>,
    current_entry: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SetUnitPlayerAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.inline_depth == 0 {
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let is_ok = if self.state == SetUnitPlayerState::RemoveFromSelections ||
                        self.state == SetUnitPlayerState::PlayerGainedUpgrade
                    {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        arg1 == ctx.register(1)
                    } else {
                        let this = ctrl.resolve(ctx.register(1));
                        this == ctx.register(1)
                    };
                    if is_ok {
                        if self.state == SetUnitPlayerState::UnitChangingPlayer {
                            let ok = Some(())
                                .map(|_| ctrl.resolve(self.arg_cache.on_thiscall_call(0)))
                                .filter(|&x| x == self.arg_cache.on_thiscall_entry(0))
                                .map(|_| ctrl.resolve(self.arg_cache.on_thiscall_call(1)))
                                .filter(|&x| x.if_constant() == Some(1))
                                .is_some();
                            if ok {
                                self.result.unit_changing_player = Some(dest);
                                self.state = SetUnitPlayerState::PlayerGainedUpgrade;
                            }
                        } else if self.state == SetUnitPlayerState::PlayerGainedUpgrade {
                            let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                            if arg3 == ctx.const_0() {
                                if let Some(cb) = ctrl.resolve_va(self.arg_cache.on_call(1)) {
                                    let binary = ctrl.binary();
                                    let mut analysis = FuncAnalysis::new(binary, ctx, cb);
                                    let mut analyzer = FindPlayerGainedUpgrade::<E> {
                                        arg_cache: self.arg_cache,
                                        limit: 8,
                                        result: None,
                                    };
                                    analysis.analyze(&mut analyzer);
                                    self.result.player_gained_upgrade = analyzer.result;
                                    ctrl.end_analysis();
                                }
                            }
                        } else {
                            self.inline_depth = 1;
                            self.current_entry = dest;
                            ctrl.analyze_with_current_state(self, dest);
                            self.stop_inlining = false;
                            self.inline_depth = 0;
                        }
                    }
                }
            }
        } else {
            if self.inline_depth == 2 {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        if self.inline_limit == 0{
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                    _ => (),
                }
            }
            if let Operation::Call(dest) = *op {
                if self.inline_depth == 1 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_limit = 8;
                        self.inline_depth = 2;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 1;
                        if self.stop_inlining {
                            ctrl.end_analysis();
                        }
                    }
                }
                return;
            }
            match self.state {
                SetUnitPlayerState::RemoveFromSelections => {
                    if let Operation::Move(_, val, None) = *op {
                        let val = ctrl.resolve(val);
                        if ctrl.if_mem_word(val).filter(|&x| x == self.selections).is_some() {
                            self.result.remove_from_selections = Some(self.current_entry);
                            self.stop_inlining = true;
                            self.state = SetUnitPlayerState::RemoveFromClientSelection;
                            ctrl.end_analysis();
                        }
                    }
                }
                SetUnitPlayerState::RemoveFromClientSelection => {
                    let val = match *op {
                        Operation::Move(_, val, None) => ctrl.resolve(val),
                        Operation::SetFlags(ref arith) => {
                            if arith.ty != scarf::FlagArith::And {
                                return;
                            }
                            ctx.and(ctrl.resolve(arith.left), ctrl.resolve(arith.right))
                        }
                        _ => return,
                    };
                    let ok = val.if_arithmetic_and()
                        .and_then(|(l, r)| {
                            let c = r.if_constant()?;
                            // (unit.sprite.flags >> 3) & 1 or
                            // unit.sprite.flags & 8
                            let rest = if c == 1 {
                                l.if_arithmetic_rsh_const(3)?
                            } else if c == 8 {
                                l
                            } else {
                                return None;
                            };
                            let sprite = rest.if_mem8()?
                                .if_arithmetic_add_const(0xe)?;
                            let unit = ctrl.if_mem_word(sprite)?
                                .if_arithmetic_add_const(0xc)?;
                            if unit == ctx.register(1) {
                                Some(())
                            } else {
                                None
                            }
                        })
                        .is_some();
                    if ok {
                        self.result.remove_from_client_selection = Some(self.current_entry);
                        self.stop_inlining = true;
                        self.state = SetUnitPlayerState::ClearBuildQueue;
                        ctrl.end_analysis();
                    }
                }
                SetUnitPlayerState::ClearBuildQueue => {
                    if let Operation::Move(DestOperand::Memory(mem), val, None) = *op {
                        let address = ctrl.resolve(mem.address);
                        let addr_ok = address.if_arithmetic_add_const(0x98)
                            .filter(|&x| x == ctx.register(1))
                            .is_some();
                        if addr_ok {
                            let val_u16 = ctx.and_const(ctrl.resolve(val), 0xffff);
                            if val_u16.if_constant() == Some(0xe4) {
                                self.result.clear_build_queue = Some(self.current_entry);
                                self.stop_inlining = true;
                                self.state = SetUnitPlayerState::UnitChangingPlayer;
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                SetUnitPlayerState::UnitChangingPlayer => (),
                SetUnitPlayerState::PlayerGainedUpgrade => (),
            }
        }
    }
}

struct FindPlayerGainedUpgrade<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    limit: u8,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindPlayerGainedUpgrade<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if matches!(*op, Operation::Call(..) | Operation::Jump { .. }) {
            if self.limit == 0 {
                ctrl.end_analysis();
                return;
            }
            self.limit -= 1;
        }
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let ctx = ctrl.ctx();
                let this = ctrl.resolve(ctx.register(1));
                if this == self.arg_cache.on_entry(0) {
                    if ctrl.resolve(self.arg_cache.on_thiscall_call(0)) ==
                        self.arg_cache.on_entry(1)
                    {
                        self.result = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

pub(crate) fn unit_apply_speed_upgrades<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    flingy_dat: (E::VirtualAddress, u32),
    unit_changing_player: E::VirtualAddress,
    step_iscript: E::VirtualAddress,
) -> UnitSpeed<E::VirtualAddress> {
    let mut result = UnitSpeed {
        apply_speed_upgrades: None,
        update_speed: None,
        update_speed_iscript: None,
        buffed_flingy_speed: None,
        buffed_acceleration: None,
        buffed_turn_speed: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;

    let units_dat_flingy = match binary.read_address(units_dat.0 + units_dat.1 * 0x0) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let flingy_dat_movement_type = match binary.read_address(flingy_dat.0 + flingy_dat.1 * 0x6) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let flingy_dat_speed = match binary.read_address(flingy_dat.0 + flingy_dat.1 * 0x1) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let flingy_dat_acceleration = match binary.read_address(flingy_dat.0 + flingy_dat.1 * 0x2) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let flingy_dat_turn_speed = match binary.read_address(flingy_dat.0 + flingy_dat.1 * 0x4) {
        Ok(o) => o,
        Err(_) => return result,
    };

    // Recognize apply_speed_upgrades from it starting with a switch with
    // cases 2 == 13 != 2a != 25
    // update_speed is (tail) called by apply_speed_upgrades, it starts
    // by accessing flingy_dat_movement_type[units_dat_flingy[x]]
    let mut analysis = FuncAnalysis::new(binary, ctx, unit_changing_player);
    let mut analyzer = UnitSpeedAnalyzer::<E> {
        result: &mut result,
        inline_depth: 0,
        inline_limit: 0,
        entry_esp: ctx.const_0(),
        end_caller_branch: false,
        func_entry: E::VirtualAddress::from_u64(0),
        step_iscript,
        units_dat_flingy: ctx.constant(units_dat_flingy.as_u64()),
        flingy_dat_movement_type: ctx.constant(flingy_dat_movement_type.as_u64()),
        flingy_dat_speed: ctx.constant(flingy_dat_speed.as_u64()),
        flingy_dat_acceleration: ctx.constant(flingy_dat_acceleration.as_u64()),
        flingy_dat_turn_speed: ctx.constant(flingy_dat_turn_speed.as_u64()),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct UnitSpeedAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut UnitSpeed<E::VirtualAddress>,
    inline_depth: u8,
    inline_limit: u8,
    end_caller_branch: bool,
    entry_esp: Operand<'e>,
    func_entry: E::VirtualAddress,
    step_iscript: E::VirtualAddress,
    flingy_dat_movement_type: Operand<'e>,
    flingy_dat_speed: Operand<'e>,
    flingy_dat_acceleration: Operand<'e>,
    flingy_dat_turn_speed: Operand<'e>,
    units_dat_flingy: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitSpeedAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.inline_depth == 0 {
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let this = ctrl.resolve(ctx.register(1));
                    if this == ctx.register(1) {
                        self.inline_depth = 1;
                        self.inline_limit = 8;
                        self.func_entry = dest;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        if self.result.apply_speed_upgrades.is_some() {
                            if self.result.update_speed == Some(E::VirtualAddress::from_u64(0)) {
                                // Was inlined, make None
                                self.result.update_speed = None;
                            }
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
            }
        } else {
            if self.result.apply_speed_upgrades.is_none() {
                if matches!(*op, Operation::Call(..) | Operation::Jump { .. }) {
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                    self.inline_limit -= 1;
                }
                // Checking start of function to be switch on unit_id
                if let Operation::Jump { to, condition } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        // Just assuming u8 cases
                        let switch_table = ctrl.if_mem_word(to)
                            .and_then(|x| x.if_arithmetic_add())
                            .and_then(|x| {
                                let base_table = E::VirtualAddress::from_u64(x.1.if_constant()?);
                                let small_table = x.0.if_arithmetic_mul_const(4)
                                    .and_then(|x| x.if_mem8())
                                    .and_then(|x| x.if_arithmetic_add())
                                    .and_then(|x| x.1.if_constant())
                                    .map(|x| E::VirtualAddress::from_u64(x))?;
                                Some((base_table, small_table))
                            });
                        if let Some((base_table, table)) = switch_table {
                            let binary = ctrl.binary();
                            let cases = binary.slice_from_address(table, 0x40)
                                .ok()
                                .and_then(|x| x.try_into().ok())
                                .filter(|x: &[_; 0x40]| {
                                    x[2] == x[0x13] &&
                                        x[0x2a] != x[0x2] &&
                                        x[0x25] != x[0x2] &&
                                        (4..15).all(|i| x[i] == x[3])
                                });
                            if let Some(cases) = cases {
                                self.result.apply_speed_upgrades = Some(self.func_entry);
                                // Continue analysis, update_speed gets called
                                // by apply_speed_upgrades
                                // Take case 0x36 (Devouring one)
                                let case_n = cases[0x36];
                                let address = base_table + 4 * case_n as u32;
                                if let Some(dest) = binary.read_address(address).ok() {
                                    ctrl.analyze_with_current_state(self, dest);
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            } else if self.result.update_speed.is_none() {
                if self.inline_depth == 1 {
                    let dest = match *op {
                        Operation::Call(dest) => {
                            ctrl.resolve_va(dest)
                                .filter(|_| ctrl.resolve(ctx.register(1)) == ctx.register(1))
                        }
                        _ => None,
                    };
                    if let Some(dest) = dest {
                        self.inline_depth = 2;
                        self.func_entry = dest;
                        self.entry_esp = ctx.sub_const(
                            ctrl.resolve(ctx.register(4)),
                            E::VirtualAddress::SIZE.into(),
                        );
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 1;
                        if self.result.update_speed.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
                if let Operation::Call(..) = *op {
                    ctrl.skip_call_preserve_esp();
                }
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = if_arithmetic_eq_neq(condition)
                        .map(|x| (x.0, x.1))
                        .and_either_other(|x| x.if_constant())
                        .and_then(|x| x.if_mem8())
                        .and_then(|x| x.if_arithmetic_add())
                        .and_if_either_other(|x| x == self.flingy_dat_movement_type)
                        .and_then(|x| x.if_memory())
                        .and_then(|x| x.address.if_arithmetic_add())
                        .and_if_either_other(|x| x == self.units_dat_flingy)
                        .is_some();
                    if ok {
                        // update_speed can be sometimes inlined :l
                        // If inline_depth == 1 leave it as None
                        if self.inline_depth == 2 {
                            self.result.update_speed = Some(self.func_entry);
                        } else {
                            self.result.update_speed = Some(E::VirtualAddress::from_u64(0));
                        }
                        // Continue analysis for functions called by update_speed
                    }
                }
            } else {
                if self.inline_depth == 3 {
                    self.check_update_speed_funcs(ctrl, op);
                } else {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_depth = 3;
                            self.func_entry = dest;
                            self.end_caller_branch = false;
                            ctrl.analyze_with_current_state(self, dest);
                            ctrl.skip_call_preserve_esp();
                            self.inline_depth = 2;
                            if self.end_caller_branch {
                                ctrl.end_branch();
                                if self.result.buffed_turn_speed.is_some() &&
                                    self.result.update_speed_iscript.is_some()
                                {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    } else if let Operation::Jump { to, condition } = *op {
                        // update_speed_iscript is sometimes a tail call
                        if condition == ctx.const_1() {
                            if ctrl.resolve(ctx.register(4)) == self.entry_esp {
                                if let Some(to) = ctrl.resolve_va(to) {
                                    self.inline_depth = 3;
                                    self.func_entry = to;
                                    ctrl.analyze_with_current_state(self, to);
                                    self.inline_depth = 2;
                                    ctrl.end_branch();
                                    if self.result.buffed_turn_speed.is_some() &&
                                        self.result.update_speed_iscript.is_some()
                                    {
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
}

impl<'a, 'e, E: ExecutionState<'e>> UnitSpeedAnalyzer<'a, 'e, E> {
    fn check_update_speed_funcs(
        &mut self,
        ctrl: &mut Control<'e,
        '_, '_, Self>, op: &Operation<'e>,
    ) {
        // Checking one of candidate funcs
        // flingy speed / acceleration / turn rate funcs are assumed from
        // the code reading from corresponding array
        if let Operation::Move(_, val, None) = *op {
            let val = ctrl.resolve(val);
            if let Some(mem) = val.if_memory() {
                let size = mem.size;
                let (_, r) = match mem.address.if_arithmetic_add() {
                    Some(s) => s,
                    None => return,
                };
                let result = if r == self.flingy_dat_speed && size == MemAccessSize::Mem32 {
                    &mut self.result.buffed_flingy_speed
                } else if r == self.flingy_dat_acceleration && size == MemAccessSize::Mem16 {
                    &mut self.result.buffed_acceleration
                } else if r == self.flingy_dat_turn_speed && size == MemAccessSize::Mem8 {
                    // Turn speed is last of these three handled, can end branch then.
                    self.end_caller_branch = true;
                    &mut self.result.buffed_turn_speed
                } else {
                    return;
                };
                *result = Some(self.func_entry);
                ctrl.end_analysis();
                return;
            }
        }
        if let Operation::Call(dest) = *op {
            // update_speed_iscript calls step_iscript
            if let Some(dest) = ctrl.resolve_va(dest) {
                if dest == self.step_iscript {
                    self.result.update_speed_iscript = Some(self.func_entry);
                    ctrl.end_analysis();
                    self.end_caller_branch = true;
                }
            }
        }
    }
}

pub(crate) fn analyze_step_active_unit<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_active_unit: E::VirtualAddress,
    reveal_area: E::VirtualAddress,
) -> StepActiveUnitAnalysis<'e, E::VirtualAddress> {
    let mut result = StepActiveUnitAnalysis {
        step_unit_movement: None,
        should_vision_update: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_active_unit);
    let mut analyzer = StepActiveAnalyzer::<E> {
        result: &mut result,
        reveal_area,
        custom_to_func_addr: bumpvec_with_capacity(8, &actx.bump),
        zero_compares: bumpvec_with_capacity(8, &actx.bump),
        checking_movement: false,
        check_limit: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.finish(ctx, binary);
    result
}

struct StepActiveAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepActiveUnitAnalysis<'e, E::VirtualAddress>,
    reveal_area: E::VirtualAddress,
    custom_to_func_addr: BumpVec<'acx, E::VirtualAddress>,
    zero_compares: BumpVec<'acx, (E::VirtualAddress, Operand<'e>)>,
    checking_movement: bool,
    check_limit: u8,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepActiveAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.checking_movement {
            if let Operation::Jump { condition, .. } = *op {
                let ctx = ctrl.ctx();
                let ok = ctrl.resolve(condition)
                    .if_arithmetic_gt()
                    .and_either_other(|x| x.if_constant())
                    .and_then(|x| x.if_mem8()?.if_arithmetic_add_const(0x97))
                    .filter(|&x| x == ctx.register(1))
                    .is_some();
                if ok {
                    self.result.step_unit_movement = Some(E::VirtualAddress::from_u64(0));
                    ctrl.end_analysis();
                    return;
                }
                if self.check_limit == 0 {
                    ctrl.end_analysis();
                } else {
                    self.check_limit -= 1;
                }
            }
            return;
        }
        let movement_found = self.result.step_unit_movement.is_some();
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if !movement_found {
                    self.checking_movement = true;
                    self.check_limit = 8;
                    ctrl.analyze_with_current_state(self, dest);
                    if self.result.step_unit_movement.is_some() {
                        self.result.step_unit_movement = Some(dest);
                    }
                    self.checking_movement = false;
                } else {
                    if dest == self.reveal_area {
                        let address = ctrl.address();
                        let should_vision_update = self.zero_compares.iter()
                            .filter(|x| x.0 < address)
                            .min_by_key(|x| x.0)
                            .map(|x| x.1);
                        self.result.should_vision_update = should_vision_update;
                        ctrl.end_analysis();
                    }
                    let custom = ctrl.ctx().custom(self.custom_to_func_addr.len() as u32);
                    self.custom_to_func_addr.push(dest);
                    ctrl.do_call_with_result(custom);
                }
            }
        }
        if movement_found {
            if let Operation::Jump { condition, .. } = *op {
                let condition = ctrl.resolve(condition);
                let ctx = ctrl.ctx();
                let cmp_zero = if_arithmetic_eq_neq(condition)
                    .filter(|x| x.1 == ctx.const_0())
                    .map(|x| x.0);
                if let Some(val) = cmp_zero {
                    self.zero_compares.push((ctrl.address(), val));
                }
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> StepActiveAnalyzer<'a, 'acx, 'e, E> {
    fn finish(&mut self, ctx: OperandCtx<'e>, binary: &'e BinaryFile<E::VirtualAddress>) {
        let funcs = &self.custom_to_func_addr;
        if let Some(ref mut op) = self.result.should_vision_update {
            *op = ctx.transform(*op, 8, |op| {
                if let Some(idx) = op.if_custom() {
                    let func = funcs[idx as usize];
                    crate::call_tracker::analyze_func_return::<E>(func, ctx, binary)
                } else {
                    None
                }
            });
        }
    }
}

pub(crate) fn analyze_prepare_issue_order<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    prepare_issue_order: E::VirtualAddress,
) -> PrepareIssueOrderAnalysis<'e> {
    let mut result = PrepareIssueOrderAnalysis {
        first_free_order: None,
        last_free_order: None,
        allocated_order_count: None,
        replay_bfix: None,
        replay_gcfg: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, prepare_issue_order);
    let mut analyzer = PrepareIssueOrderAnalyzer::<E> {
        result: &mut result,
        inline_depth: 0,
        inline_limit: 0,
        arg_cache: &actx.arg_cache,
        state: PrepareIssueOrderState::Bfix,
        inline_result: None,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct PrepareIssueOrderAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut PrepareIssueOrderAnalysis<'e>,
    inline_depth: u8,
    inline_limit: u8,
    arg_cache: &'a ArgCache<'e, E>,
    state: PrepareIssueOrderState,
    inline_result: Option<Operand<'e>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum PrepareIssueOrderState {
    // Search for branch on Mem8[x] & 4,
    // Inline 1 depth if arg1 == this.order, or with low limit 2 depth unconditionally.
    Bfix,
    // Search for branch on Mem8[x + 10] == 5
    // Inline once from current position
    Gcfg,
    FirstFreeOrder,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    PrepareIssueOrderAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.inline_limit != 0 {
            if let Operation::Return(..) = *op {
                let result = ctrl.resolve(ctx.register(0));
                if let Some(old) = self.inline_result {
                    if old != result {
                        self.inline_result = None;
                        ctrl.end_analysis();
                    }
                } else {
                    self.inline_result = Some(result);
                }
                return;
            }
            if matches!(*op, Operation::Call(..) | Operation::Jump { .. }) {
                self.inline_limit -= 1;
            }
            if self.inline_limit == 0 {
                ctrl.end_analysis();
                return;
            }
        }
        match self.state {
            PrepareIssueOrderState::Bfix | PrepareIssueOrderState::Gcfg => {
                let is_bfix = self.state == PrepareIssueOrderState::Bfix;
                if let Operation::Call(dest) = *op {
                    if is_bfix && self.seems_append_order(ctrl) {
                        // Wasn't able to find replay sections, skip them.
                        self.state = PrepareIssueOrderState::FirstFreeOrder;
                        self.state_order_alloc(ctrl, op);
                        return;
                    }
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let inline = match is_bfix {
                            true => self.inline_depth < 2,
                            false => self.inline_limit == 0,
                        };
                        if !inline {
                            return;
                        }

                        let mut inline_limit = 4;
                        if is_bfix && self.inline_depth == 0 {
                            let arg1 =
                                ctx.and_const(ctrl.resolve(self.arg_cache.on_call(0)), 0xff);
                            let is_this_order = arg1.if_mem8()
                                .and_then(|x| {
                                    x.if_arithmetic_add_const(
                                        struct_layouts::unit_order::<E::VirtualAddress>()
                                    )
                                })
                                .filter(|&x| x == ctx.register(1))
                                .is_some();
                            if is_this_order {
                                inline_limit = 0;
                            }
                        }
                        let old_limit = self.inline_limit;
                        self.inline_depth += 1;
                        self.inline_limit = inline_limit;
                        self.inline_result = None;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if let Some(result) = self.inline_result.take() {
                            ctrl.do_call_with_result(result);
                        }
                        if self.result.first_free_order.is_some() {
                            // May happen if we inline and then realize the replay sections
                            // can't be found.
                            ctrl.end_analysis();
                        }
                        self.inline_limit = old_limit;
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    if is_bfix {
                        let result = if_arithmetic_eq_neq(condition)
                            .and_then(|(l, r, _)| {
                                if r != ctx.const_0() {
                                    return None;
                                }
                                l.if_arithmetic_and_const(4)?.if_mem8()
                            });
                        if let Some(result) = result {
                            self.result.replay_bfix = Some(result);
                            self.state = PrepareIssueOrderState::Gcfg;
                        }
                    } else {
                        let result = if_arithmetic_eq_neq(condition)
                            .and_then(|(l, r, _)| {
                                if r.if_constant() != Some(5) {
                                    return None;
                                }
                                l.if_mem8().map(|x| ctx.sub_const(x, 0x10))
                            });
                        if let Some(result) = result {
                            self.result.replay_gcfg = Some(result);
                            self.state = PrepareIssueOrderState::FirstFreeOrder;
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    // Block moves to Mem[esp + x]; a string initialized to
                    // stack and then moving to heap, followed by string.ptr[constant] = 0
                    // caused issues.
                    let address = ctrl.resolve(mem.address);
                    let block = address.if_arithmetic_add()
                        .filter(|x| x.0 == ctx.register(4))
                        .is_some();
                    if block {
                        ctrl.skip_operation();
                    }
                    // Another check to skip replay operand analysis,
                    // if append_order call is inlined.
                    if is_bfix && mem.size == MemAccessSize::Mem8 {
                        let value = ctrl.resolve(value);
                        if let Some(val) = self.find_first_free_order(ctrl, address, value) {
                            self.result.first_free_order = Some(val);
                            self.inline_limit = 0;
                            self.state = PrepareIssueOrderState::FirstFreeOrder;
                            self.state_order_alloc(ctrl, op);
                        }
                    }
                }
            }
            PrepareIssueOrderState::FirstFreeOrder => self.state_order_alloc(ctrl, op),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> PrepareIssueOrderAnalyzer<'a, 'e, E> {
    /// Returns true if the call seems like a call to append_order(), which is
    /// done after any replay compatibility checks and needs to be inlined to
    /// for order allocation vars.
    fn seems_append_order(&self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        // append_order(this = this, a1, a2, a3, a4, 0),
        // -- In 64bit it is append_order(this = this, a1, a2, a3, 0) (I think)
        let ctx = ctrl.ctx();
        let arg_cache = self.arg_cache;
        if self.inline_depth != 0 {
            return false;
        }
        if ctrl.resolve(ctx.register(1)) != ctx.register(1) {
            return false;
        }
        if ctrl.resolve(arg_cache.on_thiscall_call(4)) != ctx.const_0() {
            return false;
        }
        if ctx.and_const(ctrl.resolve(arg_cache.on_thiscall_call(0)), 0xff) !=
            ctx.and_const(arg_cache.on_thiscall_entry(0), 0xff)
        {
            return false;
        }
        (1..3).all(|i| {
            ctrl.resolve(arg_cache.on_thiscall_call(i)) == arg_cache.on_thiscall_entry(i)
        })
    }

    fn state_order_alloc(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if self.inline_depth < 3 {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let seems_append_order = self.seems_append_order(ctrl);
                    let had_first_free_order = self.result.first_free_order.is_some();
                    let inline_limit = if seems_append_order || had_first_free_order {
                        0
                    } else if self.inline_limit == 0 {
                        16
                    } else {
                        self.inline_limit
                    };

                    let old_limit = self.inline_limit;
                    self.inline_depth += 1;
                    self.inline_limit = inline_limit;
                    self.inline_result = None;
                    ctrl.analyze_with_current_state(self, dest);
                    self.inline_depth -= 1;
                    self.inline_limit = old_limit;
                    if !had_first_free_order && self.result.first_free_order.is_some() {
                        ctrl.end_analysis();
                    }
                    if self.result.allocated_order_count.is_some() {
                        ctrl.end_analysis();
                    }
                }
            }
        } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
            let value = ctrl.resolve(value);
            if self.result.first_free_order.is_none() {
                if mem.size == MemAccessSize::Mem8 {
                    let address = ctrl.resolve(mem.address);
                    if let Some(val) = self.find_first_free_order(ctrl, address, value) {
                        self.result.first_free_order = Some(val);
                        self.inline_limit = 0;
                    }
                }
            } else if self.result.last_free_order.is_some() {
                // Check for allocated_order_count += 1
                if let Some(base) = Operand::and_masked(value).0
                    .if_arithmetic_add_const(1)
                {
                    if let Some(base_mem) = base.if_memory() {
                        if base_mem.address == ctrl.resolve(mem.address) {
                            self.result.allocated_order_count = Some(base);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        } else if let Operation::Jump { condition, .. } = *op {
            if self.result.last_free_order.is_none() {
                if let Some(first_free) = self.result.first_free_order {
                    let condition = ctrl.resolve(condition);
                    let result = if_arithmetic_eq_neq(condition)
                        .map(|x| (x.0, x.1))
                        .and_if_either_other(|x| x == first_free)
                        .filter(|&x| ctrl.if_mem_word(x).is_some());
                    if let Some(result) = result {
                        self.result.last_free_order = Some(result);
                    }
                }
            }
        }
    }

    fn find_first_free_order(
        &self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        address: Operand<'e>,
        value: Operand<'e>,
    ) -> Option<Operand<'e>> {
        let ctx = ctrl.ctx();
        if value == ctx.and_const(self.arg_cache.on_thiscall_entry(0), 0xff) {
            return address.if_arithmetic_add_const(
                struct_layouts::order_id::<E::VirtualAddress>()
            );
        }
        None
    }
}
