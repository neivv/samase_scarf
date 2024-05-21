use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, MemAccess, MemAccessSize, Operand, OperandCtx, Operation};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, entry_of_until, FunctionFinder};
use crate::add_terms::collect_arith_add_terms;
use crate::call_tracker::CallTracker;
use crate::linked_list::{self, DetectListAdd};
use crate::struct_layouts::StructLayouts;
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, MemAccessExt, OptionExt, OperandExt, single_result_assign, bumpvec_with_capacity,
    is_global, is_global_struct, if_arithmetic_eq_neq, seems_assertion_call, ExecStateExt,
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

pub(crate) struct PylonAura<'e, Va: VirtualAddress> {
    pub first_pylon: Option<Operand<'e>>,
    pub pylon_auras_visible: Option<Operand<'e>>,
    pub pylon_refresh: Option<Operand<'e>>,
    pub add_pylon_aura: Option<Va>,
}

pub(crate) struct UpdateUnitVisibility<'e, Va: VirtualAddress> {
    pub local_visions: Option<Operand<'e>>,
    pub first_free_selection_circle: Option<Operand<'e>>,
    pub last_free_selection_circle: Option<Operand<'e>>,
    pub unit_skin_map: Option<Operand<'e>>,
    pub sprite_skin_map: Option<Operand<'e>>,
    pub create_fow_sprite: Option<Va>,
    pub duplicate_sprite: Option<Va>,
}

pub(crate) struct UnitStrength<'e, Va: VirtualAddress> {
    pub unit_strength: Option<Operand<'e>>,
    pub sprite_include_in_vision_sync: Option<Operand<'e>>,
    pub team_game_teams: Option<Operand<'e>>,
    pub init_game_before_map_load_hook: Option<Va>,
    pub create_starting_units: Option<Va>,
    pub create_team_game_starting_units: Option<Va>,
}

pub(crate) struct FinishUnitPost<'e> {
    pub first_revealer: Option<Operand<'e>>,
    pub last_revealer: Option<Operand<'e>>,
    pub first_hidden_unit: Option<Operand<'e>>,
    pub last_hidden_unit: Option<Operand<'e>>,
}

pub(crate) struct HideUnit<'e, Va: VirtualAddress> {
    pub remove_references: Option<Va>,
    pub end_collision_tracking: Option<Va>,
    pub path_array: Option<Operand<'e>>,
    pub first_free_path: Option<Operand<'e>>,
    pub first_active_unit: Option<Operand<'e>>,
    pub last_active_unit: Option<Operand<'e>>,
}

pub(crate) struct KillUnit<Va: VirtualAddress> {
    pub drop_powerup: Option<Va>,
    pub remove_unit_ai: Option<Va>,
}

pub(crate) struct OrderUnitMorph<Va: VirtualAddress> {
    pub transform_unit: Option<Va>,
    pub add_ai_to_trained_unit: Option<Va>,
    pub show_finished_unit_notification: Option<Va>,
    pub switch_construction_image: Option<Va>,
    pub check_resources_for_building: Option<Va>,
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

fn check_active_hidden_cond<'e>(
    struct_layouts: StructLayouts,
    condition: Operand<'e>,
    ctx: OperandCtx<'e>,
) -> Option<Operand<'e>> {
    // It's doing something comparing to subunit ptr, should have written a comment :l
    // Mem32[unit + 70] == 0
    condition.if_arithmetic_eq()
        .filter(|&(_, r)| r == ctx.const_0())
        .and_then(|(l, _)| {
            l.if_memory()?
                .if_offset(struct_layouts.unit_subunit_linked())
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
                        let (base, offset) = mem.address();
                        if offset == self.memref_address.as_u64() {
                            self.memref_found = true;
                        } else {
                            self.memref_found = base.iter().any(|x| match x.if_constant() {
                                Some(c) => c == self.memref_address.as_u64(),
                                None => false,
                            });
                        }
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
                if let Some(addr) = check_active_hidden_cond(E::struct_layouts(), condition, ctx) {
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
        let order = ctx.mem8c(address.as_u64());
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
                        let esp = ctrl.resolve_register(4);
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
                        if ctrl.resolve_register(4) == self.entry_esp {
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
            let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
            let xy = ctx.mem_access(arg2, 0, MemAccessSize::Mem32);
            if ctrl.read_memory(&xy) != ctx.const_0() {
                return false;
            }
            let unit_pointer = ctx.mem_access(arg2, 8, MemAccessSize::Mem64);
            if ctrl.read_memory(&unit_pointer) != ctx.const_0() {
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
        let arg3_ok = arg3.if_arithmetic_mul_const(unit_size).is_some() ||
            arg3.if_constant() == Some(unit_size * 1700);
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
                                x.if_mem8_offset(E::struct_layouts().unit_player())
                            })
                            .is_some();
                        if ok {
                            self.result.create_unit = Some(dest);
                            ctrl.skip_operation();
                            ctrl.set_register(0, ctx.custom(0));
                        }
                    } else {
                        if Some(dest) == self.result.create_unit {
                            ctrl.skip_operation();
                            ctrl.set_register(0, ctx.custom(0));
                            return;
                        }
                        if ctrl.resolve_register(1).if_custom() == Some(0) {
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

/// This is actually more like init_game_analysis_for_point_after_init_units
pub(crate) fn strength<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    init_game: E::VirtualAddress,
    init_units: E::VirtualAddress,
    loaded_save: Operand<'e>,
    is_multiplayer: Operand<'e>,
) -> UnitStrength<'e, E::VirtualAddress> {
    let mut result = UnitStrength {
        unit_strength: None,
        sprite_include_in_vision_sync: None,
        team_game_teams: None,
        init_game_before_map_load_hook: None,
        create_starting_units: None,
        create_team_game_starting_units: None,
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut analyzer = StrengthAnalyzer::<E> {
        result: &mut result,
        state: StrengthState::FindInitUnits,
        init_units,
        candidate: None,
        inline_depth: 0,
        inline_limit: 0,
        loaded_save,
        is_multiplayer,
        is_multiplayer_seen: false,
        current_func: init_game,
        is_team_game_separate_func: false,
        not_team_game_branch: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_game);
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum StrengthState {
    FindInitUnits,
    UnitStrength,
    SpriteVisionSync,
    BeforeMapLoadHook,
    // Inline to find is_multiplayer != 0 && team_game_teams != 0 jumps
    TeamGameTeams,
    // Check both team_game != 0 and team_game == 0 branches for different starting unit
    // creation functions. (Should be called immediately on both branches)
    // If team_game check was not inlined but separate function, TeamGameTeams state
    // returns from it, sets result to Custom(0) and waits for branch on that before
    // switching to this state.
    StartingUnits,
}

struct StrengthAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut UnitStrength<'e, E::VirtualAddress>,
    init_units: E::VirtualAddress,
    state: StrengthState,
    candidate: Option<MemAccess<'e>>,
    inline_depth: u8,
    inline_limit: u8,
    loaded_save: Operand<'e>,
    is_multiplayer: Operand<'e>,
    is_multiplayer_seen: bool,
    current_func: E::VirtualAddress,
    // True if is_team_game() is not inlined when team_game_teams is found
    is_team_game_separate_func: bool,
    not_team_game_branch: Option<(E::VirtualAddress, E)>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StrengthAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let state = self.state;
        if self.inline_limit != 0 {
            match *op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    if self.inline_limit == 1 {
                        ctrl.end_analysis();
                        return;
                    } else {
                        self.inline_limit -= 1;
                    }
                }
                _ => (),
            }
        }
        if matches!(state, StrengthState::UnitStrength | StrengthState::SpriteVisionSync |
            StrengthState::TeamGameTeams)
        {
            // Inline a bit for these states
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.inline_depth < 2 {
                        if self.inline_depth == 0 && state == StrengthState::TeamGameTeams {
                            self.inline_limit = 15;
                        }
                        self.inline_depth += 1;
                        let current_func = self.current_func;
                        let teams_were_found = self.result.team_game_teams.is_some();
                        self.current_func = dest;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        self.current_func = current_func;
                        if self.inline_depth == 0 {
                            self.inline_limit = 0;
                        }
                        if state == StrengthState::TeamGameTeams {
                            if !teams_were_found && self.result.team_game_teams.is_some() &&
                                self.is_team_game_separate_func
                            {
                                let ctx = ctrl.ctx();
                                ctrl.do_call_with_result(ctx.custom(0));
                                return;
                            }
                        }
                        if self.state != state {
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                return;
            }
        }
        match state {
            StrengthState::FindInitUnits => {
                if let Operation::Call(dest) = *op {
                    if ctrl.resolve_va(dest) == Some(self.init_units) {
                        self.state = StrengthState::UnitStrength;
                        ctrl.clear_unchecked_branches();
                    }
                }
            }
            StrengthState::UnitStrength => {
                if let Operation::Move(DestOperand::Memory(ref mem), _, None) = *op {
                    if mem.size == MemAccessSize::Mem32 {
                        let dest = ctrl.resolve_mem(mem);
                        let ctx = ctrl.ctx();
                        if dest.is_global() {
                            if let Some(old) = self.candidate {
                                // Ground strength is guaranteed to be 0xe4 * 4 bytes after air
                                let (old_base, old_offset) = old.address();
                                let (new_base, new_offset) = dest.address();
                                if old_base == new_base &&
                                    old_offset.wrapping_add(0xe4 * 4) == new_offset
                                {
                                    self.result.unit_strength = Some(old.address_op(ctx));
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    }
                                    self.state = StrengthState::SpriteVisionSync;
                                    return;
                                }
                            }
                            self.candidate = Some(dest);
                        }
                    }
                }
            }
            StrengthState::SpriteVisionSync => {
                if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    let value = ctrl.resolve(value);
                    let ctx = ctrl.ctx();
                    if value == ctx.const_1() {
                        let mem = ctrl.resolve_mem(mem);
                        // Check for flingy_dat_sprite[units_dat_flingy[_]]
                        // flingy_dat_sprite is Mem16, units_dat_flingy is Mem8
                        let result = mem.if_add_either(ctx, |x| x.if_mem16())
                            .and_then(|x| {
                                x.0.address().0.if_arithmetic_mul_const(2)?.if_mem8()?;
                                Some(x.1)
                            });
                        if let Some(result) = result {
                            self.result.sprite_include_in_vision_sync = Some(result);
                            self.state = StrengthState::BeforeMapLoadHook;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            StrengthState::BeforeMapLoadHook => {
                // Making the hook on first save cmp instruction
                if let Operation::SetFlags(ref arith) = *op {
                    let left = ctrl.resolve(arith.left);
                    let right = ctrl.resolve(arith.right);
                    let usize_max = match E::VirtualAddress::SIZE == 4 {
                        true => u32::MAX as u64,
                        false => u64::MAX,
                    };
                    if (left == self.loaded_save && right.if_constant() == Some(usize_max))
                        || (right == self.loaded_save && left.if_constant() == Some(usize_max))
                    {
                        self.result.init_game_before_map_load_hook = Some(ctrl.address());
                        self.state = StrengthState::TeamGameTeams;
                        ctrl.clear_unchecked_branches();
                    }
                }
            }
            StrengthState::TeamGameTeams => {
                match *op {
                    Operation::Jump { condition, to } => {
                        if let Some(to) = ctrl.resolve_va(to) {
                            let condition = ctrl.resolve(condition);
                            let ctx = ctrl.ctx();
                            if let Some((x, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                                if self.result.team_game_teams.is_none() {
                                    if x == self.is_multiplayer {
                                        // Follow only multiplayer == 1 branch
                                        let dest = match eq {
                                            true => ctrl.current_instruction_end(),
                                            false => to,
                                        };
                                        ctrl.clear_unchecked_branches();
                                        ctrl.continue_at_address(dest);
                                        self.is_multiplayer_seen = true;
                                        self.is_team_game_separate_func =
                                            ctrl.branch_start() == self.current_func;
                                        return;
                                    } else if self.is_multiplayer_seen {
                                        self.result.team_game_teams = Some(x);
                                        if self.is_team_game_separate_func {
                                            ctrl.end_analysis();
                                        } else {
                                            self.on_team_game_jump(ctrl, to, eq);
                                        }
                                    }
                                } else if Operand::and_masked(x).0.if_custom() == Some(0) {
                                    self.on_team_game_jump(ctrl, to, eq);
                                }
                            }
                        }
                        self.is_multiplayer_seen = false;
                    }
                    Operation::Return(..) => {
                        self.is_multiplayer_seen = false;
                    }
                    _ => (),
                }
            }
            StrengthState::StartingUnits => {
                match *op {
                    Operation::Jump { .. } => {
                        // Should immediately call, probably got inlined
                        ctrl.end_analysis();
                    }
                    Operation::Call(dest) => {
                        // team game branch is checked first
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            if self.result.create_team_game_starting_units.is_none() {
                                self.result.create_team_game_starting_units = Some(dest);
                                ctrl.end_branch();
                                if let Some((addr, state)) = self.not_team_game_branch.take() {
                                    ctrl.add_branch_with_state(addr, state, Default::default());
                                }
                            } else {
                                self.result.create_starting_units = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                    _ => (),
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> StrengthAnalyzer<'a, 'e, E> {
    fn on_team_game_jump(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        to: E::VirtualAddress,
        jump_if_not: bool,
    ) {
        let no_branch_addr = ctrl.current_instruction_end();
        let (team_game, not) = match jump_if_not {
            true => (no_branch_addr, to),
            false => (to, no_branch_addr),
        };
        ctrl.clear_unchecked_branches();
        let state = ctrl.exec_state();
        self.not_team_game_branch = Some((not, state.clone()));
        self.state = StrengthState::StartingUnits;
        ctrl.continue_at_address(team_game);
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
                let offset = if E::VirtualAddress::SIZE == 4 { 0xc } else { 0x10 };
                let trigger_action_callback = ctx.mem_access(arg3, offset, E::WORD_SIZE);
                let func = ctrl.read_memory(&trigger_action_callback);
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
        inline_depth: 0,
        inline_limit: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindSetUnitPlayer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    skipped_branch: E::VirtualAddress,
    inline_depth: u8,
    inline_limit: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSetUnitPlayer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth != 0 {
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                    self.inline_limit -= 1;
                }
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ctx = ctrl.ctx();
                    let tc_arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                    let this = ctrl.resolve_register(1);
                    let input_unit = self.arg_cache.on_entry(0);
                    let input_player = ctx.and_const(self.arg_cache.on_entry(1), 0xff);
                    // -- If inlining, check if current func is set_unit_player --
                    // set_unit_player calls
                    //      set_unit_iscript(this = unit, a1(u8) = 14, a2(u8) =1)
                    //      or set_sprite_iscript(this = unit.sprite, a1/a2 same)
                    if self.inline_depth != 0 {
                        let this_ok = this == input_unit ||
                            ctrl.if_mem_word_offset(this, E::struct_layouts().unit_sprite())
                                .filter(|&x| x == input_unit)
                                .is_some();
                        if this_ok && ctx.and_const(tc_arg1, 0xff).if_constant() == Some(0x14) {
                            let tc_arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                            if ctx.and_const(tc_arg2, 0xff) == ctx.const_1() {
                                self.result = Some(E::VirtualAddress::from_u64(0));
                                ctrl.end_analysis();
                                return;
                            }
                        }
                    }
                    // -- Consider more inlining --
                    if self.inline_depth < 2 {
                        let mut inline = false;
                        // Inline if thiscall(unit, player)
                        // Or at depth 0 if cdecl(unit, player)
                        //      (Almost-empty single-assert function that is often not separated)
                        let arg1_ok = ctx.and_const(tc_arg1, 0xff) == input_player;
                        if arg1_ok && this == input_unit {
                            inline = true;
                        }
                        if !inline && self.inline_depth == 0 {
                            // cdecl(unit, player)
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            if arg1 == input_unit &&
                                ctx.and_const(ctrl.resolve(self.arg_cache.on_call(1)), 0xff) ==
                                    input_player
                            {
                                inline = true;
                            }
                        }
                        if inline {
                            self.inline_depth += 1;
                            let old_inline_limit = self.inline_limit;
                            self.inline_limit = 12;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_limit = old_inline_limit;
                            self.inline_depth -= 1;
                            if let Some(result) = self.result {
                                if result.as_u64() == 0 {
                                    self.result = Some(dest);
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.inline_depth != 0 {
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                    self.inline_limit -= 1;
                }
                // Assume that player isn't 0xd (trigger current player),
                // so that later player comparision isn't undef
                let condition = ctrl.resolve(condition);
                let is_player_cmp_d = if_arithmetic_eq_neq(condition)
                    .filter(|x| x.1.if_constant() == Some(0xd))
                    .filter(|x| Operand::and_masked(x.0).0 == self.arg_cache.on_entry(1))
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
        selections_mem: ctx.mem_access(selections, 0, E::WORD_SIZE),
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
    selections_mem: MemAccess<'e>,
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
                        let this = ctrl.resolve_register(1);
                        this == ctx.register(1)
                    };
                    if is_ok {
                        if self.state == SetUnitPlayerState::UnitChangingPlayer {
                            let ok = Some(())
                                .map(|_| ctrl.resolve(self.arg_cache.on_thiscall_call(0)))
                                .filter(|&x| {
                                    ctx.and_const(x, 0xff) ==
                                        ctx.and_const(self.arg_cache.on_thiscall_entry(0), 0xff)
                                })
                                .map(|_| ctrl.resolve(self.arg_cache.on_thiscall_call(1)))
                                .filter(|&x| x == ctx.const_1())
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
                        if ctrl.if_mem_word(val).filter(|&x| x == &self.selections_mem).is_some() {
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
                            let sprite =
                                rest.if_mem8_offset(E::struct_layouts().sprite_flags())?;
                            let unit_sprite = E::struct_layouts().unit_sprite();
                            let unit = ctrl.if_mem_word_offset(sprite, unit_sprite)?;
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
                    if let Operation::Move(DestOperand::Memory(ref mem), val, None) = *op {
                        let (base, offset) = ctrl.resolve_mem(mem).address();
                        let addr_ok = base == ctx.register(1) &&
                            offset == E::struct_layouts().unit_build_queue();
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
                let this = ctrl.resolve_register(1);
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
        units_dat_flingy: units_dat_flingy,
        flingy_dat_movement_type: flingy_dat_movement_type,
        flingy_dat_speed: flingy_dat_speed,
        flingy_dat_acceleration: flingy_dat_acceleration,
        flingy_dat_turn_speed: flingy_dat_turn_speed,
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
    flingy_dat_movement_type: E::VirtualAddress,
    flingy_dat_speed: E::VirtualAddress,
    flingy_dat_acceleration: E::VirtualAddress,
    flingy_dat_turn_speed: E::VirtualAddress,
    units_dat_flingy: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitSpeedAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.inline_depth == 0 {
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let this = ctrl.resolve_register(1);
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
                        let exec = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                            let binary = ctrl.binary();
                            let cases_ok = Some(()).and_then(|()| {
                                let case_2 = switch.branch(binary, ctx, 0x2)?;
                                let case_3 = switch.branch(binary, ctx, 0x3)?;
                                let ok = case_2 == switch.branch(binary, ctx, 0x13)? &&
                                    case_2 != switch.branch(binary, ctx, 0x25)? &&
                                    case_2 != switch.branch(binary, ctx, 0x2a)? &&
                                    (4..15)
                                        .all(|i| switch.branch(binary, ctx, i) == Some(case_3));
                                if ok {
                                    Some(())
                                } else {
                                    None
                                }
                            }).is_some();
                            if cases_ok {
                                self.result.apply_speed_upgrades = Some(self.func_entry);
                                // Continue analysis, update_speed gets called
                                // by apply_speed_upgrades
                                // Take case 0x36 (Devouring one)
                                if let Some(dest) = switch.branch(binary, ctx, 0x36) {
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
                                .filter(|_| ctrl.resolve_register(1) == ctx.register(1))
                        }
                        _ => None,
                    };
                    if let Some(dest) = dest {
                        self.inline_depth = 2;
                        self.func_entry = dest;
                        self.entry_esp = ctrl.get_new_esp_for_call();
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
                    // 32bit seems to compile (x == 0 || x == 1), 64bit as (x < 2)
                    let ok = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1.if_constant().is_some())
                        .map(|x| x.0)
                        .or_else(|| {
                            condition.if_arithmetic_gt()
                                .filter(|x| x.0.if_constant() == Some(2))
                                .map(|x| x.1)
                        })
                        .and_then(|x| x.if_mem8_offset(self.flingy_dat_movement_type.as_u64()))
                        .and_then(|x| x.if_memory())
                        .and_then(|x| x.if_offset(self.units_dat_flingy.as_u64()))
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
                            if ctrl.resolve_register(4) == self.entry_esp {
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
                let (_, offset) = mem.address();
                let offset = E::VirtualAddress::from_u64(offset);
                let result = if offset == self.flingy_dat_speed && size == MemAccessSize::Mem32 {
                    &mut self.result.buffed_flingy_speed
                } else if offset == self.flingy_dat_acceleration && size == MemAccessSize::Mem16 {
                    &mut self.result.buffed_acceleration
                } else if offset == self.flingy_dat_turn_speed && size == MemAccessSize::Mem8 {
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
                    .and_then(|x| x.if_mem8_offset(E::struct_layouts().unit_movement_state()))
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
                let cmp_zero = condition.if_arithmetic_eq_neq_zero(ctx)
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
                let result = ctrl.resolve_register(0);
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
                            let is_this_order =
                                arg1.if_mem8_offset(E::struct_layouts().unit_order())
                                    == Some(ctx.register(1));
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
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if is_bfix {
                        // Skip past any arg1 == constant comparisions
                        // to avoid early append_order for SCV build
                        let skip = if_arithmetic_eq_neq(condition)
                            .filter(|x| x.1.if_constant().is_some())
                            .filter(|x| {
                                x.0 == ctx.and_const(self.arg_cache.on_thiscall_entry(0), 0xff)
                            })
                            .map(|x| x.2);
                        if let Some(jump_if_constant) = skip {
                            // Go to the non-constant branch
                            let to = match jump_if_constant {
                                false => ctrl.resolve_va(to),
                                true => Some(ctrl.current_instruction_end()),
                            };
                            ctrl.end_branch();
                            if let Some(to) = to {
                                ctrl.add_branch_with_current_state(to);
                            }
                            return;
                        }

                        let result = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|(l, _)| l.if_arithmetic_and_const(4)?.if_mem8());
                        if let Some(result) = result {
                            self.result.replay_bfix = Some(result.address_op(ctx));
                            self.state = PrepareIssueOrderState::Gcfg;
                        }
                    } else {
                        let result = if_arithmetic_eq_neq(condition)
                            .and_then(|(l, r, _)| {
                                if r.if_constant() != Some(5) {
                                    return None;
                                }
                                l.if_mem8().map(|x| ctx.mem_sub_const_op(x, 0x10))
                            });
                        if let Some(result) = result {
                            self.result.replay_gcfg = Some(result);
                            self.state = PrepareIssueOrderState::FirstFreeOrder;
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    // Block moves to Mem[esp + x]; a string initialized to
                    // stack and then moving to heap, followed by string.ptr[constant] = 0
                    // caused issues by overwriting stack args.
                    let mem = ctrl.resolve_mem(mem);
                    let (base, offset) = mem.address();
                    if base == ctx.register(4) && offset as i32 > 0 {
                        ctrl.skip_operation();
                    }
                    // Another check to skip replay operand analysis,
                    // if append_order call is inlined.
                    if is_bfix && mem.size == MemAccessSize::Mem8 {
                        let value = ctrl.resolve(value);
                        if let Some(val) = self.find_first_free_order(ctrl, mem, value) {
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
        // -- In 64bit it is append_order(this = this, a1, local copy of a2 (pos+target), a3, 0)
        let ctx = ctrl.ctx();
        let arg_cache = self.arg_cache;
        if self.inline_depth != 0 {
            return false;
        }
        if ctrl.resolve_register(1) != ctx.register(1) {
            return false;
        }
        if ctx.and_const(ctrl.resolve(arg_cache.on_thiscall_call(0)), 0xff) !=
            ctx.and_const(arg_cache.on_thiscall_entry(0), 0xff)
        {
            return false;
        }
        if E::VirtualAddress::SIZE == 4 {
            if ctrl.resolve(arg_cache.on_thiscall_call(4)) != ctx.const_0() {
                return false;
            }
            (1..3).all(|i| {
                ctrl.resolve(arg_cache.on_thiscall_call(i)) == arg_cache.on_thiscall_entry(i)
            })
        } else {
            if ctrl.resolve(arg_cache.on_thiscall_call(3)) != ctx.const_0() {
                return false;
            }
            let arg2 = ctrl.resolve(arg_cache.on_thiscall_call(1));
            let arg2_mem = ctx.mem_access(arg2, 0, MemAccessSize::Mem64);
            let ok = ctrl.read_memory(&arg2_mem) ==
                ctx.mem64(arg_cache.on_thiscall_entry(1), 0) &&
                ctrl.read_memory(&ctx.mem_access(arg2, 8, MemAccessSize::Mem64)) ==
                    ctx.mem64(arg_cache.on_thiscall_entry(1), 8);
            if !ok {
                return false;
            }
            ctx.and_const(ctrl.resolve(arg_cache.on_thiscall_call(2)), 0xffff) ==
                ctx.and_const(arg_cache.on_thiscall_entry(2), 0xffff)
        }
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
                    let mem = ctrl.resolve_mem(mem);
                    if let Some(val) = self.find_first_free_order(ctrl, mem, value) {
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
                        if base_mem == &ctrl.resolve_mem(mem) {
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
        address: MemAccess<'e>,
        value: Operand<'e>,
    ) -> Option<Operand<'e>> {
        let ctx = ctrl.ctx();
        if value == ctx.and_const(self.arg_cache.on_thiscall_entry(0), 0xff) {
            return address.if_offset(E::struct_layouts().order_id());
        }
        None
    }
}

pub(crate) fn pylon_aura<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_pylon_init: E::VirtualAddress,
) -> PylonAura<'e, E::VirtualAddress> {
    let mut result = PylonAura {
        first_pylon: None,
        add_pylon_aura: None,
        pylon_auras_visible: None,
        pylon_refresh: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, order_pylon_init);
    let mut analyzer = PylonInitAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: PylonInitState::FirstPylon,
        inline_depth: 0,
        limit: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct PylonInitAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut PylonAura<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: PylonInitState,
    inline_depth: u8,
    limit: u8,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum PylonInitState {
    // Search for this.next_pylon = first_pylon
    FirstPylon,
    // Should be first call immediately after, verify from create_sprite(141, ...)
    AddPylonAura,
    AddPylonAuraVerify,
    // Assign 1 to a global in add_pylon_aura
    PylonAurasVisible,
    // Back to depth 0, assign 1 right after add_pylon_aura
    PylonRefresh,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for PylonInitAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            PylonInitState::FirstPylon => {
                if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    let mem = ctrl.resolve_mem(mem);
                    let offset = E::struct_layouts().unit_next_pylon();
                    if mem.address() == (ctx.register(1), offset) {
                        self.result.first_pylon = Some(ctrl.resolve(value));
                        self.state = PylonInitState::AddPylonAura;
                    }
                }
            }
            PylonInitState::AddPylonAura => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_depth = 1;
                        self.state = PylonInitState::AddPylonAuraVerify;
                        self.limit = 2;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        if self.state != PylonInitState::AddPylonAuraVerify {
                            self.result.add_pylon_aura = Some(dest);
                            ctrl.clear_all_branches();
                            if self.state == PylonInitState::PylonAurasVisible {
                                self.state = PylonInitState::PylonRefresh;
                            }
                        } else {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            PylonInitState::AddPylonAuraVerify => {
                if let Operation::Call(_) = *op {
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    if arg1.if_constant() == Some(0x141) {
                        self.state = PylonInitState::PylonAurasVisible;
                        ctrl.clear_unchecked_branches();
                    } else {
                        if self.limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.limit -= 1;
                        }
                    }
                }
            }
            PylonInitState::PylonAurasVisible | PylonInitState::PylonRefresh => {
                if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if ctrl.resolve(value) == ctx.const_1() {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            let dest = ctx.memory(&mem);
                            if self.state == PylonInitState::PylonAurasVisible {
                                self.result.pylon_auras_visible = Some(dest);
                                self.state = PylonInitState::PylonRefresh;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            } else {
                                self.result.pylon_refresh = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if seems_assertion_call(ctrl, self.arg_cache) {
                        ctrl.end_branch();
                        return;
                    }
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        // Inline once if searching pylon_auras_visible
                        // (inline_depth == 1 already from AddPylonAuraVerify)
                        if self.state == PylonInitState::PylonAurasVisible {
                            if self.inline_depth < 2 {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != PylonInitState::PylonAurasVisible {
                                    if self.inline_depth != 0 {
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

pub(crate) fn update_unit_visibility_analysis<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    update_unit_visibility: E::VirtualAddress,
    unit_array: Operand<'e>,
    sprite_array: Operand<'e>,
    first_free_fow_sprite: Operand<'e>,
) -> UpdateUnitVisibility<'e, E::VirtualAddress> {
    let mut result = UpdateUnitVisibility {
        local_visions: None,
        first_free_selection_circle: None,
        last_free_selection_circle: None,
        unit_skin_map: None,
        sprite_skin_map: None,
        create_fow_sprite: None,
        duplicate_sprite: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, update_unit_visibility);
    let mut analyzer = UpdateUnitVisibilityAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        bump: &actx.bump,
        state: UnitVisibilityState::LocalVisions,
        inline_depth: 0,
        selection_circle_image: ctx.const_0(),
        duplicated_sprite: ctx.const_0(),
        call_tracker: CallTracker::with_capacity(actx, 0, 32),
        unit_array,
        sprite_array,
        first_free_fow_sprite,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct UpdateUnitVisibilityAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut UpdateUnitVisibility<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    bump: &'acx Bump,
    state: UnitVisibilityState,
    inline_depth: u8,
    selection_circle_image: Operand<'e>,
    duplicated_sprite: Operand<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
    unit_array: Operand<'e>,
    sprite_array: Operand<'e>,
    first_free_fow_sprite: Operand<'e>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum UnitVisibilityState {
    // Search for this.sprite.visibility_mask & global
    // Inline to unit_set_sprite_visibility_mask(this.subunit, this.sprite.visibility_mask)
    // and sprite_set_visibility_mask(this.subunit.sprite, this.sprite.visibility_mask)
    LocalVisions,
    // Find comparision of image.image_id <= 0x23a
    // Inline to sprite_remove_selection_circle(this.sprite)
    SelectionCircleImage,
    SelectionCircles,
    // Inline to create_fow_sprite(unit_uid, this.unit_id, this.sprite)
    // Find store to first_fow_sprite.sprite
    FindDuplicatedSprite,
    UnitSkinMap,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    UpdateUnitVisibilityAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            UnitVisibilityState::LocalVisions => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 2 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let arg1 = ctx.and_const(
                                ctrl.resolve(self.arg_cache.on_thiscall_call(0)),
                                0xff,
                            );
                            if is_this_sprite_vismask(E::struct_layouts(), ctx, arg1) {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != UnitVisibilityState::LocalVisions {
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    } else {
                                        ctrl.clear_unchecked_branches();
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Move(_, value, None) = *op {
                    if let Some((l, r)) = value.if_arithmetic_and() {
                        let l = ctrl.resolve(l);
                        let r = ctrl.resolve(r);
                        let other = Some((l, r))
                            .and_if_either_other(|x| {
                                is_this_sprite_vismask(E::struct_layouts(), ctx, x)
                            });
                        if let Some(other) = other {
                            if is_global(other) && other.if_constant().is_none() {
                                self.result.local_visions = Some(other);
                                self.state = UnitVisibilityState::SelectionCircleImage;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                } else {
                                    ctrl.clear_unchecked_branches();
                                }
                            }
                        }
                    }
                }
            }
            UnitVisibilityState::SelectionCircleImage => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 1 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            let ok = E::struct_layouts().if_unit_sprite(this)
                                .filter(|&x| x == ctx.register(1))
                                .is_some();
                            if ok {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    // Check for image_id < 0x23b as alone or combined with image_id >= 0x231
                    let image = condition.if_arithmetic_gt()
                        .and_then(|x| {
                            let lhs = x.0.if_constant()?;
                            if lhs == 0x23b {
                                Some(x.1)
                            } else if lhs == 0xa {
                                x.1.if_arithmetic_sub_const(0x231)
                            } else {
                                None
                            }
                        })
                        .and_then(|x| x.if_mem16_offset(E::struct_layouts().image_id()));
                    if let Some(image) = image {
                        if let Some(to) = ctrl.resolve_va(to) {
                            self.selection_circle_image = image;
                            self.state = UnitVisibilityState::SelectionCircles;
                            ctrl.clear_unchecked_branches();
                            ctrl.end_branch();
                            ctrl.add_branch_with_current_state(to);
                        }
                    }
                }
            }
            UnitVisibilityState::SelectionCircles => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 3 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            if this == self.selection_circle_image {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != UnitVisibilityState::SelectionCircles {
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    let value = ctrl.resolve(value);
                    let dest = ctrl.resolve_mem(mem);
                    let (dest_base, dest_off) = dest.address();
                    if value == self.selection_circle_image && dest.is_global() {
                        if dest_off == E::VirtualAddress::SIZE.into() {
                            // Move image = [free_head].next
                            let result = dest_base;
                            if let Some(head) = self.result.first_free_selection_circle {
                                if head == result {
                                    // Ok, guessed correctly from head/tail move below
                                } else {
                                    if Some(result) == self.result.last_free_selection_circle {
                                        // Guessed wrong, swap
                                        std::mem::swap(
                                            &mut self.result.first_free_selection_circle,
                                            &mut self.result.last_free_selection_circle,
                                        );
                                    }
                                }
                            } else {
                                self.result.first_free_selection_circle = Some(result);
                            }
                            if self.result.last_free_selection_circle.is_some() {
                                self.state = UnitVisibilityState::FindDuplicatedSprite;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                                return;
                            }
                        } else {
                            let ok =
                                ctrl.if_mem_word_offset(dest_base, E::VirtualAddress::SIZE.into())
                                .is_none();
                            if ok {
                                // May be a move to free list head or tail, assume tail
                                // unless it has been used already
                                let op = ctrl.mem_word(dest_base, dest_off);
                                if let Some(tail) = self.result.last_free_selection_circle {
                                    if tail != op {
                                        self.result.first_free_selection_circle = Some(op);
                                    }
                                } else {
                                    self.result.last_free_selection_circle = Some(op);
                                    if self.result.first_free_selection_circle.is_some() {
                                        self.state = UnitVisibilityState::FindDuplicatedSprite;
                                        if self.inline_depth != 0 {
                                            ctrl.end_analysis();
                                        }
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            UnitVisibilityState::FindDuplicatedSprite => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.inline_depth < 1 {
                            // Check inline to create_fow_sprite
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                            let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                            let ok =
                                self.is_uid(arg1, self.unit_array)
                                    .filter(|&x| x == ctx.register(1))
                                    .is_some() &&
                                ctx.and_const(arg2, 0xffff)
                                    .if_mem16_offset(E::struct_layouts().unit_id())
                                    .filter(|&x| x == ctx.register(1))
                                    .is_some() &&
                                E::struct_layouts().if_unit_sprite(arg3)
                                    .filter(|&x| x == ctx.register(1))
                                    .is_some();
                            if ok {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != UnitVisibilityState::FindDuplicatedSprite {
                                    self.result.create_fow_sprite = Some(dest);
                                    ctrl.end_analysis();
                                }
                                return;
                            }
                        }
                        if E::VirtualAddress::SIZE == 4 {
                            let esp = ctrl.resolve_register(4);
                            self.call_tracker.add_call_resolve(ctrl, dest);
                            // Assume no stack offset
                            ctrl.set_register(4, esp);
                        } else {
                            self.call_tracker.add_call_resolve(ctrl, dest);
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    // Check for first_free_fow_sprite.sprite = duplicated
                    let mem = ctrl.resolve_mem(mem);
                    let (base, offset) = mem.address();
                    if base == self.first_free_fow_sprite &&
                        offset == E::struct_layouts().unit_sprite()
                    {
                        let value = ctrl.resolve(value);
                        if value.if_constant().is_none() {
                            if let Some(custom) = value.if_custom() {
                                // Value was returned from a complex call,
                                // it should be duplicate_sprite_call then
                                self.result.duplicate_sprite =
                                    self.call_tracker.custom_id_to_func(custom);
                            }
                            self.state = UnitVisibilityState::UnitSkinMap;
                            self.duplicated_sprite = value;
                        }
                    }
                }
            }
            UnitVisibilityState::UnitSkinMap => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let this = ctrl.resolve_register(1);
                        let tc_arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if is_global(this) {
                            if self.result.unit_skin_map.is_none() {
                                if self.is_uid(tc_arg1, self.unit_array) ==
                                    Some(ctx.register(1))
                                {
                                    self.result.unit_skin_map = Some(this);
                                }
                            } else {
                                if self.is_uid(tc_arg1, self.sprite_array) ==
                                    Some(self.duplicated_sprite)
                                {
                                    self.result.sprite_skin_map = Some(this);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                        // Assume nonzero if arg1 is this or this->sprite,
                        // for unit_uid() and sprite_uid()
                        let assume_arg1_nonzero = arg1 == ctx.register(1) ||
                            arg1 == self.duplicated_sprite;
                        let constraint = if assume_arg1_nonzero {
                            ctx.neq_const(self.arg_cache.on_entry(0), 0)
                        } else {
                            ctx.const_1()
                        };
                        if E::VirtualAddress::SIZE == 4 {
                            let esp = ctrl.resolve_register(4);
                            self.call_tracker.add_call_resolve_with_constraint(
                                ctrl,
                                dest,
                                constraint,
                            );
                            // Assume no stack offset
                            ctrl.set_register(4, esp);
                        } else {
                            self.call_tracker.add_call_resolve_with_constraint(
                                ctrl,
                                dest,
                                constraint,
                            );
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> UpdateUnitVisibilityAnalyzer<'a, 'acx, 'e, E> {
    fn is_uid(&self, op: Operand<'e>, array: Operand<'e>) -> Option<Operand<'e>> {
        // Accept (((this - units_array) & opt_mask) / constant) + 1
        // And ((((this - units_array) & opt_mask) * constant) >> constant) + 1
        Operand::and_masked(op).0
            .if_arithmetic_add_const(1)
            .and_then(|x| if_division_by_constant(x, self.bump))
            .and_then(|x| {
                let (l, r) = Operand::and_masked(x).0.if_arithmetic_sub()?;
                if r != array {
                    None
                } else {
                    Some(l)
                }
            })
    }
}

fn if_division_by_constant<'e, 'acx>(op: Operand<'e>, bump: &'acx Bump) -> Option<Operand<'e>> {
    use scarf::ArithOpType;

    // Not complete, but catches most constant division forms that
    // get generated
    // (Also some of it may break if scarf gets signed multiplication fixed)
    op.if_arithmetic(ArithOpType::Div)
        .filter(|x| x.1.if_constant().is_some())
        .map(|x| x.0)
        .or_else(|| {
            let (shifted, c) = op.if_arithmetic(ArithOpType::Rsh)?;
            c.if_constant()?;
            let (inner, c) = shifted.if_arithmetic(ArithOpType::Mul)
                .or_else(|| shifted.if_arithmetic(ArithOpType::MulHigh))?;
            c.if_constant()?;
            Some(inner)
        })
        .or_else(|| {
            let mut terms = collect_arith_add_terms(op, bump);
            terms.remove_get(|x, _| {
                Some(x).and_then(|x| {
                    let (_, r) = x.if_arithmetic(ArithOpType::Rsh)?;
                    r.if_constant().filter(|&c| c == 0x3f || c == 0x1f)
                }).is_some()
            })?;
            let rest = terms.get_if_single()?;
            let (shifted, c) = rest.if_arithmetic(ArithOpType::Rsh)?;
            c.if_constant()?;
            let mut terms = collect_arith_add_terms(shifted, bump);
            let mut result = None;
            terms.remove_get(|x, neg| {
                !neg && Some(()).and_then(|()| {
                    let (inner, c) = x.if_arithmetic(ArithOpType::Mul)
                        .or_else(|| x.if_arithmetic(ArithOpType::MulHigh))?;
                    c.if_constant()?;
                    result = Some(inner);
                    Some(())
                }).is_some()
            });
            result
        })
}

fn is_this_sprite_vismask<'e>(
    struct_layouts: StructLayouts,
    ctx: OperandCtx<'e>,
    op: Operand<'e>,
) -> bool {
    Some(()).and_then(|()| {
        let sprite = op.if_mem8_offset(struct_layouts.sprite_visibility_mask())?;
        let (unit, offset) = sprite
            .if_memory()
            .filter(|x| x.size == struct_layouts.mem_access_size())?
            .address();
        if offset != struct_layouts.unit_sprite() {
            return None;
        }
        if unit != ctx.register(1) {
            None
        } else {
            Some(())
        }
    }).is_some()
}

pub(crate) fn analyze_finish_unit_post<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    finish_unit_post: E::VirtualAddress,
) -> FinishUnitPost<'e> {
    let mut result = FinishUnitPost {
        first_revealer: None,
        last_revealer: None,
        first_hidden_unit: None,
        last_hidden_unit: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, finish_unit_post);
    let mut analyzer = FinishUnitPostAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: FinishUnitPostState::RemoveFromHiddenUnits,
        inline_depth: 0,
        inline_limit: 0,
        list_add_tracker: DetectListAdd::new(Some(ctx.register(1))),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct FinishUnitPostAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut FinishUnitPost<'e>,
    arg_cache: &'a ArgCache<'e, E>,
    state: FinishUnitPostState,
    inline_depth: u8,
    inline_limit: u8,
    list_add_tracker: DetectListAdd<'e, E>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum FinishUnitPostState {
    RemoveFromHiddenUnits,
    AddToRevealers,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FinishUnitPostAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.inline_limit != 0 {
            match *op {
                Operation::Call(..) => {
                    ctrl.end_branch();
                    return;
                }
                Operation::Jump { .. } => {
                    self.inline_limit -= 1;
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                }
                _ => (),
            }
        }
        if self.inline_depth == 0 {
            // Inline if this == this, and a1 and a2 are globals
            if let Operation::Call(dest) = *op {
                let inline = ctrl.resolve_register(1) == ctx.register(1) &&
                    is_global_struct::<E>(ctrl.resolve(self.arg_cache.on_thiscall_call(0))) &&
                    is_global_struct::<E>(ctrl.resolve(self.arg_cache.on_thiscall_call(1)));
                if inline {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_depth = 1;
                        self.inline_limit = 16;
                        let old_state = self.state;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        self.inline_limit = 0;
                        if old_state == FinishUnitPostState::RemoveFromHiddenUnits {
                            if self.state == old_state {
                                // Clear partially found result if any
                                self.result.first_hidden_unit = None;
                                self.result.last_hidden_unit = None;
                            } else {
                                ctrl.clear_unchecked_branches();
                            }
                        }
                        if self.result.last_revealer.is_some() {
                            ctrl.end_analysis();
                        }
                        return;
                    }
                }
            }
        }
        match self.state {
            FinishUnitPostState::RemoveFromHiddenUnits => {
                let result = linked_list::detect_list_remove(ctrl, op, ctx.register(1));
                if let Some((val, offset)) = result {
                    let result = &mut self.result;
                    if offset == 0 {
                        // last_hidden = this.prev
                        result.last_hidden_unit = Some(val);
                    } else {
                        // first_hidden = this.next
                        result.first_hidden_unit = Some(val);
                    }
                    if result.last_hidden_unit.is_some() && result.first_hidden_unit.is_some() {
                        self.state = FinishUnitPostState::AddToRevealers;
                        if self.inline_depth != 0 {
                            ctrl.end_analysis();
                        } else {
                            ctrl.clear_unchecked_branches();
                        }
                    }
                }
            }
            FinishUnitPostState::AddToRevealers => {
                self.list_add_tracker.operation(ctrl, op);
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.state == FinishUnitPostState::AddToRevealers {
            self.list_add_tracker.branch_start(ctrl);
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.state == FinishUnitPostState::AddToRevealers {
            let ctx = ctrl.ctx();
            if let Some(result) = self.list_add_tracker.result(ctx) {
                self.result.first_revealer = Some(result.head);
                self.result.last_revealer = Some(result.tail);
                ctrl.end_analysis();
            }
        }
    }
}

pub(crate) fn analyze_hide_unit<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    hide_unit: E::VirtualAddress,
) -> HideUnit<'e, E::VirtualAddress> {
    let mut result = HideUnit {
        remove_references: None,
        end_collision_tracking: None,
        path_array: None,
        first_free_path: None,
        first_active_unit: None,
        last_active_unit: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, hide_unit);
    let mut analyzer = HideUnitAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: HideUnitState::IsHiddenJump,
        inline_depth: 0,
        inline_limit: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct HideUnitAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut HideUnit<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: HideUnitState,
    inline_depth: u8,
    inline_limit: u8,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum HideUnitState {
    /// Find is_hidden() jump, follow false branch
    IsHiddenJump,
    /// find remove_references(this, 0)
    RemoveReferences,
    EndCollisionTracking,
    /// Should start with this.unit_search_index < 0 check
    VerifyEndCollisionTracking,
    /// Inline up to 3 times, with either this = this or arg1 = this.path
    /// Find Mem32[this.path] = (first_free_path - path_array) + 1
    Paths,
    /// Find removal from active unit list (Inline once with this = this)
    ActiveUnits,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for HideUnitAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            HideUnitState::IsHiddenJump => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((val, _)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        // undefined for uninlined call
                        if Operand::and_masked(val).0.is_undefined() ||
                            val.if_arithmetic_and().is_some()
                        {
                            if let Some(to) = ctrl.resolve_va(to) {
                                ctrl.assign_to_unresolved_on_eq_branch(condition, to);
                                self.state = HideUnitState::RemoveReferences;
                            }
                        }
                    }
                }
            }
            HideUnitState::RemoveReferences => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = ctrl.resolve_register(1) == ctx.register(1) &&
                            ctx.and_const(
                                ctrl.resolve(self.arg_cache.on_thiscall_call(0)),
                                0xff,
                            ) == ctx.const_0();
                        if ok {
                            self.result.remove_references = Some(dest);
                            self.state = HideUnitState::EndCollisionTracking;
                        }
                    }
                }
            }
            HideUnitState::EndCollisionTracking => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if ctrl.resolve_register(1) == ctx.register(1) {
                            self.state = HideUnitState::VerifyEndCollisionTracking;
                            self.inline_limit = 5;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.end_collision_tracking.is_some() {
                                self.result.end_collision_tracking = Some(dest);
                                self.state = HideUnitState::Paths;
                            } else {
                                self.state = HideUnitState::EndCollisionTracking;
                            }
                        }
                    }
                }
            }
            HideUnitState::VerifyEndCollisionTracking => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 2 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let inline = ctrl.resolve_register(1) == ctx.register(1);
                            if inline {
                                self.inline_depth += 1;
                                let old_limit = self.inline_limit;
                                self.inline_limit = 5;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_limit = old_limit;
                                self.inline_depth -= 1;
                                if self.result.end_collision_tracking.is_some() {
                                    ctrl.end_analysis();
                                } else {
                                    ctrl.end_branch();
                                }
                            }
                        }
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    // Scarf canonicalizes int(Mem32[x] < 0) to `Mem8[x + 3] >> 7`
                    // or `(Mem8[x + 3] & 80) == 0` .__.
                    let offset = E::struct_layouts().unit_search_indices();
                    let ok = condition.if_arithmetic_rsh_const(7)
                        .or_else(|| {
                            condition.if_arithmetic_eq_const(0)
                                .and_then(|x| x.if_arithmetic_and_const(0x80))
                        })
                        .and_then(|x| x.if_mem8_offset(offset + 3)) == Some(ctx.register(1));
                    if ok {
                        self.result.end_collision_tracking = Some(E::VirtualAddress::from_u64(0));
                        ctrl.end_analysis();
                    } else {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                }
            }
            HideUnitState::Paths => {
                let path_offset = E::struct_layouts().unit_path();
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 4 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let inline = ctrl.resolve_register(1) == ctx.register(1) || {
                                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                                ctrl.if_mem_word_offset(arg1, path_offset) ==
                                    Some(ctx.register(1))
                            };
                            if inline {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != HideUnitState::Paths && self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if mem.size == MemAccessSize::Mem32 && mem.address().0 != ctx.register(4) {
                        let mem = ctrl.resolve_mem(mem);
                        let (base, offset) = mem.address();
                        let is_path_field0 = offset == 0 &&
                            ctrl.if_mem_word_offset(base, path_offset) == Some(ctx.register(1));
                        if is_path_field0 {
                            let value = ctrl.resolve(value);
                            // The value is int(first_free_path - path_array) >> 7 + 1
                            // Signed right shift is pain to match against
                            // But on 64bit it is just normal right shift;
                            // (intptr_t & ffff_ffff) probably
                            let result = Operand::and_masked(value).0
                                .if_arithmetic_add_const(1)
                                .and_then(|x| {
                                    x.if_arithmetic_or()
                                        .and_either(|x| {
                                            Operand::and_masked(x).0.if_arithmetic_rsh_const(7)?
                                                .if_arithmetic_sub()
                                        })
                                        .map(|x| x.0)
                                        .or_else(|| {
                                            x.if_arithmetic_rsh_const(7)?.if_arithmetic_sub()
                                        })
                                });
                            if let Some((free, array)) = result {
                                self.result.first_free_path = Some(free);
                                self.result.path_array = Some(array);
                                self.state = HideUnitState::ActiveUnits;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            HideUnitState::ActiveUnits => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < 2 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let inline = ctrl.resolve_register(1) == ctx.register(1);
                            if inline {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.first_active_unit.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                } else {
                    let result = linked_list::detect_list_remove(ctrl, op, ctx.register(1));
                    if let Some((val, offset)) = result {
                        let result = &mut self.result;
                        if offset == 0 {
                            result.last_active_unit = Some(val);
                        } else {
                            result.first_active_unit = Some(val);
                        }
                        if result.last_active_unit.is_some() &&
                            result.first_active_unit.is_some()
                        {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_kill_unit<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    kill_unit: E::VirtualAddress,
) -> KillUnit<E::VirtualAddress> {
    let mut result = KillUnit {
        drop_powerup: None,
        remove_unit_ai: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, kill_unit);
    let mut analyzer = KillUnitAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: KillUnitState::DropPowerup,
        inline_limit: 0,
        call_tracker: CallTracker::with_capacity(actx, 0, 16),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct KillUnitAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut KillUnit<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: KillUnitState,
    inline_limit: u8,
    call_tracker: CallTracker<'acx, 'e, E>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum KillUnitState {
    /// Find drop_powerup(this = this)
    DropPowerup,
    /// Verify jump on unit.carried_powerup_bits
    VerifyDropPowerup,
    /// Find remove_unit_ai(a1 = this, 1u8)
    RemoveUnitAi,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    KillUnitAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            KillUnitState::DropPowerup => {
                if let Operation::Call(dest) = *op {
                    if ctrl.resolve_register(1) == ctx.register(1)  {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.state = KillUnitState::VerifyDropPowerup;
                            self.inline_limit = 8;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.drop_powerup.is_some() {
                                self.result.drop_powerup = Some(dest);
                                self.state = KillUnitState::RemoveUnitAi;
                            } else {
                                self.state = KillUnitState::DropPowerup;
                            }
                        }
                    }
                }
            }
            KillUnitState::VerifyDropPowerup => {
                match *op {
                    Operation::Call(dest) => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.call_tracker.add_call_resolve(ctrl, dest);
                        }
                    }
                    Operation::Jump { condition, .. } => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                        let condition = ctrl.resolve(condition);
                        let carried_powerup_bits = E::struct_layouts().unit_poweurp_bits();
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| x.0.if_mem8_offset(carried_powerup_bits)) ==
                                Some(ctx.register(1));
                        if ok {
                            self.result.drop_powerup = Some(E::VirtualAddress::from_u64(0));
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
            KillUnitState::RemoveUnitAi => {
                let arg1;
                let arg2;
                let dest;
                if let Operation::Call(dest_) = *op {
                    dest = dest_;
                    arg1 = self.arg_cache.on_call(0);
                    arg2 = self.arg_cache.on_call(1);
                } else if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() && ctrl.resolve_register(4) == ctx.register(4) {
                        // Tail call
                        dest = to;
                        arg1 = self.arg_cache.on_entry(0);
                        arg2 = self.arg_cache.on_entry(1);
                    } else {
                        return;
                    }
                } else {
                    return;
                }
                let ok = ctrl.resolve(arg1) == ctx.register(1) &&
                    ctx.and_const(ctrl.resolve(arg2), 0xff) == ctx.const_1();
                if ok {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.result.remove_unit_ai = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_order_unit_morph<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_unit_morph: E::VirtualAddress,
) -> OrderUnitMorph<E::VirtualAddress> {
    let mut result = OrderUnitMorph {
        transform_unit: None,
        add_ai_to_trained_unit: None,
        show_finished_unit_notification: None,
        switch_construction_image: None,
        check_resources_for_building: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut exec_state = E::initial_state(ctx, binary);
    let order_state = ctx.mem_access(
        ctx.register(1),
        E::struct_layouts().unit_order_state(),
        MemAccessSize::Mem8,
    );

    // Order state 2
    exec_state.write_memory(&order_state, ctx.constant(2));
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        order_unit_morph,
        exec_state.clone(),
        Default::default(),
    );
    let mut analyzer = UnitMorphAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: UnitMorphState::TransformUnit,
        jump_seen: false,
        call_tracker: CallTracker::with_capacity(actx, 0, 16),
    };
    analysis.analyze(&mut analyzer);

    // Order state 0
    exec_state.write_memory(&order_state, ctx.constant(0));
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        order_unit_morph,
        exec_state,
        Default::default(),
    );
    analyzer.state = UnitMorphState::CheckResourcesForBuilding;
    analysis.analyze(&mut analyzer);
    result
}

struct UnitMorphAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderUnitMorph<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: UnitMorphState,
    call_tracker: CallTracker<'acx, 'e, E>,
    jump_seen: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum UnitMorphState {
    /// On order state 2
    /// transform_unit(this = this, this.build_queue_first)
    TransformUnit,
    /// add_ai_to_trained_unit(a1 = this, a2 = this)
    AddAiToTrainedUnit,
    /// a1 = this, right after add_ai_to_trained_unit, before any jumps
    ShowFinishedUnitNotification,
    /// Follow jump Mem32[units_dat_construction_image] != 0 path,
    /// switch_to_construction_image(this = this, a1 = 1u8)
    SwitchToConstructionImage,
    /// On order state 0
    /// a1 = this.player, a2 = this.build_queue_first, a3 = 1u8
    CheckResourcesForBuilding,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    UnitMorphAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let this = ctrl.resolve_register(1);
                let this_resolved = ctx.register(1);
                match self.state {
                    UnitMorphState::TransformUnit => {
                        if this == this_resolved {
                            let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                            let arg1 = self.call_tracker.resolve_simple(arg1);
                            let ok = arg1.if_mem16_offset(E::struct_layouts().unit_build_queue())
                                .is_some();
                            if ok {
                                self.result.transform_unit = Some(dest);
                                self.state = UnitMorphState::AddAiToTrainedUnit;
                                ctrl.clear_unchecked_branches();
                                return;
                            }
                        }
                        self.call_tracker.add_call_preserve_esp(ctrl, dest);
                    }
                    UnitMorphState::AddAiToTrainedUnit => {
                        let ok = ctrl.resolve(self.arg_cache.on_call(0)) == this_resolved &&
                            ctrl.resolve(self.arg_cache.on_call(1)) == this_resolved;
                        if ok {
                            self.result.add_ai_to_trained_unit = Some(dest);
                            self.state = UnitMorphState::ShowFinishedUnitNotification;
                            ctrl.clear_unchecked_branches();
                        }
                    }
                    UnitMorphState::ShowFinishedUnitNotification => {
                        let ok = ctrl.resolve(self.arg_cache.on_call(0)) == this_resolved;
                        if ok {
                            self.result.show_finished_unit_notification = Some(dest);
                            self.state = UnitMorphState::SwitchToConstructionImage;
                        }
                    }
                    UnitMorphState::SwitchToConstructionImage => {
                        if self.jump_seen && this == this_resolved {
                            let ok = ctrl.resolve(self.arg_cache.on_thiscall_call_u8(0)) ==
                                ctx.const_1();
                            if ok {
                                self.result.switch_construction_image = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                    UnitMorphState::CheckResourcesForBuilding => {
                        let ok = ctrl.resolve(self.arg_cache.on_call_u8(0))
                            .if_mem8_offset(E::struct_layouts().unit_player()) ==
                                Some(this_resolved) && {
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(1));
                            let arg1 = self.call_tracker.resolve_simple(arg1);
                            arg1.if_mem16_offset(E::struct_layouts().unit_build_queue()).is_some()
                        } && ctrl.resolve(self.arg_cache.on_call_u8(2)) == ctx.const_1();
                        if ok {
                            self.result.check_resources_for_building = Some(dest);
                            ctrl.end_analysis();
                            return;
                        }
                        if this == this_resolved {
                            self.call_tracker.add_call_preserve_esp(ctrl, dest);
                        }
                    }
                }
            }
        } else if let Operation::Jump { condition, to } = *op {
            match self.state {
                UnitMorphState::ShowFinishedUnitNotification => {
                    ctrl.end_analysis();
                    return;
                }
                UnitMorphState::SwitchToConstructionImage => {
                    let condition = ctrl.resolve(condition);
                    if let Some((other, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if other.if_mem32().is_some() {
                            ctrl.continue_at_neq_address(eq, to);
                            self.jump_seen = true;
                        }
                    }
                }
                _ => (),
            }
        }
    }
}
