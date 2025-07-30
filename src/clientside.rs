use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{
    BinaryFile, BinarySection, DestOperand, MemAccess, MemAccessSize, Operand, OperandCtx,
    Operation, Rva, ArithOpType,
};

use crate::analysis::{AnalysisCtx, ArgCache, Patch};
use crate::analysis_find::{EntryOf, EntryOfResult, FunctionFinder, entry_of_until};
use crate::analysis_state::{
    AnalysisState, StateEnum, MiscClientSideAnalyzerState, HandleTargetedClickState,
};
use crate::call_tracker::CallTracker;
use crate::hash_map::HashMap;
use crate::struct_layouts;
use crate::util::{
    ControlExt, MemAccessExt, OperandExt, OptionExt, single_result_assign, if_arithmetic_eq_neq,
    is_global, bumpvec_with_capacity, ExecStateExt, make_jump_unconditional,
};
use crate::vtables::Vtables;

pub enum ResultOrEntries<'acx, T, Va: VirtualAddress> {
    Result(T),
    /// "not ok", but have entries of the functions for further analysis.
    Entries(BumpVec<'acx, Va>),
}

#[derive(Default)]
pub struct GameCoordConversion<'e> {
    pub screen_x: Option<Operand<'e>>,
    pub screen_y: Option<Operand<'e>>,
    pub scale: Option<Operand<'e>>,
}

#[derive(Clone, Debug)]
pub struct GameScreenRClick<'e, Va: VirtualAddress> {
    pub game_screen_rclick: Option<Va>,
    pub client_selection: Option<Operand<'e>>,
}

#[derive(Default)]
pub struct MiscClientSide<'e> {
    pub is_paused: Option<Operand<'e>>,
    pub is_targeting: Option<Operand<'e>>,
    pub is_placing_building: Option<Operand<'e>>,
}

pub struct StartTargeting<'e, Va: VirtualAddress> {
    pub start_targeting: Option<Va>,
    pub targeted_order_unit: Option<Operand<'e>>,
    pub targeted_order_ground: Option<Operand<'e>>,
    pub targeted_order_fow: Option<Operand<'e>>,
    pub minimap_cursor_type: Option<Operand<'e>>,
}

pub(crate) struct TargetingLclick<Va: VirtualAddress> {
    pub find_unit_for_click: Option<Va>,
    pub find_fow_sprite_for_click: Option<Va>,
    pub handle_targeted_click: Option<Va>,
}

pub(crate) struct HandleTargetedClick<Va: VirtualAddress> {
    pub check_weapon_targeting_flags: Option<Va>,
    pub check_tech_targeting: Option<Va>,
    pub check_order_targeting: Option<Va>,
    pub check_fow_order_targeting: Option<Va>,
}

pub(crate) struct CenterViewAction<'e, Va: VirtualAddress> {
    pub move_screen: Option<Va>,
    pub trigger_current_player: Option<Operand<'e>>,
    pub game_screen_width_bwpx: Option<Operand<'e>>,
    pub game_screen_height_bwpx: Option<Operand<'e>>,
}

pub(crate) struct InitIngameUi<'e, Va: VirtualAddress> {
    pub init_ingame_ui: Option<Va>,
    pub init_obs_ui: Option<Va>,
    pub load_consoles: Option<Va>,
    pub init_consoles: Option<Va>,
    pub get_ui_consoles: Option<Va>,
    pub ui_consoles: Option<Operand<'e>>,
    pub observer_ui: Option<Operand<'e>>,
}

pub(crate) struct GameScreenLClick<'e, Va: VirtualAddress> {
    pub stop_targeting: Option<Va>,
    pub place_building: Option<Va>,
    pub select_mouse_up: Option<Va>,
    pub select_mouse_move: Option<Va>,
    pub clip_cursor: Option<Va>,
    pub game_screen_rect_winpx: Option<Operand<'e>>,
    pub on_clip_cursor_end: Option<Operand<'e>>,
    pub select_start_x: Option<Operand<'e>>,
    pub select_start_y: Option<Operand<'e>>,
    pub is_selecting: Option<Operand<'e>>,
}

pub(crate) struct SelectMouseUp<Va: VirtualAddress> {
    pub decide_cursor_type: Option<Va>,
    pub set_current_cursor_type: Option<Va>,
    pub select_units: Option<Va>,
}

pub(crate) struct UpdateGameScreenSize<'e> {
    pub update_mode: Option<Operand<'e>>,
    pub game_screen_height_ratio: Option<Operand<'e>>,
}

pub(crate) struct TalkingPortrait<Va: VirtualAddress> {
    pub trigger_talking_portrait: Option<Va>,
    pub show_portrait: Option<Va>,
}

pub(crate) struct ShowPortrait<'e> {
    pub videos: Option<Operand<'e>>,
    pub talking_active: Option<Operand<'e>>,
    pub video_id: Option<Operand<'e>>,
}

pub(crate) struct LoadAllCursors<Va: VirtualAddress> {
    pub load_all_cursors: Option<Va>,
    pub load_ddsgrp_cursor: Option<Va>,
}

// Candidates are either a global ref with Some(global), or a call with None
fn game_screen_rclick_inner<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    candidates: &[(E::VirtualAddress, Option<E::VirtualAddress>)],
    checked_functions: &mut BumpVec<'acx, E::VirtualAddress>,
) -> ResultOrEntries<'acx, (E::VirtualAddress, Operand<'e>), E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    let mut result: Option<(E::VirtualAddress, Operand<'e>)> = None;
    let mut entries = BumpVec::new_in(bump);
    'outer: for &(middle_of_func, global_addr) in candidates {
        let res = entry_of_until(binary, &funcs, middle_of_func, |entry| {
            if checked_functions.contains(&entry) {
                return EntryOf::Stop;
            }
            checked_functions.push(entry);
            let mut analyzer = GameScreenRClickAnalyzer::<E> {
                call_found: false,
                result: None,
                mov_u32_max_seen: false,
                first_branch: true,
                middle_of_func,
                global_addr,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if let Some(res) = analyzer.result {
                return EntryOf::Ok(res);
            }
            if analyzer.call_found {
                EntryOf::Stop
            } else {
                EntryOf::Retry
            }
        });
        match res {
            EntryOfResult::Ok(show_rclick_error_if_needed, client_selection) => {
                entries.push(show_rclick_error_if_needed);
                let callers = functions.find_callers(analysis, show_rclick_error_if_needed);
                for f in callers {
                    let res: EntryOfResult<(), E::VirtualAddress> = entry_of_until(
                        binary,
                        &funcs,
                        f,
                        |entry| {
                            let mut analyzer = WasInstructionRan::<E> {
                                ins: f,
                                result: false,
                            };
                            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                            analysis.analyze(&mut analyzer);
                            if analyzer.result {
                                EntryOf::Stop
                            } else {
                                EntryOf::Retry
                            }
                        }
                    );
                    if let EntryOfResult::Entry(e) = res {
                        let res = Some((e, client_selection.clone()));
                        if single_result_assign(res, &mut result) {
                            break 'outer;
                        }
                    }
                }
            }
            EntryOfResult::Entry(e) => {
                entries.push(e);
            }
            EntryOfResult::None => (),
        }
    }
    match result {
        Some(s) => ResultOrEntries::Result(s),
        None => ResultOrEntries::Entries(entries),
    }
}

struct WasInstructionRan<'e, E: ExecutionState<'e>> {
    ins: E::VirtualAddress,
    result: bool,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for WasInstructionRan<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, _op: &Operation<'e>) {
        if ctrl.address() == self.ins {
            self.result = true;
            ctrl.end_analysis();
        }
    }
}

struct GameScreenRClickAnalyzer<'e, E: ExecutionState<'e>> {
    call_found: bool,
    first_branch: bool,
    mov_u32_max_seen: bool,
    result: Option<Operand<'e>>,
    middle_of_func: E::VirtualAddress,
    global_addr: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for GameScreenRClickAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        if !self.call_found {
            let in_possible_range =
                address.as_u64() >= self.middle_of_func.as_u64() - 8 &&
                address <= self.middle_of_func;
            if in_possible_range {
                if let Some(global_addr) = self.global_addr {
                    if let Operation::Move(_, ref val) = *op {
                        // No need to resolve here, as the constant
                        // was found by just binary scanning,
                        self.call_found = val.if_memory()
                            .map(|x| x.address().1)
                            .or_else(|| val.if_constant())
                            .map(|x| x == global_addr.as_u64())
                            .is_some();
                    }
                } else {
                    self.call_found = address == self.middle_of_func;
                }
            }
        }
        if self.call_found && !self.first_branch {
            ctrl.end_analysis();
            return;
        }
        match *op {
            Operation::Move(ref dest, val) => {
                if !self.mov_u32_max_seen && self.first_branch {
                    let val = ctrl.resolve(val);
                    if val.if_constant().map(|x| x as u32) == Some(u32::MAX) {
                        if E::VirtualAddress::SIZE == 4 {
                            if let DestOperand::Memory(dest) = dest {
                                // Don't accept push -1 which is part of SEH scope in function
                                // prologue.
                                let ctx = ctrl.ctx();
                                if dest.address() == (ctx.register(4), 0) {
                                    let dest = ctrl.resolve_mem(dest);
                                    if dest.address() == (ctx.register(4), -8i64 as u64) {
                                        return;
                                    }
                                }
                            }
                        }
                        self.mov_u32_max_seen = true;
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.mov_u32_max_seen {
                    let condition = ctrl.resolve(condition);
                    let ctx = ctrl.ctx();
                    let client_selection = condition.if_arithmetic_eq()
                        .filter(|x| x.1 == ctx.const_0())
                        .and_then(|x| x.0.if_memory())
                        .map(|mem| {
                            ctx.mem_sub_const_op(mem, u64::from(11 * E::VirtualAddress::SIZE))
                        });
                    if let Some(csl) = client_selection {
                        self.result = Some(csl);
                    }
                }
                self.first_branch = false;
            }
            Operation::Call(..) => {
                self.first_branch = false;
            }
            _ => (),
        }
    }
}

// Candidates are either a global ref with Some(global), or a call with None
pub(crate) fn is_outside_game_screen<'a, E: ExecutionState<'a>>(
    analysis: &AnalysisCtx<'a, E>,
    game_screen_rclick: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    struct Analyzer<'a, E: ExecutionState<'a>> {
        result: Option<E::VirtualAddress>,
    }

    impl<'a, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation<'a>) {
            match *op {
                Operation::Jump { .. } => {
                    ctrl.end_analysis();
                }
                Operation::Call(to) => {
                    let to = ctrl.resolve_va(to);
                    let arg1 = ctrl.resolve_arg(0).unwrap_sext();
                    let arg2 = ctrl.resolve_arg(1).unwrap_sext();
                    if let Some(dest) = to {
                        if arg1.if_mem16().is_some() && arg2.if_mem16().is_some() {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = Analyzer::<E> {
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_rclick);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn if_float_to_int<'e>(operand: Operand<'e>) -> Option<Operand<'e>> {
    match *operand.ty() {
        scarf::operand::OperandType::ArithmeticFloat(ref arith, _)
            if arith.ty == scarf::operand::ArithOpType::ToInt => Some(arith.left),
        _ => None,
    }
}

fn if_int_to_float<'e>(operand: Operand<'e>) -> Option<Operand<'e>> {
    match *operand.ty() {
        scarf::operand::OperandType::Arithmetic(ref arith)
            if arith.ty == scarf::operand::ArithOpType::ToFloat => Some(arith.left),
        _ => None,
    }
}

fn if_f32_div<'e>(operand: Operand<'e>) -> Option<(Operand<'e>, Operand<'e>)> {
    match *operand.ty() {
        scarf::operand::OperandType::ArithmeticFloat(ref arith, MemAccessSize::Mem32)
            if arith.ty == scarf::operand::ArithOpType::Div => Some((arith.left, arith.right)),
        _ => None,
    }
}

pub(crate) fn game_coord_conversion<'a, E: ExecutionState<'a>>(
    analysis: &AnalysisCtx<'a, E>,
    game_screen_rclick: E::VirtualAddress,
    is_outside_game_screen: E::VirtualAddress,
) -> GameCoordConversion<'a> {
    let mut result = GameCoordConversion::default();

    // Search for the collowing start in game_screen_rclick:
    // if is_outside_game_screen(event.x, event.y) == 0 {
    //     convert_screen_to_game(event, &mut out_xy);
    //     ...
    // } else {
    //     ...
    // }

    struct Analyzer<'a, 'b, E: ExecutionState<'a>> {
        depth: u32,
        result: &'b mut GameCoordConversion<'a>,
        set_eax_to_zero: bool,
        is_outside_game_screen: E::VirtualAddress,
        is_outside_game_screen_seen: bool,
        ctx: OperandCtx<'a>,
        args: &'b ArgCache<'a, E>,
    }

    impl<'a, 'b, E: ExecutionState<'a>> Analyzer<'a, 'b, E> {
        fn is_event_pos_in_game_coords_call<A: scarf::Analyzer<'a>>(
            &self,
            ctrl: &mut Control<'a, '_, '_, A>,
        ) -> bool {
            let arg2 = ctrl.resolve_arg(1);
            arg2 == self.args.on_entry(0)
        }

        // Check for screen_x + mem16[&event.x] / scale
        fn check_move<'e>(val: Operand<'e>) -> Option<(Operand<'e>, Operand<'e>, u32)> {
            val.if_arithmetic_add()
                .and_either(|x| x.if_mem32().map(|_| x))
                .and_then(|(screen_coord, other)| {
                    if_float_to_int(other)
                        .and_then(if_f32_div)
                        .and_then(|(l, divisor)| {
                            if_int_to_float(l)
                                .and_then(|x| x.unwrap_sext().if_mem16())
                                .map(|mem| (screen_coord, divisor, mem.address().1 as u32))
                        })
                })
        }
    }

    impl<'a, 'b, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation<'a>) {
            if self.set_eax_to_zero {
                self.set_eax_to_zero = false;
                ctrl.set_register(0, self.ctx.const_0());
                return;
            }
            match *op {
                Operation::Call(to) => {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        if !self.is_outside_game_screen_seen {
                            if dest == self.is_outside_game_screen {
                                self.is_outside_game_screen_seen = true;
                                self.set_eax_to_zero = true;
                            }
                            return;
                        }

                        if self.depth == 0 {
                            if self.is_event_pos_in_game_coords_call(ctrl) {
                                self.depth += 1;
                                ctrl.inline(self, dest);
                                ctrl.skip_operation();
                                self.depth -= 1;
                            }
                        } else if self.depth == 3 {
                            ctrl.end_analysis();
                            return;
                        } else {
                            self.depth += 1;
                            ctrl.inline(self, dest);
                            ctrl.skip_operation();
                            self.depth -= 1;
                        }
                        if self.result.screen_x.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
                Operation::Move(_, val) => {
                    if self.depth != 0 {
                        let val = ctrl.resolve(val);
                        let result = Self::check_move(val);
                        if let Some((screen_coord, scale, struct_offset)) = result {
                            if struct_offset == E::struct_layouts().event_mouse_xy() as u32 {
                                self.result.screen_x = Some(screen_coord);
                                self.result.scale = Some(scale);
                            } else {
                                self.result.screen_y = Some(screen_coord);
                            }
                            if self.result.screen_x.is_some() && self.result.screen_y.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = Analyzer {
        result: &mut result,
        depth: 0,
        set_eax_to_zero: false,
        is_outside_game_screen_seen: false,
        is_outside_game_screen,
        ctx,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_rclick);
    analysis.analyze(&mut analyzer);

    result
}

pub(crate) fn game_screen_rclick<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> GameScreenRClick<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let bump = &analysis.bump;

    // units_dat_rlick_order is accessed by get_rclick_order,
    // which is called/inlined by show_rclick_error_if_needed,
    // which is recognized from moving -1 into a local at start of the function,
    // which also contains loop over client selection (while ptr != &client_selection[0])
    // game_screen_rclick should be only caller of show_rclick_error_if_needed

    let rclick_order = binary.read_address(units_dat.0 + 0x1c * units_dat.1)
        .unwrap_or_else(|_| E::VirtualAddress::from_u64(0));
    let uses = BumpVec::from_iter_in(
        functions.find_functions_using_global(analysis, rclick_order)
            .into_iter()
            .map(|x| (x.use_address, Some(rclick_order))),
        bump,
    );
    let mut checked_functions = bumpvec_with_capacity(0x20, bump);
    let result = game_screen_rclick_inner(analysis, functions, &uses, &mut checked_functions);
    let result = match result {
        ResultOrEntries::Entries(entries) => {
            let callers = entries.iter().flat_map(|&f| {
                functions.find_callers(analysis, f).into_iter().map(|x| (x, None))
            });
            let callers = BumpVec::from_iter_in(callers, bump);
            game_screen_rclick_inner(analysis, functions, &callers, &mut checked_functions)
        }
        ResultOrEntries::Result(o) => ResultOrEntries::Result(o),
    };

    match result {
        ResultOrEntries::Result((rclick, csl)) => GameScreenRClick {
            client_selection: Some(csl),
            game_screen_rclick: Some(rclick),
        },
        ResultOrEntries::Entries(..) => GameScreenRClick {
            client_selection: None,
            game_screen_rclick: None,
        },
    }
}

pub(crate) fn misc_clientside<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    is_multiplayer: Operand<'e>,
    scmain_state: Operand<'e>,
    vtables: &Vtables<'e, E::VirtualAddress>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> MiscClientSide<'e> {
    let mut result = MiscClientSide {
        is_paused: None,
        is_placing_building: None,
        is_targeting: None,
    };
    // Options menu popup does the usual pausing game/canceling placement/targeting
    // Get init func from its vtable, then search for a inner function
    // if this.vtable_fn() == 0 {
    //    ui_switching_to_dialog();
    // }
    //
    // ui_switching_to_dialog has the checks:
    // if is_multiplayer == 0 {
    //    pause_game()
    // }
    // if scmain_state == 3 {
    //   if is_placing_building {
    //     end_building_placement()
    //   }
    //   if is_targeting {
    //     end_targeting()
    //   }
    // }
    let bump = &analysis.bump;
    let vtables = vtables.vtables_starting_with(b".?AVOptionsMenuPopup@glues@@\0")
        .map(|x| x.address);
    let mut vtables = BumpVec::from_iter_in(vtables, bump);
    if vtables.is_empty() {
        vtables = options_menu_vtables_fallback(analysis, functions);
    }
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let vtable_fn_result_op = ctx.custom(0);
    for vtable in vtables {
        let init_func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let state = MiscClientSideAnalyzerState::Begin;
        let state = AnalysisState::new(bump, StateEnum::MiscClientSide(state));
        let mut analyzer = MiscClientSideAnalyzer {
            result: &mut result,
            done: false,
            inline_depth: 0,
            vtable_fn_result_op,
            is_multiplayer,
            scmain_state,
            branch_start_states: Default::default(),
            binary,
            phantom: Default::default(),
        };
        let exec = E::initial_state(ctx, binary);
        let mut analysis = FuncAnalysis::custom_state(binary, ctx, init_func, exec, state);
        analysis.analyze(&mut analyzer);
        // Not taking half-complete results for this, I don't have the confidence
        // that they would be right.
        if analyzer.done {
            break;
        } else {
            result = MiscClientSide {
                is_paused: None,
                is_placing_building: None,
                is_targeting: None,
            };
        }
    }
    result
}

/// No-RTTI fallback, find vtable from OptionsMenuPopup constructor
fn options_menu_vtables_fallback<'acx, 'e, E: ExecutionState<'e>>(
    actx: &'acx AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> BumpVec<'acx, E::VirtualAddress> {
    let str_refs = crate::dialog::dialog_string_refs(
        actx,
        functions,
        b"rez\\gluoptionspopup",
        b"gluoptionspopup.ui",
    );
    let funcs = functions.functions();
    let bump = &actx.bump;
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = bumpvec_with_capacity(0x4, bump);
    for str_ref in &str_refs {
        entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = FindConstructorVtable::<E> {
                use_address: str_ref.use_address,
                result: &mut result,
                entry_of: EntryOf::Retry,
                rdata: actx.binary_sections.rdata,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        if !result.is_empty() {
            break;
        }
    }
    result
}

struct FindConstructorVtable<'a, 'acx, 'e, E: ExecutionState<'e>> {
    use_address: E::VirtualAddress,
    result: &'a mut BumpVec<'acx, E::VirtualAddress>,
    rdata: &'e BinarySection<E::VirtualAddress>,
    entry_of: EntryOf<()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    FindConstructorVtable<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;

    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.use_address >= ctrl.address() &&
            self.use_address < ctrl.current_instruction_end()
        {
            self.entry_of = EntryOf::Ok(());
        }
        if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
            if mem.size == E::WORD_SIZE {
                let value = ctrl.resolve(value);
                if let Some(c) = value.if_constant() {
                    let addr = E::VirtualAddress::from_u64(c);
                    if self.rdata.contains(addr) {
                        let mem = ctrl.resolve_mem(mem);
                        let ctx = ctrl.ctx();
                        let (base, offset) = mem.address();
                        if base == ctx.register(1) {
                            // There are 2 vtables, one at offset 0 and other at higher
                            // The one at 0 is one needed here.
                            if offset == 0 {
                                self.result.push(addr);
                                ctrl.end_analysis();
                                self.entry_of = EntryOf::Ok(());
                            }
                        }
                    }
                }
            }
        }
    }
}

struct MiscClientSideAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut MiscClientSide<'e>,
    done: bool,
    inline_depth: u8,
    vtable_fn_result_op: Operand<'e>,
    is_multiplayer: Operand<'e>,
    scmain_state: Operand<'e>,
    branch_start_states: HashMap<Rva, MiscClientSideAnalyzerState>,
    binary: &'a BinaryFile<E::VirtualAddress>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    MiscClientSideAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let rva = Rva((ctrl.address().as_u64() - self.binary.base.as_u64()) as u32);
        if let Some(state) = self.branch_start_states.remove(&rva) {
            if state == MiscClientSideAnalyzerState::MultiplayerZeroBranch {
                self.inline_depth = 0;
            }
            ctrl.user_state().set(state);
        }
    }

    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        use MiscClientSideAnalyzerState as State;
        match ctrl.user_state().get::<State>() {
            State::End => {
                ctrl.end_branch();
            }
            State::Begin => self.state_begin(ctrl, op),
            State::OnVtableFnZeroBranch => self.state_vtable_fn_zero_branch(ctrl, op),
            State::MultiplayerZeroBranch => self.state_multiplayer_zero_branch(ctrl, op),
            State::ScMainStateThreeBranch | State::IsPlacingBuildingFound => {
                self.state_check_placing_building_or_targeting(ctrl, op);
            }
        }
    }
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> MiscClientSideAnalyzer<'a, 'acx, 'e, E> {
    fn state_begin(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        use MiscClientSideAnalyzerState as State;
        // Check for the this.vtable_fn() call and
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                // call [[ecx] + offset]
                let is_vtable_fn = ctrl.if_mem_word(dest)
                    .and_then(|x| ctrl.if_mem_word_offset(x.address().0, 0))
                    .filter(|&x| x == ctx.register(1))
                    .is_some();
                if is_vtable_fn {
                    ctrl.skip_operation();
                    ctrl.set_register(0, self.vtable_fn_result_op);
                }

            }
            Operation::Jump { condition, to } => {
                let cond = ctrl.resolve(condition);
                let cond_ok = if_arithmetic_eq_neq(cond)
                    .filter(|x| x.1 == ctx.const_0())
                    .filter(|x| Operand::and_masked(x.0).0 == self.vtable_fn_result_op)
                    .map(|x| x.2);
                if let Some(is_eq) = cond_ok {
                    // is_eq: true jumps if x == 0
                    // is_eq: false jumps if x != 0
                    let branch_start = match is_eq {
                        true => match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        },
                        false => ctrl.current_instruction_end(),
                    };
                    let rva = Rva((branch_start.as_u64() - self.binary.base.as_u64()) as u32);
                    self.branch_start_states.insert(rva, State::OnVtableFnZeroBranch);
                }
            }
            _ => (),
        }
    }

    fn state_vtable_fn_zero_branch(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        use MiscClientSideAnalyzerState as State;
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth < 2 {
                    // Inline once fully to ui_switching_to_dialog,
                    // also allow partial inlining is is_multiplayer read
                    // is inside function
                    let old_inline_depth = self.inline_depth;
                    self.inline_depth += 1;
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                    }
                    self.inline_depth = old_inline_depth;
                    if self.done {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if self.inline_depth == 2 {
                    ctrl.end_analysis();
                }
                let cond = ctrl.resolve(condition);
                let cond_ok = if_arithmetic_eq_neq(cond)
                    .and_then(|(l, r, is_eq)| {
                        Some((l, r))
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                            .filter(|&x| x == self.is_multiplayer)?;
                        Some(is_eq)
                    });
                if let Some(is_eq) = cond_ok {
                    let branch_start = match is_eq {
                        true => match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        },
                        false => ctrl.current_instruction_end(),
                    };
                    let rva = Rva((branch_start.as_u64() - self.binary.base.as_u64()) as u32);
                    self.branch_start_states.insert(rva, State::MultiplayerZeroBranch);
                }
            }
            _ => (),
        }
    }

    fn state_multiplayer_zero_branch(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        use MiscClientSideAnalyzerState as State;
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.inline_depth == 0 {
                        self.inline_depth += 1;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inline_depth -= 1;
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let cond = ctrl.resolve(condition);
                // Check for if_paused if inlining,
                // otherwise for scmain_state == 3
                if self.inline_depth == 0 {
                    let cond_ok = if_arithmetic_eq_neq(cond)
                        .and_then(|(l, r, is_eq)| {
                            Some((l, r))
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 3))
                                .map(|x| Operand::and_masked(x).0)
                                .filter(|&x| x == self.scmain_state)?;
                            Some(is_eq)
                        });
                    if let Some(is_eq) = cond_ok {
                        let branch_start = match is_eq {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        let rva = Rva((branch_start.as_u64() - self.binary.base.as_u64()) as u32);
                        self.branch_start_states.insert(rva, State::ScMainStateThreeBranch);
                    }
                } else {
                    if self.result.is_paused.is_none() {
                        let is_paused = if_arithmetic_eq_neq(cond)
                            .map(|(l, r, _)| (l, r))
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 0));
                        if let Some(is_paused) = is_paused {
                            self.result.is_paused = Some(is_paused.clone());
                        }
                    }
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }

    fn state_check_placing_building_or_targeting(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        use MiscClientSideAnalyzerState as State;
        // These two are similar checks.
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.inline_depth == 0 {
                        self.inline_depth += 1;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inline_depth -= 1;
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                if self.inline_depth == 0 {
                    let ctx = ctrl.ctx();
                    // Condition should always be x == 0,
                    // check for that to avoid confusing with `x != 0` assertion jump
                    let cond_ok = if_arithmetic_eq_neq(cond)
                        .filter(|x| x.1 == ctx.const_0() && x.2 == true)
                        .map(|x| x.0);
                    if let Some(op) = cond_ok {
                        let state = ctrl.user_state().get::<State>();
                        if *state == State::ScMainStateThreeBranch {
                            self.result.is_placing_building = Some(op.clone());
                            *state = State::IsPlacingBuildingFound;
                        } else {
                            self.result.is_targeting = Some(op.clone());
                            self.done = true;
                            *state = State::End;
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    // Only inline functions which are jumpless (e.g. get_is_targeting)
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn start_targeting<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    button_sets: E::VirtualAddress,
) -> StartTargeting<'e, E::VirtualAddress> {
    let mut result = StartTargeting {
        start_targeting: None,
        targeted_order_unit: None,
        targeted_order_ground: None,
        targeted_order_fow: None,
        minimap_cursor_type: None,
    };

    // Patrol button action (buttonsets[0][3].action) should just call
    // start_targeting(0x98, 0x98, 0x98)
    // start_targeting arg1 is unit target, arg 2 ground target, arg 3 fow target,
    // they get stored to targeted_order_x globals.
    // Additionally it writes 2 to minimap_cursor_type.

    let binary = actx.binary;
    let ctx = actx.ctx;
    let patrol_action =
        match struct_layouts::button_set_index_to_action(binary, button_sets, 0, 3)
    {
        Some(s) => s,
        None => return result,
    };
    let mut analyzer = StartTargetingAnalyzer {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        in_start_targeting: false,
        results_found: 0,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, patrol_action);
    analysis.analyze(&mut analyzer);

    result
}

struct StartTargetingAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    result: &'a mut StartTargeting<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    in_start_targeting: bool,
    results_found: u8,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for StartTargetingAnalyzer<'e, 'a, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if !self.in_start_targeting {
            let ctx = ctrl.ctx();
            let dest = if let Operation::Call(dest) = *op {
                dest
            } else if let Operation::Jump { to, condition } = *op {
                // Tail call
                let esp = ctx.register(4);
                if condition == ctx.const_1() && ctrl.resolve(esp) == esp {
                    to
                } else {
                    return;
                }
            } else {
                return;
            };
            if let Some(dest) = ctrl.resolve_va(dest) {
                let ok = (0..3).all(|i| {
                    ctrl.resolve_arg_u8(i).if_constant() == Some(0x98)
                });
                if ok {
                    self.result.start_targeting = Some(dest);
                    self.in_start_targeting = true;
                    let binary = ctrl.binary();
                    let mut analysis = FuncAnalysis::new(binary, ctx, dest);
                    analysis.analyze(self);
                    ctrl.end_analysis();
                }
            }
        } else {
            if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                let mem = ctrl.resolve_mem(mem);
                if mem.is_global() {
                    let ctx = ctrl.ctx();
                    let value = ctx.and_const(ctrl.resolve(value), 0xff);
                    let result = &mut self.result;
                    let result_out = if value.if_constant() == Some(2) {
                        &mut result.minimap_cursor_type
                    } else if value == ctx.and_const(self.arg_cache.on_entry(0), 0xff) {
                        &mut result.targeted_order_unit
                    } else if value == ctx.and_const(self.arg_cache.on_entry(1), 0xff) {
                        &mut result.targeted_order_ground
                    } else if value == ctx.and_const(self.arg_cache.on_entry(2), 0xff) {
                        &mut result.targeted_order_fow
                    } else {
                        return;
                    };
                    if single_result_assign(Some(ctx.memory(&mem)), result_out) {
                        if self.results_found >= 3 {
                            ctrl.end_analysis();
                            return;
                        }
                        self.results_found += 1;
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_targeting_lclick<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    lclick: E::VirtualAddress,
) -> TargetingLclick<E::VirtualAddress> {
    let mut result = TargetingLclick {
        find_unit_for_click: None,
        find_fow_sprite_for_click: None,
        handle_targeted_click: None,
    };

    // There should be the following calls
    // event_coords_to_game(&mut xy, arg1)
    // unit = find_unit_for_click(xy[0], xy[1])
    // fow = find_fow_sprite_for_click(xy[0], xy[1], unit)
    // handle_targeted_click(xy[0], xy[1], unit, fow ? fow : e4)

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = TargetingLclickAnalyzer {
        result: &mut result,
        arg_cache: &actx.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, lclick);
    analysis.analyze(&mut analyzer);

    result
}

struct TargetingLclickAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    result: &'a mut TargetingLclick<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for TargetingLclickAnalyzer<'e, 'a, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            let ctx = ctrl.ctx();
            let arg1 = ctrl.resolve_arg(0);
            let arg2 = ctrl.resolve_arg(1);
            if arg2 == self.arg_cache.on_entry(0) {
                // event_coords_to_game, use Custom(0) for x and Custom(1) for y
                let mem = ctx.mem_access(arg1, 0, MemAccessSize::Mem32);
                ctrl.write_memory(&mem, ctx.custom(0));
                let mem = mem.with_offset_size(4, MemAccessSize::Mem32);
                ctrl.write_memory(&mem, ctx.custom(1));
            } else if Operand::and_masked(arg2).0.if_custom() == Some(1) &&
                Operand::and_masked(arg1).0.if_custom() == Some(0)
            {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let result = &mut self.result;
                    if result.find_unit_for_click.is_none() {
                        result.find_unit_for_click = Some(dest);
                        ctrl.do_call_with_result(ctx.custom(2));
                    } else {
                        let arg3 = ctrl.resolve_arg(2);
                        if arg3.if_custom() == Some(2) {
                            if result.find_fow_sprite_for_click.is_none() {
                                result.find_fow_sprite_for_click = Some(dest);
                            } else {
                                result.handle_targeted_click = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_handle_targeted_click<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    handle_targeted_click: E::VirtualAddress,
    orders_dat: (E::VirtualAddress, u32),
) -> HandleTargetedClick<E::VirtualAddress> {
    let mut result = HandleTargetedClick {
        check_weapon_targeting_flags: None,
        check_tech_targeting: None,
        check_order_targeting: None,
        check_fow_order_targeting: None,
    };

    // Find check_weapon_targeting_flags(orders_dat_weapon[order], target(this arg3)),
    // preceded by orders_dat_use_weapon_targeting[order] != 0 jump
    //
    // Find check_tech_targeting(orders_dat_tech[order], target, fow, x, y, _),
    // preceded by orders_dat_tech[order] != 2c jump
    //
    // Find check_order_targeting(order, target, x, y, _)
    // and check_fow_order_targeting(order, fow, x, y, _)
    // in branch where weapon_targeting == false and tech == 2c
    //
    // `order` operand will be same Undefined for all checks, get it from one of the
    // orders_dat_x indexing jumps

    let binary = actx.binary;
    let ctx = actx.ctx;

    let orders_dat_use_weapon_targeting =
        match binary.read_address(orders_dat.0 + orders_dat.1 * 0x1)
    {
        Ok(o) => o,
        Err(_) => return result,
    };
    let orders_dat_weapon = match binary.read_address(orders_dat.0 + orders_dat.1 * 0xd) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let orders_dat_tech = match binary.read_address(orders_dat.0 + orders_dat.1 * 0xe) {
        Ok(o) => o,
        Err(_) => return result,
    };

    let bump = &actx.bump;

    let mut analyzer = HandleTargetedClickAnalyzer {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        orders_dat_use_weapon_targeting,
        orders_dat_tech,
        orders_dat_weapon,
        order_operand: None,
        phantom: Default::default(),
    };
    let state = HandleTargetedClickState {
        order_weapon_branch: None,
        order_tech_branch: None,
    };
    let state = AnalysisState::new(bump, StateEnum::HandleTargetedClick(state));
    let exec = E::initial_state(ctx, binary);
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, handle_targeted_click, exec, state);
    analysis.analyze(&mut analyzer);

    result
}

struct HandleTargetedClickAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut HandleTargetedClick<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    orders_dat_use_weapon_targeting: E::VirtualAddress,
    orders_dat_tech: E::VirtualAddress,
    orders_dat_weapon: E::VirtualAddress,
    order_operand: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    HandleTargetedClickAnalyzer<'e, 'acx, 'a, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Jump { condition, to } = *op {
            if let Some(to) = ctrl.resolve_va(to) {
                let condition = ctrl.resolve(condition);
                let ok = if_arithmetic_eq_neq(condition)
                    .and_then(|(l, r, is_eq)| {
                        let constant = r.if_constant()?;
                        let mem = l.if_mem8()?;
                        let (index, address) = mem.address();
                        // false => order jump
                        let weapon_jump;
                        if address == self.orders_dat_use_weapon_targeting.as_u64() &&
                            constant == 0
                        {
                            weapon_jump = true;
                        } else if address == self.orders_dat_tech.as_u64() && constant == 0x2c {
                            weapon_jump = false;
                        } else {
                            return None;
                        }
                        if let Some(op) = self.order_operand {
                            if op != index {
                                return None;
                            }
                        } else {
                            self.order_operand = Some(index);
                        }
                        // For both cases eq branch is not weapon/tech branch:
                        // use_weapon_targeting == 0 or tech == NO_TECH
                        let no_jump = ctrl.current_instruction_end();
                        let (true_branch, false_branch) = match is_eq {
                            true => (no_jump, to),
                            false => (to, no_jump),
                        };
                        let state = ctrl.user_state().get::<HandleTargetedClickState>();
                        if weapon_jump {
                            state.order_weapon_branch = Some(true);
                        } else {
                            state.order_tech_branch = Some(true);
                        }
                        ctrl.add_branch_with_current_state(true_branch);
                        let state = ctrl.user_state().get::<HandleTargetedClickState>();
                        if weapon_jump {
                            state.order_weapon_branch = Some(false);
                        } else {
                            state.order_tech_branch = Some(false);
                        }
                        ctrl.continue_at_address(false_branch);
                        Some(())
                    })
                    .is_some();
                if !ok {
                    ctrl.assign_to_unresolved_on_eq_branch(condition, to);
                }
            }
        } else if let Operation::Call(dest) = *op {
            let dest = match ctrl.resolve_va(dest) {
                Some(s) => s,
                None => return,
            };
            let ctx = ctrl.ctx();
            let args: [Operand<'e>; 5] = array_init::array_init(|i| {
                ctrl.resolve_arg_thiscall(i as u8)
            });
            let state = ctrl.user_state().get::<HandleTargetedClickState>();
            let mut got_result = false;
            if state.order_weapon_branch == Some(true) {
                let ok =
                    self.is_dat_index(ctx.and_const(args[0], 0xff), self.orders_dat_weapon) &&
                    args[1] == self.arg_cache.on_entry(2);
                if ok {
                    single_result_assign(
                        Some(dest),
                        &mut self.result.check_weapon_targeting_flags,
                    );
                    got_result = true;
                }
            } else if state.order_tech_branch == Some(true) {
                let ok = self.is_dat_index(ctx.and_const(args[0], 0xff), self.orders_dat_tech) &&
                    args[1] == self.arg_cache.on_entry(2) &&
                    ctx.and_const(args[2], 0xffff) ==
                        ctx.and_const(self.arg_cache.on_entry(3), 0xffff) &&
                    ctx.and_const(args[3], 0xffff_ffff) ==
                        ctx.and_const(self.arg_cache.on_entry(0), 0xffff_ffff) &&
                    ctx.and_const(args[4], 0xffff_ffff) ==
                        ctx.and_const(self.arg_cache.on_entry(1), 0xffff_ffff);
                if ok {
                    single_result_assign(Some(dest), &mut self.result.check_tech_targeting);
                    got_result = true;
                }
            } else if state.order_weapon_branch == Some(false) &&
                state.order_tech_branch == Some(false)
            {
                let ok = Some(ctx.and_const(args[0], 0xff)) == self.order_operand &&
                    ctx.and_const(args[2], 0xffff_ffff) ==
                        ctx.and_const(self.arg_cache.on_entry(0), 0xffff_ffff) &&
                    ctx.and_const(args[3], 0xffff_ffff) ==
                        ctx.and_const(self.arg_cache.on_entry(1), 0xffff_ffff);
                if ok {
                    if args[1] == self.arg_cache.on_entry(2) {
                        single_result_assign(Some(dest), &mut self.result.check_order_targeting);
                        got_result = true;
                    } else if ctx.and_const(args[1], 0xffff) ==
                        ctx.and_const(self.arg_cache.on_entry(3), 0xffff)
                    {
                        single_result_assign(
                            Some(dest),
                            &mut self.result.check_fow_order_targeting,
                        );
                        got_result = true;
                    }
                }
            }
            if got_result {
                ctrl.end_branch();
                let result = &mut self.result;
                if result.check_weapon_targeting_flags.is_some() &&
                    result.check_tech_targeting.is_some() &&
                    result.check_order_targeting.is_some() &&
                    result.check_fow_order_targeting.is_some()
                {
                    ctrl.end_analysis();
                }
            }
        } else if let Operation::ConditionalMove(ref dest, val, condition) = *op {
            // Assume that orders_dat_obscured[x] is never 0xbd
            let condition = ctrl.resolve(condition);
            if let Some((_, right, is_eq)) = if_arithmetic_eq_neq(condition) {
                if right.if_constant() == Some(0xbd) {
                    // If move when x == bd => skip
                    // If move when x != bd => do unconditionally
                    ctrl.skip_operation();
                    if !is_eq {
                        ctrl.move_unresolved(dest, val);
                    }
                }
            }
        }
    }
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> HandleTargetedClickAnalyzer<'e, 'acx, 'a, E> {
    fn is_dat_index(&mut self, op: Operand<'e>, dat: E::VirtualAddress) -> bool {
        op.if_mem8()
            .filter(|mem| {
                let (index, address) = mem.address();
                Some(index) == self.order_operand && address == dat.as_u64()
            })
            .is_some()
    }
}

pub(crate) fn analyze_center_view_action<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    trigger_actions: E::VirtualAddress,
    local_player_id: Operand<'e>,
    is_multiplayer: Operand<'e>,
) -> CenterViewAction<'e, E::VirtualAddress> {
    let mut result = CenterViewAction {
        move_screen: None,
        trigger_current_player: None,
        game_screen_width_bwpx: None,
        game_screen_height_bwpx: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let action_ptr = trigger_actions + E::VirtualAddress::SIZE * 0xa;
    let action = match binary.read_address(action_ptr) {
        Ok(o) => o,
        Err(_) => return result,
    };

    let mut analyzer = CenterViewActionAnalyzer {
        result: &mut result,
        local_player_id,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
    };
    let mut exec = E::initial_state(ctx, binary);
    // Center view has move-screen-over-time logic in single player,
    // this analysis just cares about instant move so set multiplayer = 1
    if let Some(mem) = is_multiplayer.if_memory() {
        exec.write_memory(mem, ctx.const_1());
    }
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, action, exec, Default::default());
    analysis.analyze(&mut analyzer);

    result
}

struct CenterViewActionAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut CenterViewAction<'e, E::VirtualAddress>,
    local_player_id: Operand<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    CenterViewActionAnalyzer<'e, 'acx, 'a, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.result.trigger_current_player.is_none() {
            // Search for jump trigger_current_player == local_player_id
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_neq()
                        .map(|x| (x.0, x.1))
                        .and_if_either_other(|x| x == self.local_player_id);
                    if let Some(result) = result {
                        self.result.trigger_current_player =
                            Some(self.call_tracker.resolve_calls(result));
                    }
                }
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
                _ => (),
            }
        } else {
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg1 = ctrl.resolve_arg(0);
                    let ctx = ctrl.ctx();
                    if let Some(w) = self.screen_size_from_move_screen_arg(ctx, arg1) {
                        let arg2 = ctrl.resolve_arg(1);
                        if let Some(h) = self.screen_size_from_move_screen_arg(ctx, arg2) {
                            self.result.move_screen = Some(dest);
                            self.result.game_screen_width_bwpx = Some(w);
                            self.result.game_screen_height_bwpx = Some(h);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    self.call_tracker.add_call_preserve_esp(ctrl, dest);
                }
            }
        }
    }
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> CenterViewActionAnalyzer<'e, 'acx, 'a, E> {
    fn screen_size_from_move_screen_arg(
        &mut self,
        ctx: OperandCtx<'e>,
        value: Operand<'e>,
    ) -> Option<Operand<'e>> {
        // move_screen arguments are
        // int(loc.l + loc.r) / 2 - int(screen_w) / 2
        // Signed divisions are bit pain to inspect, so mask with 0x7fff_ffff
        let x = Operand::and_masked(value).0.if_arithmetic_sub()?.1;
        let x = Operand::and_masked(ctx.and_const(x, 0x7fff_ffff)).0
            .if_arithmetic_rsh_const(1)?;
        let (l, _) = x.if_arithmetic_sub()?;
        Some(self.call_tracker.resolve_calls(l))
    }
}

pub(crate) fn init_ingame_ui<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    init_statlb: E::VirtualAddress,
    is_replay: Operand<'e>,
) -> InitIngameUi<'e, E::VirtualAddress> {
    let mut result = InitIngameUi {
        init_ingame_ui: None,
        init_obs_ui: None,
        load_consoles: None,
        init_consoles: None,
        get_ui_consoles: None,
        ui_consoles: None,
        observer_ui: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let callers = functions.find_callers(actx, init_statlb);
    let funcs = functions.functions();
    for caller in callers {
        let entry_of_result = entry_of_until(binary, &funcs, caller, |entry| {
            let mut analyzer = InitIngameUiAnalyzer {
                result: &mut result,
                rdata: actx.binary_sections.rdata,
                init_statlb,
                is_replay,
                state: InitIngameUiState::IsReplayJump,
                call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
                console_func_candidates: bumpvec_with_capacity(0x8, bump),
                ui_consoles_state: None,
                entry_of: EntryOf::Retry,
                verify_limit: 0,
                was_replay_func: false,
                was_obs_ui_alloc: false,
                last_call: None,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        match entry_of_result {
            EntryOfResult::Ok(func, ()) | EntryOfResult::Entry(func) => {
                result.init_ingame_ui = Some(func);
                break;
            }
            EntryOfResult::None => (),
        }
    }

    result
}

#[allow(bad_style)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum InitIngameUiState {
    /// Follow jump is_replay == true
    /// (Though keep false path for later)
    IsReplayJump,
    /// Check for subfunction is_replay_or_local_player_obs
    CheckReplayJumpFunc,
    /// Should be first call after is_replay == true
    InitObsUi,
    /// Similar to IsReplayJump, init_obs_ui should also check for
    /// is_replay_or_local_player_obs first
    VerifyInitObsUi_ReplayJump,
    /// Verify from finding large malloc call (0x500+ bytes) which gets stored to
    /// observer_ui global
    VerifyInitObsUi,
    /// Check for the large malloc call if it wasn't inlined in init_obs_ui, and
    /// the child function should return that.
    VerifyInitObsUi_AllocChild,
    /// Take the is_replay == false path and
    /// find load_consoles(this = ui_consoles) followed by init_consoles(this = ui_consoles)
    /// Stop if reaching init_obs_ui call
    UiConsoles,
}

struct InitIngameUiAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut InitIngameUi<'e, E::VirtualAddress>,
    rdata: &'e BinarySection<E::VirtualAddress>,
    is_replay: Operand<'e>,
    init_statlb: E::VirtualAddress,
    entry_of: EntryOf<()>,
    state: InitIngameUiState,
    call_tracker: CallTracker<'acx, 'e, E>,
    console_func_candidates: BumpVec<'acx, (Operand<'e>, E::VirtualAddress)>,
    ui_consoles_state: Option<(E, E::VirtualAddress)>,
    verify_limit: u8,
    was_replay_func: bool,
    was_obs_ui_alloc: bool,
    last_call: Option<E::VirtualAddress>,
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    InitIngameUiAnalyzer<'e, 'acx, 'a, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if dest == self.init_statlb {
                    self.entry_of = EntryOf::Stop;
                    ctrl.end_analysis();
                }
            }
        }
        if self.verify_limit != 0 {
            match *op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    self.verify_limit -= 1;
                    if self.verify_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                }
                _ => (),
            }
        }
        match self.state {
            InitIngameUiState::IsReplayJump | InitIngameUiState::VerifyInitObsUi_ReplayJump => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.state == InitIngameUiState::IsReplayJump {
                            // Check for obs ui here too since the console func is not always
                            // inlined.
                            // If this results in obs ui being found then assume that previous
                            // call was init_consoles and go back to it.
                            if self.check_obs_ui_verify(ctrl, dest) {
                                if let Some(last) = self.last_call {
                                    self.state = InitIngameUiState::UiConsoles;
                                    ctrl.analyze_with_current_state(self, last);
                                }
                                ctrl.end_analysis();
                                return;
                            } else {
                                self.state = InitIngameUiState::IsReplayJump;
                            }
                            self.last_call = Some(dest);
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let jump_if_replay = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|(op, eq_zero)| {
                            let op = Operand::and_masked(op).0;
                            if op == self.is_replay {
                                Some(!eq_zero)
                            } else if let Some(custom) = op.if_custom() {
                                if self.check_is_replay_func(ctrl, custom) {
                                    Some(!eq_zero)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        });
                    if let Some(jump_if_replay) = jump_if_replay {
                        if let Some(to) = ctrl.resolve_va(to) {
                            let (replay_branch, other) = match jump_if_replay {
                                true => (to, ctrl.current_instruction_end()),
                                false => (ctrl.current_instruction_end(), to),
                            };
                            if self.state == InitIngameUiState::IsReplayJump {
                                let state = ctrl.exec_state();
                                self.ui_consoles_state = Some((state.clone(), other));
                                self.state = InitIngameUiState::InitObsUi;
                            } else {
                                self.state = InitIngameUiState::VerifyInitObsUi;
                            }
                            ctrl.continue_at_address(replay_branch);
                        }
                    }
                }
            }
            InitIngameUiState::CheckReplayJumpFunc => {
                if let Operation::Call(..) = *op {
                    ctrl.end_analysis();
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((op, eq_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if op == self.is_replay {
                            self.was_replay_func = true;
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq_zero, to);
                        }
                    }
                } else if let Operation::Return(..) = *op {
                    if self.was_replay_func {
                        let ret = ctrl.resolve_register(0);
                        if ctx.and_const(ret, 0xff) != ctx.const_1() {
                            self.was_replay_func = false;
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            InitIngameUiState::InitObsUi => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.check_obs_ui_verify(ctrl, dest) {
                            ctrl.clear_unchecked_branches();
                            ctrl.end_branch();
                            if let Some((exec, addr)) = self.ui_consoles_state.take() {
                                ctrl.add_branch_with_state(addr, exec, Default::default());
                                self.state = InitIngameUiState::UiConsoles;
                            }
                        } else {
                            self.state = InitIngameUiState::InitObsUi;
                        }
                    }
                }
            }
            InitIngameUiState::VerifyInitObsUi => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.seems_obs_ui_alloc_call(ctrl) {
                            ctrl.clear_unchecked_branches();
                            ctrl.do_call_with_result(ctx.custom(0));
                            return;
                        } else {
                            let this = ctrl.resolve_register(1);
                            if this.if_custom() == Some(0) {
                                // Assume to be constructor call returning this
                                ctrl.do_call_with_result(this);
                                return;
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == E::WORD_SIZE {
                        let value = ctrl.resolve(value);
                        let mem = ctrl.resolve_mem(mem);
                        let (mem_base, mem_offset) = mem.address();
                        if let Some(custom) = value.if_custom() {
                            if mem.is_global() {
                                if custom == 0 {
                                    self.result.observer_ui = Some(ctx.memory(&mem));
                                    ctrl.end_analysis();
                                } else {
                                    // Memory allocation / construction may be in a child
                                    // func, check that
                                    if self.check_obs_ui_alloc_child(ctrl, custom) {
                                        self.result.observer_ui = Some(ctx.memory(&mem));
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        } else if let Some(custom) = ctrl.if_mem_word_offset(value, 0)
                            .and_then(|x| x.if_custom())
                        {
                            // Also accept child function returning ObserverUi **
                            if self.check_obs_ui_alloc_child(ctrl, custom) {
                                self.result.observer_ui = Some(ctx.memory(&mem));
                                ctrl.end_analysis();
                            }
                        } else if mem_base.if_custom() == Some(0) && mem_offset == 0 {
                            if let Some(c) = value.if_constant() {
                                if self.rdata.contains(E::VirtualAddress::from_u64(c)) {
                                    // Assuming inlined constructor which moves vtable
                                    // to observer_ui
                                    // (Could check the value to actually be vtable too though)
                                    self.verify_limit = 0;
                                }
                            }
                        }
                    }
                }
            }
            InitIngameUiState::VerifyInitObsUi_AllocChild => {
                if let Operation::Call(..) = *op {
                    if self.seems_obs_ui_alloc_call(ctrl) {
                        ctrl.do_call_with_result(ctx.custom(1));
                        self.verify_limit = 0;
                    } else {
                        let this = ctrl.resolve_register(1);
                        if this.if_custom() == Some(1) {
                            // Assume to be constructor call returning this
                            ctrl.do_call_with_result(this);
                        }
                    }
                } else if let Operation::Return(..) = *op {
                    // This child function does not return pointer to
                    // obs ui, but writes it to arg1 ObserverUi ** and returns that.
                    // Probably just unique_ptr ABI limitation, so check for both
                    // ObserverUi ** and ObserverUi * in case it ever changes.
                    let ret = ctrl.resolve_register(0);
                    self.was_obs_ui_alloc = ret.if_custom() == Some(1) ||
                        ctrl.read_memory(&ctx.mem_access(ret, 0, E::WORD_SIZE))
                            .if_custom() == Some(1);
                    if self.was_obs_ui_alloc {
                        ctrl.end_analysis();
                    }
                }
            }
            InitIngameUiState::UiConsoles => {
                let check_end = if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if Some(dest) == self.result.init_obs_ui {
                            true
                        } else {
                            let this = ctrl.resolve_register(1);
                            self.console_func_candidates.push((this, dest));
                            self.call_tracker.add_call(ctrl, dest);
                            false
                        }
                    } else {
                        false
                    }
                } else if let Operation::Return(..) = *op {
                    true
                } else {
                    false
                };
                if check_end {
                    // console_func_candidates should contain
                    // two different function calls with same `this`.
                    for (i, &(this, func)) in
                        self.console_func_candidates.iter().enumerate()
                    {
                        if this.if_custom().is_some() || is_global(this) {
                            if let Some(&(_, other)) =
                                self.console_func_candidates[i + 1..].iter()
                                .find(|x| x.0 == this && x.1 != func)
                            {
                                self.result.load_consoles = Some(func);
                                self.result.init_consoles = Some(other);
                                self.result.ui_consoles =
                                    Some(self.call_tracker.resolve_calls(this));
                                if let Some(c) = this.if_custom() {
                                    if let Some(func) = self.call_tracker.custom_id_to_func(c) {
                                        self.result.get_ui_consoles = Some(func);
                                    }
                                }
                            }
                        }
                    }
                    ctrl.end_analysis();
                    return;
                }
            }
        }
    }
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> InitIngameUiAnalyzer<'e, 'acx, 'a, E> {
    /// Returns true if this is a function returning nonzero constant when
    /// is_replay is set. (In effect called for is_replay_or_local_user_obs though)
    fn check_is_replay_func(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, custom: u32) -> bool {
        self.call_tracker.custom_id_to_func(custom)
            .and_then(|func| {
                let old_state = self.state;
                self.state = InitIngameUiState::CheckReplayJumpFunc;
                let old_verify_limit = self.verify_limit;
                self.verify_limit = 4;
                self.was_replay_func = false;
                ctrl.analyze_with_current_state(self, func);
                self.state = old_state;
                self.verify_limit = old_verify_limit;
                Some(self.was_replay_func)
            })
            .unwrap_or(false)
    }

    fn check_obs_ui_verify(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: E::VirtualAddress,
    ) -> bool {
        self.state = InitIngameUiState::VerifyInitObsUi_ReplayJump;
        let old_verify_limit = self.verify_limit;
        self.verify_limit = 10;
        ctrl.analyze_with_current_state(self, dest);
        self.verify_limit = old_verify_limit;
        if self.result.observer_ui.is_some() {
            self.result.init_obs_ui = Some(dest);
            self.entry_of = EntryOf::Ok(());
            true
        } else {
            false
        }
    }

    /// Returns true if `custom` is calling a function that seems like allocating obs ui
    /// and returning it
    fn check_obs_ui_alloc_child(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        custom: u32,
    ) -> bool {
        self.call_tracker.custom_id_to_func(custom)
            .and_then(|func| {
                let old_state = self.state;
                self.was_obs_ui_alloc = false;
                self.state = InitIngameUiState::VerifyInitObsUi_AllocChild;
                let old_verify_limit = self.verify_limit;
                self.verify_limit = 4;
                ctrl.analyze_with_current_state(self, func);
                self.state = old_state;
                self.verify_limit = old_verify_limit;
                Some(self.was_obs_ui_alloc)
            })
            .unwrap_or(false)
    }

    fn seems_obs_ui_alloc_call(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        let arg1 = ctrl.resolve_arg(0);
        if let Some(c) = arg1.if_constant() {
            c > 0x400 && c < 0x1000
        } else {
            false
        }
    }
}

pub(crate) fn analyze_game_screen_lclick<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    is_targeting: Operand<'e>,
    is_placing_building: Operand<'e>,
    global_event_handlers: Operand<'e>,
    game_screen_lclick: E::VirtualAddress,
) -> GameScreenLClick<'e, E::VirtualAddress> {
    let mut result = GameScreenLClick {
        stop_targeting: None,
        place_building: None,
        select_mouse_up: None,
        select_mouse_move: None,
        clip_cursor: None,
        game_screen_rect_winpx: None,
        on_clip_cursor_end: None,
        select_start_x: None,
        select_start_y: None,
        is_selecting: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = GameScreenLClickAnalyzer {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        is_targeting,
        is_placing_building,
        global_event_handlers_first: ctx.mem_access(global_event_handlers, 0, E::WORD_SIZE),
        state: GameScreenLClickState::IsTargetingJump,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        stop_targeting_entry: E::VirtualAddress::from_u64(0),
        stop_targeting_inline_depth: 0,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_lclick);
    analysis.analyze(&mut analyzer);

    result
}

#[allow(bad_style)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum GameScreenLClickState {
    /// Check for is_targeting jump, follow true branch
    IsTargetingJump,
    /// Should be the first branch afterwards
    StopTargeting,
    /// stop_targeting should write `is_targeting = 0` at start
    VerifyStopTargeting,
    /// Same but for is_placing_building
    IsPlacingBuildingJump,
    /// place_building(0, 0, 1)
    PlaceBuilding,
    /// Next call, should have clip_cursor(game_screen_rect_winpx)
    ClipCursor,
    /// Writes to global variables:
    /// clip_end_callback = func
    ///     func should just write is_selecting = 0
    /// global_event_handlers[5] = select_mouse_up
    /// global_event_handlers[3] = select_mouse_move
    /// select_start_x = arg1.x12
    /// select_start_y = arg1.x14
    GlobalWrites,
    VerifyClipEndCallback,
}

struct GameScreenLClickAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut GameScreenLClick<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    is_targeting: Operand<'e>,
    is_placing_building: Operand<'e>,
    global_event_handlers_first: MemAccess<'e>,
    state: GameScreenLClickState,
    call_tracker: CallTracker<'acx, 'e, E>,
    /// stop_targeting may be just jump to another instruction, register
    /// the jump target as real stop_targeting.
    stop_targeting_entry: E::VirtualAddress,
    stop_targeting_inline_depth: u8,
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    GameScreenLClickAnalyzer<'e, 'acx, 'a, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            GameScreenLClickState::IsTargetingJump |
                GameScreenLClickState::IsPlacingBuildingJump =>
            {
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.call_tracker.add_call(ctrl, dest);
                        }
                    }
                    Operation::Jump { condition, to } => {
                        let condition = self.call_tracker.resolve_calls(ctrl.resolve(condition));
                        let compare = if self.state == GameScreenLClickState::IsTargetingJump {
                            self.is_targeting
                        } else {
                            self.is_placing_building
                        };
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .filter(|x| x.0 == compare)
                            .map(|x| x.1);
                        if let Some(jump_if_zero) = ok {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(jump_if_zero, to);
                            if self.state == GameScreenLClickState::IsTargetingJump {
                                self.state = GameScreenLClickState::StopTargeting;
                            } else {
                                self.state = GameScreenLClickState::PlaceBuilding;
                            }
                        }
                    }
                    _ => (),
                }
            }
            GameScreenLClickState::StopTargeting | GameScreenLClickState::PlaceBuilding => {
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let ok = if self.state == GameScreenLClickState::StopTargeting {
                                self.verify_stop_targeting(ctrl, dest)
                            } else {
                                Some(dest).filter(|_| {
                                    let zero = ctx.const_0();
                                    let one = ctx.const_1();
                                    [zero, zero, one]
                                        .iter().enumerate()
                                        .all(|(i, &expected)| {
                                            ctrl.resolve_arg_u8(i as u8) == expected
                                        })
                                })
                            };
                            if let Some(dest) = ok {
                                if self.state == GameScreenLClickState::StopTargeting {
                                    self.result.stop_targeting = Some(dest);
                                    self.state = GameScreenLClickState::IsPlacingBuildingJump;
                                } else {
                                    self.result.place_building = Some(dest);
                                    self.state = GameScreenLClickState::ClipCursor;
                                }
                            }
                            self.call_tracker.add_call(ctrl, dest);
                        }
                    }
                    Operation::Jump { .. } => {
                        // Go back
                        self.state = if self.state == GameScreenLClickState::StopTargeting {
                            GameScreenLClickState::IsTargetingJump
                        } else {
                            GameScreenLClickState::IsPlacingBuildingJump
                        };
                        self.operation(ctrl, op);
                    }
                    _ => (),
                }
            }
            GameScreenLClickState::VerifyStopTargeting => {
                match *op {
                    Operation::Call(..) | Operation::Return(..) => {
                        // Sometimes depending on inlining, this calls
                        // stop_targeting_inner1(0), where arg1 selects
                        // whether to return targeted_order_ground or _unit
                        // But it is only caller and discards the value.
                        // And then stop_targeting_inner1 can even call stop_targeting_inner2..
                        if self.stop_targeting_inline_depth < 2 {
                            if let Operation::Call(dest) = *op {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    let this_func = self.stop_targeting_entry;
                                    self.stop_targeting_inline_depth += 1;
                                    let ok = self.verify_stop_targeting(ctrl, dest).is_some();
                                    self.stop_targeting_inline_depth -= 1;
                                    if ok {
                                        self.stop_targeting_entry = this_func;
                                        ctrl.end_analysis();
                                        return;
                                    }
                                }
                            }
                        }
                        self.stop_targeting_entry = E::VirtualAddress::from_u64(0);
                        ctrl.end_analysis();
                    }
                    Operation::Move(DestOperand::Memory(ref mem), value) => {
                        let value = ctrl.resolve(value);
                        if value == ctx.const_0() {
                            let mem = ctrl.resolve_mem(mem);
                            if Some(&mem) == self.is_targeting.if_memory() {
                                // Ok; not zeroing stop_targeting_entry
                                // signals to caller that this was success.
                                ctrl.end_analysis();
                            }
                        }
                    }
                    Operation::Jump { condition, to } => {
                        if ctrl.address() == self.stop_targeting_entry &&
                            condition == ctx.const_1()
                        {
                            if let Some(to) = ctrl.resolve_va(to) {
                                // Func just redirects to another, consider
                                // the redirected-to function the real stop_targeting
                                self.stop_targeting_entry = to;
                                return;
                            }
                        }
                        // Other kind of jump; fail analysis unless it is assertion
                        // `is_targeting != 0` or `command_user == unique_player_id`
                        let condition = ctrl.resolve(condition);
                        let seems_assert = condition.if_arithmetic_eq_neq()
                            .and_then(|(l, r, eq)| {
                                if r == ctx.const_0() && l == self.is_targeting {
                                    Some(!eq)
                                } else if l.if_mem32().is_some() &&
                                    r.if_mem32().is_some() &&
                                    is_global(l) && is_global(r)
                                {
                                    Some(eq)
                                } else {
                                    None
                                }
                            });
                        if let Some(eq) = seems_assert {
                            ctrl.continue_at_eq_address(eq, to);
                        } else {
                            self.stop_targeting_entry = E::VirtualAddress::from_u64(0);
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
            GameScreenLClickState::ClipCursor => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        if is_global(arg1) {
                            self.result.game_screen_rect_winpx = Some(arg1);
                            self.result.clip_cursor = Some(dest);
                            self.state = GameScreenLClickState::GlobalWrites;
                        }
                    }
                }
            }
            GameScreenLClickState::GlobalWrites => {
                if let Operation::Move(DestOperand::Memory(ref dest), value) = *op {
                    let mut result_changed = false;
                    let dest = ctrl.resolve_mem(dest);
                    let value = ctrl.resolve(value);
                    if dest.size == E::WORD_SIZE {
                        if let Some(value) = value.if_constant() {
                            let value = E::VirtualAddress::from_u64(value);
                            if dest == self.global_event_handlers_first.with_offset(
                                E::VirtualAddress::SIZE as u64 * 3
                            ) {
                                self.result.select_mouse_move = Some(value);
                                result_changed = true;
                            } else if dest == self.global_event_handlers_first.with_offset(
                                E::VirtualAddress::SIZE as u64 * 5
                            ) {
                                self.result.select_mouse_up = Some(value);
                                result_changed = true;
                            } else if self.result.is_selecting.is_none() {
                                if self.verify_clip_end_callback(ctrl, value) {
                                    self.result.on_clip_cursor_end = Some(ctx.memory(&dest));
                                    result_changed = true;
                                }
                            }
                        }
                    }
                    if !result_changed {
                        if let Some(mem) = value.if_mem16() {
                            let (base, offset) = mem.address();
                            if base == self.arg_cache.on_entry(0) && dest.is_global() {
                                let xy_offset = E::struct_layouts().event_mouse_xy();
                                if offset == xy_offset {
                                    self.result.select_start_x = Some(ctx.memory(&dest));
                                    result_changed = true;
                                } else if offset == xy_offset + 2 {
                                    self.result.select_start_y = Some(ctx.memory(&dest));
                                    result_changed = true;
                                }
                            }
                        }
                    }
                    if result_changed {
                        let done = self.result.select_mouse_up.is_some() &&
                            self.result.select_mouse_move.is_some() &&
                            self.result.select_start_x.is_some() &&
                            self.result.select_start_y.is_some() &&
                            self.result.is_selecting.is_some();
                        if done {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            GameScreenLClickState::VerifyClipEndCallback => {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        self.result.is_selecting = None;
                        ctrl.end_analysis();
                    }
                    Operation::Move(DestOperand::Memory(ref mem), value) => {
                        let value = ctrl.resolve(value);
                        if value == ctx.const_0() {
                            if self.result.is_selecting.is_some() {
                                self.result.is_selecting = None;
                                ctrl.end_analysis();
                            } else {
                                self.result.is_selecting =
                                    Some(ctx.memory(&ctrl.resolve_mem(mem)));
                            }
                        }
                    }
                    _ => (),
                }
            }
        }
    }
}

impl<'e: 'acx, 'acx, 'a, E: ExecutionState<'e>> GameScreenLClickAnalyzer<'e, 'acx, 'a, E> {
    fn verify_stop_targeting(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: E::VirtualAddress,
    ) -> Option<E::VirtualAddress> {
        let old_state = self.state;
        self.state = GameScreenLClickState::VerifyStopTargeting;
        self.stop_targeting_entry = dest;
        ctrl.analyze_with_current_state(self, dest);
        self.state = old_state;
        Some(self.stop_targeting_entry).filter(|x| x.as_u64() != 0)
    }

    fn verify_clip_end_callback(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: E::VirtualAddress,
    ) -> bool {
        let old_state = self.state;
        self.state = GameScreenLClickState::VerifyClipEndCallback;
        ctrl.analyze_with_current_state(self, dest);
        self.state = old_state;
        self.result.is_selecting.is_some()
    }
}

pub(crate) fn analyze_select_mouse_up<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    reset_ui_event_handlers: E::VirtualAddress,
    game_screen_lclick: E::VirtualAddress,
) -> SelectMouseUp<E::VirtualAddress> {
    let mut result = SelectMouseUp {
        decide_cursor_type: None,
        set_current_cursor_type: None,
        select_units: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let mut analyzer = SelectMouseUpAnalyzer {
        result: &mut result,
        reset_ui_event_handlers,
        state: SelectMouseUpState::ResetUiEventHandlers,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        inline_depth: 0,
        eq_one_comparisons: bumpvec_with_capacity(0x20, bump),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_lclick);
    analysis.analyze(&mut analyzer);

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SelectMouseUpState {
    /// select_mouse_up should just do
    /// ..
    /// reset_ui_event_handlers();
    /// set_current_cursor_type(decide_cursor_type(), 0u8);
    /// just taking first call which takes another call as an argument
    /// ..
    ResetUiEventHandlers,
    SetCurrentCursorType,
    /// Find func(x, _, 1, 1), if it calls another func(x, _, 1, 1)
    /// then use that.
    /// x should be a value that was compared against 1 before
    SelectUnits,
}

struct SelectMouseUpAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut SelectMouseUp<E::VirtualAddress>,
    reset_ui_event_handlers: E::VirtualAddress,
    state: SelectMouseUpState,
    call_tracker: CallTracker<'acx, 'e, E>,
    inline_depth: u8,
    eq_one_comparisons: BumpVec<'acx, Operand<'e>>,
}

impl<'e, 'acx, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    SelectMouseUpAnalyzer<'e, 'acx, 'a, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            SelectMouseUpState::ResetUiEventHandlers |
                SelectMouseUpState::SetCurrentCursorType =>
            {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        match self.state {
                            SelectMouseUpState::ResetUiEventHandlers => {
                                if dest == self.reset_ui_event_handlers {
                                    self.state = SelectMouseUpState::SetCurrentCursorType;
                                    ctrl.clear_unchecked_branches();
                                }
                            }
                            _ => {
                                let arg1 = ctrl.resolve_arg(0);
                                if let Some(c) = Operand::and_masked(arg1).0.if_custom() {
                                    if let Some(func) = self.call_tracker.custom_id_to_func(c) {
                                        self.result.decide_cursor_type = Some(func);
                                        self.result.set_current_cursor_type = Some(dest);
                                        self.state = SelectMouseUpState::SelectUnits;
                                    }
                                }
                                self.call_tracker.add_call(ctrl, dest);
                            }
                        }
                    }
                }
            }
            SelectMouseUpState::SelectUnits => {
                let ctx = ctrl.ctx();
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg3 = ctrl.resolve_arg_u8(2);
                        let arg4 = ctrl.resolve_arg_u8(3);
                        let ok = arg3 == ctx.const_1() &&
                            arg4 == ctx.const_1() &&
                            self.eq_one_comparisons.contains(&Operand::and_masked(arg1).0);
                        if ok {
                            if self.inline_depth < 3 {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                            }
                            if self.result.select_units.is_none() {
                                self.result.select_units = Some(dest);
                                ctrl.end_analysis();
                                return;
                            }
                        } else {
                            // Allow inlining once to multi_select(global_arr)
                            if self.inline_depth == 0 {
                                if is_global(arg1) {
                                    self.inline_depth += 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                    if self.result.select_units.is_some() {
                                        ctrl.end_analysis();
                                        return;
                                    }
                                }
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let eq_one = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1 == ctx.const_1())
                        .map(|x| x.0);
                    if let Some(eq_one) = eq_one {
                        let no_mask = Operand::and_masked(eq_one).0;
                        if no_mask.if_custom().is_some() {
                            self.eq_one_comparisons.push(no_mask);
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_update_game_screen_size<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    update_game_screen_size: E::VirtualAddress,
) -> UpdateGameScreenSize<'e> {
    let mut result = UpdateGameScreenSize {
        update_mode: None,
        game_screen_height_ratio: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = UpdateGameScreenSizeAnalyzer::<E> {
        result: &mut result,
        state: UpdateGameScreenSizeState::UpdateMode,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, update_game_screen_size);
    analysis.analyze(&mut analyzer);

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum UpdateGameScreenSizeState {
    /// Find update_mode == 2 jump, follow that
    UpdateMode,
    /// match against f32 `x / (y * ratio)`
    HeightRatio,
}

struct UpdateGameScreenSizeAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    result: &'a mut UpdateGameScreenSize<'e>,
    state: UpdateGameScreenSizeState,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    UpdateGameScreenSizeAnalyzer<'e, 'a, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            UpdateGameScreenSizeState::UpdateMode => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(2) && is_global(x.0));
                    if let Some((var, _, eq)) = ok {
                        self.result.update_mode = Some(var);
                        self.state = UpdateGameScreenSizeState::HeightRatio;
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_eq_address(eq, to);
                    }
                }
            }
            UpdateGameScreenSizeState::HeightRatio => {
                if let Operation::Move(_, value) = *op {
                    if let Some((_, r)) = if_f32_div(value) {
                        let r = ctrl.resolve(r);
                        if let Some((l, r)) = r.if_arithmetic_float(ArithOpType::Mul) {
                            let mut result = None;
                            if is_global(l) {
                                if !is_global(r) {
                                    result = Some(l);
                                }
                            } else if is_global(r) {
                                if !is_global(l) {
                                    result = Some(r);
                                }
                            }
                            if let Some(result) = result {
                                self.result.game_screen_height_ratio = Some(result);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_talking_portrait_action<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    trigger_actions: E::VirtualAddress,
) -> TalkingPortrait<E::VirtualAddress> {
    let mut result = TalkingPortrait {
        trigger_talking_portrait: None,
        show_portrait: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let action_ptr = trigger_actions + E::VirtualAddress::SIZE * 0x1d;
    let action = match binary.read_address(action_ptr) {
        Ok(o) => o,
        Err(_) => return result,
    };

    let mut analyzer = TalkingPortraitAnalyzer::<E> {
        result: &mut result,
        state: TalkingPortraitState::Init,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, action);
    analysis.analyze(&mut analyzer);

    result
}

struct TalkingPortraitAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    result: &'a mut TalkingPortrait<E::VirtualAddress>,
    state: TalkingPortraitState,
}

enum TalkingPortraitState {
    /// Find trigger_talking_portrait(_, -1, _, -1)
    Init,
    /// Inside trigger_talking_portrait, find show_portrait(0, _, 2u32)
    ShowPortrait,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for TalkingPortraitAnalyzer<'e, 'a, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                match self.state {
                    TalkingPortraitState::Init => {
                        let ok = ctrl.resolve_arg_u32(1).if_constant() == Some(0xffff_ffff) &&
                            ctrl.resolve_arg_u32(2).if_constant() == Some(0xffff_ffff);
                        if ok {
                            self.result.trigger_talking_portrait = Some(dest);
                            self.state = TalkingPortraitState::ShowPortrait;
                            ctrl.analyze_with_current_state(self, dest);
                            ctrl.end_analysis();
                        }
                    }
                    TalkingPortraitState::ShowPortrait => {
                        let ctx = ctrl.ctx();
                        let ok = ctrl.resolve_arg(0) == ctx.const_0() &&
                            ctrl.resolve_arg_u32(2).if_constant() == Some(2);
                        if ok {
                            self.result.show_portrait = Some(dest);
                            ctrl.end_analysis();
                        } else {
                            ctrl.skip_call_preserve_esp();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_show_portrait<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    show_portrait: E::VirtualAddress,
) -> ShowPortrait<'e> {
    let mut result = ShowPortrait {
        videos: None,
        talking_active: None,
        video_id: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = ShowPortraitAnalyzer::<E> {
        result: &mut result,
        videos_candidate: None,
        video_id_candidate: None,
        state: ShowPortraitState::FlagCheck,
        arg_cache: &actx.arg_cache,
        check_show_talking_portrait_inline: true,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, show_portrait);
    analysis.analyze(&mut analyzer);

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum ShowPortraitState {
    /// Follow arg2 != 0x52 branch
    FlagCheck,
    /// Find arg3 == 2 jump, follow it
    ArgJump,
    /// Should find if !videos { delete_videos; videos = null } block
    Videos,
    /// Should have x == video_id jump, then later on write something to video_id
    /// And video_id should be Mem8
    /// At the same time search for talking_active = 1 write
    /// May have to inline to show_talking_portrait(a1 = a2)
    VideoId,
}

struct ShowPortraitAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    result: &'a mut ShowPortrait<'e>,
    videos_candidate: Option<&'e MemAccess<'e>>,
    video_id_candidate: Option<&'e MemAccess<'e>>,
    state: ShowPortraitState,
    arg_cache: &'a ArgCache<'e, E>,
    check_show_talking_portrait_inline: bool,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for ShowPortraitAnalyzer<'e, 'a, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            ShowPortraitState::FlagCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(0x52))
                        .map(|x| x.2);
                    if let Some(eq) = ok {
                        self.state = ShowPortraitState::ArgJump;
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_neq_address(eq, to);
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == E::WORD_SIZE {
                        if ctrl.resolve(value) == ctx.const_0() {
                            // Videos object does have a branch where it is cleared before
                            // arg3 jump too, just ignore it and prevent it from making
                            // the memory location undef
                            ctrl.skip_operation();
                        }
                    }
                }
            }
            ShowPortraitState::ArgJump => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(2))
                        .filter(|x| {
                            ctx.and_const(x.0, 0xffff) ==
                                ctx.and_const(self.arg_cache.on_entry(2), 0xffff)
                        })
                        .map(|x| x.2);
                    if let Some(eq) = ok {
                        self.state = ShowPortraitState::Videos;
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_eq_address(eq, to);
                    }
                }
            }
            ShowPortraitState::Videos => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((op, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if let Some(mem) = ctrl.if_mem_word(op) {
                            self.videos_candidate = Some(mem);
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq, to);
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == E::WORD_SIZE {
                        if let Some(cand) = self.videos_candidate {
                            if ctrl.resolve(value) == ctx.const_0() &&
                                ctrl.resolve_mem(mem) == *cand
                            {
                                ctrl.skip_operation();
                                self.result.videos = Some(ctx.memory(cand));
                                self.state = ShowPortraitState::VideoId;
                            }
                        }
                    }
                }
            }
            ShowPortraitState::VideoId => {
                if let Operation::Jump { condition, .. } = *op {
                    self.check_show_talking_portrait_inline = false;
                    let condition = ctrl.resolve(condition);
                    if let Some((a, b, _)) = condition.if_arithmetic_eq_neq() {
                        if let Some((mem, _)) = Operand::either(a, b, |x| x.if_mem8()) {
                            self.video_id_candidate = Some(mem);
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if let Some(cand) = self.video_id_candidate {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            let value = ctrl.resolve(value);
                            if mem == *cand {
                                if value.if_constant().is_none() {
                                    single_result_assign(
                                        Some(ctx.memory(&mem)),
                                        &mut self.result.video_id,
                                    );
                                }
                            } else if value == ctx.const_1() {
                                single_result_assign(
                                    Some(ctx.memory(&mem)),
                                    &mut self.result.talking_active,
                                );
                            }
                            if self.result.video_id.is_some() &&
                                self.result.talking_active.is_some()
                            {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.check_show_talking_portrait_inline {
                        self.check_show_talking_portrait_inline = false;
                        let inline = ctrl.resolve_arg_u16(0) ==
                            ctx.and_const(self.arg_cache.on_entry(1), 0xffff);

                        if inline {
                            if let Some(dest) = ctrl.resolve_va(dest) {
                                ctrl.analyze_with_current_state(self, dest);
                                // talking_active is still at level 0, continue analysis
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn find_load_all_cursors<'acx, 'e, E: ExecutionState<'e>>(
    actx: &'acx AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> LoadAllCursors<E::VirtualAddress> {
    let mut result = LoadAllCursors {
        load_all_cursors: None,
        load_ddsgrp_cursor: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let str_refs = functions.string_refs(actx, b"cursor\\");
    let funcs = functions.functions();
    for str_ref in &str_refs {
        entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = LoadAllCursorsAnalyzer::<E> {
                entry,
                use_address: str_ref.use_address,
                result: &mut result,
                entry_of: EntryOf::Retry,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        if result.load_all_cursors.is_some() {
            break;
        }
    }
    result
}

struct LoadAllCursorsAnalyzer<'e, 'a, E: ExecutionState<'e>> {
    entry: E::VirtualAddress,
    use_address: E::VirtualAddress,
    result: &'a mut LoadAllCursors<E::VirtualAddress>,
    entry_of: EntryOf<()>,
}

impl<'e, 'a, E: ExecutionState<'e>> scarf::Analyzer<'e> for LoadAllCursorsAnalyzer<'e, 'a, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.use_address.as_u64().wrapping_sub(ctrl.address().as_u64()) < 0x10 {
            self.entry_of = EntryOf::Stop;
        }
        if let Operation::Call(dest) = *op {
            let ok = if E::VirtualAddress::SIZE == 4 {
                ctrl.resolve_arg_u8(1).if_mem8().is_some() &&
                    ctrl.resolve_arg(2).if_mem32().is_some() &&
                    ctrl.resolve_arg(3).if_mem32().is_some() &&
                    ctrl.resolve_arg_u32(4).if_constant() == Some(0xa)
            } else {
                ctrl.resolve_arg_u8(1).if_mem8().is_some() &&
                    ctrl.resolve_arg(2).if_mem64().is_some() &&
                    ctrl.resolve_arg_u32(3).if_constant() == Some(0xa)
            };
            if ok && let Some(dest) = ctrl.resolve_va(dest) {
                self.result.load_all_cursors = Some(self.entry);
                self.result.load_ddsgrp_cursor = Some(dest);
                self.entry_of = EntryOf::Ok(());
                ctrl.end_analysis();
            }
        }
    }
}

pub(crate) fn cursor_scale_factor<'acx, 'e, E: ExecutionState<'e>>(
    actx: &'acx AnalysisCtx<'e, E>,
    load_all_cursors: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let exec = E::initial_state(ctx, binary);
    let mut analysis = FuncAnalysis::with_state(binary, ctx, load_all_cursors, exec);
    let mut analyzer = CursorScaleFactorAnalyzer {
        result: None,
        state: CursorScaleFactorState::FindMax,
        phantom: std::marker::PhantomData,
        max_dest: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct CursorScaleFactorAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    state: CursorScaleFactorState,
    phantom: std::marker::PhantomData<E>,
    max_dest: Option<MemAccess<'e>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum CursorScaleFactorState {
    FindMax,
    FindStore,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CursorScaleFactorAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;

    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let binary = ctrl.binary();

        match self.state {
            // Look for a max(value, 0.25f)
            CursorScaleFactorState::FindMax => {
                if let Operation::ConditionalMove(DestOperand::Memory(ref dest), src, cond) = *op {
                    let condition = ctrl.resolve(cond);
                    if condition.if_arithmetic_float(ArithOpType::GreaterThan).is_none() {
                        return;
                    }

                    let r = ctrl.resolve(src);
                    let Some(constant) = r.if_constant_or_read_binary(binary) else {
                        return;
                    };

                    // 0.25f
                    if constant == 0x3e800000 {
                        let dest = ctrl.resolve_mem(dest);
                        self.max_dest = Some(dest);
                        self.state = CursorScaleFactorState::FindStore;
                    }
                }
            }
            // Look for storing that result in a global memory location
            CursorScaleFactorState::FindStore => {
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op
                    && mem.size == MemAccessSize::Mem32
                    && mem.is_global()
                    && let Some(value) = value.if_mem32()
                {
                    let value = ctrl.resolve_mem(value);

                    if self.max_dest == Some(value) {
                        let result = ctrl.resolve_mem(mem);
                        self.result = Some(ctx.memory(&result));
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

pub(crate) fn cursor_dimension_patch<'acx, 'e, E: ExecutionState<'e>>(
    actx: &'acx AnalysisCtx<'e, E>,
    load_ddsgrp_cursor: E::VirtualAddress,
) -> Option<Patch<E::VirtualAddress>> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    // This function has a large branch depending on arg1 bool, the patch point
    // is after that so make sure to walk through just one branch to save bit of time.
    // (Both branches of if/else are big though)
    let mut exec = E::initial_state(ctx, binary);
    exec.move_resolved(
        &DestOperand::from_oper(actx.arg_cache.on_entry(1)),
        ctx.constant(0),
    );
    let mut analysis = FuncAnalysis::with_state(binary, ctx, load_ddsgrp_cursor, exec);
    let mut analyzer = CursorDimensionPatchAnalyzer {
        result: None,
        state: CursorDimensionPatchState::Patch,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct CursorDimensionPatchAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Patch<E::VirtualAddress>>,
    state: CursorDimensionPatchState,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum CursorDimensionPatchState {
    /// Find jump `41 > x`, patch it to always jump.
    Patch,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CursorDimensionPatchAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            CursorDimensionPatchState::Patch => {
                if let Operation::Jump { condition, .. } = *op {
                    let binary = ctrl.binary();
                    let condition = ctrl.resolve(condition);
                    let mut ok = condition.if_arithmetic_gt()
                        .is_some_and(|(l, _)| l.if_constant() == Some(0x41));
                    if !ok {
                        // Some old versions used float comparison which is lot messier to unpack:
                        // or of 3 checks, one of which is f32 cmp (Mem32[x] > _) where
                        // x is rdata address to constant 64.0
                        let check_f32_cmp = |op: Operand<'_>| {
                            if let Some((l, _)) =
                                    op.if_arithmetic_float(ArithOpType::GreaterThan) &&
                                let Some(mem) = l.if_mem32() &&
                                let Some(addr) = mem.if_constant_address() &&
                                let Ok(value) =
                                    binary.read_u32(E::VirtualAddress::from_u64(addr)) &&
                                value == 0x4280_0000
                            {
                                true
                            } else {
                                false
                            }
                        };
                        let mut op = condition;
                        while let Some((l, r)) = op.if_arithmetic_or() {
                            if check_f32_cmp(r) {
                                ok = true;
                                break;
                            }
                            op = l;
                        }
                        if !ok {
                            ok = check_f32_cmp(op);
                        }
                    }
                    if ok {
                        let address = ctrl.address();
                        if let Some(patch) = make_jump_unconditional(binary, address) {
                            self.result = Some(Patch {
                                address,
                                data: Vec::from(&patch[..]),
                            });
                        }
                        ctrl.end_analysis();
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    // Ignore moves of 0 to stack variables as that's sometimes used in vec
                    // init, and then that vec size is changed in a function we don't see to
                    // and we don't reach correct point in analysis due to that.
                    let value = ctrl.resolve(value);
                    let ctx = ctrl.ctx();
                    if value == ctx.const_0() {
                        let mem = ctrl.resolve_mem(mem);
                        if is_stack_memory::<E::VirtualAddress>(&mem, ctx) {
                            ctrl.skip_operation();
                            ctrl.write_memory(&mem, ctx.new_undef());
                        }
                    }
                }
            }
        }
    }
}

fn is_stack_memory<'e, Va: VirtualAddress>(mem: &MemAccess<'e>, ctx: OperandCtx<'e>) -> bool {
    let base = mem.address().0;
    if base == ctx.register(4) {
        true
    } else if Va::SIZE == 4 {
        // May be stack pointer which was aligned to 16 bytes
        // (rsp - x) & ffff_fff8 or such
        if let Some((l, r)) = base.if_and_with_const() &&
            r & 0xffff_fff0 == 0xffff_fff0 &&
            let Some((l, _)) = l.if_sub_with_const() &&
            l == ctx.register(4)
        {
            true
        } else {
            false
        }
    } else {
        false
    }
}
