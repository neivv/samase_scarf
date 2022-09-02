use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, Operation, Rva};
use scarf::operand::{OperandCtx};

use crate::{
    AnalysisCtx, ArgCache, EntryOf, EntryOfResult, entry_of_until, FunctionFinder,
};
use crate::analysis_state::{
    AnalysisState, StateEnum, MiscClientSideAnalyzerState, HandleTargetedClickState,
};
use crate::call_tracker::CallTracker;
use crate::hash_map::HashMap;
use crate::struct_layouts;
use crate::util::{
    ControlExt, OperandExt, OptionExt, single_result_assign, if_arithmetic_eq_neq, is_global,
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

// Candidates are either a global ref with Some(global), or a call with None
fn game_screen_rclick_inner<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    candidates: &[(E::VirtualAddress, Option<E::VirtualAddress>)],
) -> ResultOrEntries<'acx, (E::VirtualAddress, Operand<'e>), E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    let mut result: Option<(E::VirtualAddress, Operand<'e>)> = None;
    let mut entries = BumpVec::new_in(bump);
    for &(middle_of_func, global_addr) in candidates {
        let res = entry_of_until(binary, funcs, middle_of_func, |entry| {
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
                        funcs,
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
                            break;
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
                    if let Operation::Move(_, ref val, _) = *op {
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
            Operation::Move(_, val, _) => {
                if !self.mov_u32_max_seen && self.first_branch {
                    let val = ctrl.resolve(val);
                    if val.if_constant().map(|x| x as u32) == Some(u32::max_value()) {
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
    struct Analyzer<'a, 'b, E: ExecutionState<'a>> {
        result: Option<E::VirtualAddress>,
        args: &'b ArgCache<'a, E>,
    }

    impl<'a, 'b, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation<'a>) {
            match *op {
                Operation::Jump { .. } => {
                    ctrl.end_analysis();
                }
                Operation::Call(to) => {
                    let to = ctrl.resolve(to);
                    let arg1 = ctrl.resolve(self.args.on_call(0)).unwrap_sext();
                    let arg2 = ctrl.resolve(self.args.on_call(1)).unwrap_sext();
                    if let Some(dest) = to.if_constant() {
                        if arg1.if_mem16().is_some() && arg2.if_mem16().is_some() {
                            self.result = Some(E::VirtualAddress::from_u64(dest));
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
    let mut analyzer = Analyzer {
        result: None,
        args: &analysis.arg_cache,
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
            let arg2 = ctrl.resolve(self.args.on_call(1));
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
                let exec_state = ctrl.exec_state();
                exec_state.move_to(&DestOperand::Register64(0), self.ctx.const_0());
                return;
            }
            match *op {
                Operation::Call(to) => {
                    let to = ctrl.resolve(to);
                    if let Some(dest) = to.if_constant() {
                        if !self.is_outside_game_screen_seen {
                            if dest == self.is_outside_game_screen.as_u64() {
                                self.is_outside_game_screen_seen = true;
                                self.set_eax_to_zero = true;
                            }
                            return;
                        }

                        if self.depth == 0 {
                            if self.is_event_pos_in_game_coords_call(ctrl) {
                                self.depth += 1;
                                ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                                ctrl.skip_operation();
                                self.depth -= 1;
                            }
                        } else if self.depth == 3 {
                            ctrl.end_analysis();
                            return;
                        } else {
                            self.depth += 1;
                            ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                            ctrl.skip_operation();
                            self.depth -= 1;
                        }
                        if self.result.screen_x.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
                Operation::Move(_, val, None) => {
                    if self.depth != 0 {
                        let val = ctrl.resolve(val);
                        let result = Self::check_move(val);
                        if let Some((screen_coord, scale, struct_offset)) = result {
                            if struct_offset ==
                                struct_layouts::event_mouse_xy::<E::VirtualAddress>() as u32
                            {
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
    let result = game_screen_rclick_inner(analysis, functions, &uses);
    let result = match result {
        ResultOrEntries::Entries(entries) => {
            let callers = entries.iter().flat_map(|&f| {
                functions.find_callers(analysis, f).into_iter().map(|x| (x, None))
            });
            let callers = BumpVec::from_iter_in(callers, bump);
            game_screen_rclick_inner(analysis, functions, &callers)
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
    let vtables = vtables.vtables_starting_with(b".?AVOptionsMenuPopup@glues@@\0")
        .map(|x| x.address);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
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

impl<'a, 'acx, 'e, E: ExecutionState<'e>> MiscClientSideAnalyzer<'a, 'acx, 'e, E> {
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
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(
                        &DestOperand::Register64(0),
                        self.vtable_fn_result_op,
                    );
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
                        true => match ctrl.resolve(to).if_constant() {
                            Some(s) => E::VirtualAddress::from_u64(s),
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
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
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
                        true => match ctrl.resolve(to).if_constant() {
                            Some(s) => E::VirtualAddress::from_u64(s),
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
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
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
                            true => match ctrl.resolve(to).if_constant() {
                                Some(s) => E::VirtualAddress::from_u64(s),
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
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
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
                    ctrl.resolve(ctx.and_const(self.arg_cache.on_call(i), 0xff))
                        .if_constant() == Some(0x98)
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
            if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                let mem = ctrl.resolve_mem(mem);
                if is_global(mem.address().0) {
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
            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
            let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
            if arg2 == self.arg_cache.on_entry(0) {
                // event_coords_to_game, use Custom(0) for x and Custom(1) for y
                let mem = ctx.mem_access(arg1, 0, MemAccessSize::Mem32);
                ctrl.move_resolved(&DestOperand::Memory(mem), ctx.custom(0));
                let mem = mem.with_offset_size(4, MemAccessSize::Mem32);
                ctrl.move_resolved(&DestOperand::Memory(mem), ctx.custom(1));
            } else if Operand::and_masked(arg2).0.if_custom() == Some(1) &&
                Operand::and_masked(arg1).0.if_custom() == Some(0)
            {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let result = &mut self.result;
                    if result.find_unit_for_click.is_none() {
                        result.find_unit_for_click = Some(dest);
                        ctrl.do_call_with_result(ctx.custom(2));
                    } else {
                        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
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
                ctrl.resolve(self.arg_cache.on_thiscall_call(i as u8))
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
        } else if let Operation::Move(ref dest, val, Some(condition)) = *op {
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
        arg_cache: &actx.arg_cache,
        local_player_id,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
    };
    let mut exec = E::initial_state(ctx, binary);
    // Center view has move-screen-over-time logic in single player,
    // this analysis just cares about instant move so set multiplayer = 1
    if let Some(mem) = is_multiplayer.if_memory() {
        exec.move_to(
            &DestOperand::Memory(*mem),
            ctx.const_1(),
        );
    }
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, action, exec, Default::default());
    analysis.analyze(&mut analyzer);

    result
}

struct CenterViewActionAnalyzer<'e, 'acx, 'a, E: ExecutionState<'e>> {
    result: &'a mut CenterViewAction<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
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
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let ctx = ctrl.ctx();
                    if let Some(w) = self.screen_size_from_move_screen_arg(ctx, arg1) {
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
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
