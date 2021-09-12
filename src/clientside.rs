use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, Operation, Rva};
use scarf::operand::{OperandCtx};

use crate::{
    AnalysisCtx, ArgCache, EntryOf, EntryOfResult, entry_of_until, unwrap_sext,
    single_result_assign, OptionExt, if_arithmetic_eq_neq, FunctionFinder,
};
use crate::hash_map::HashMap;
use crate::struct_layouts;
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
                        self.call_found = val.iter()
                            .flat_map(|x| x.if_constant())
                            .any(|x| x == global_addr.as_u64());
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
                        .map(|mem| ctx.mem_sub_const_op(mem, 11 * 4));
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
                    let arg1 = ctrl.resolve(self.args.on_call(0));
                    let arg1 = unwrap_sext(arg1);
                    let arg2 = ctrl.resolve(self.args.on_call(1));
                    let arg2 = unwrap_sext(arg2);
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
                                .map(unwrap_sext)
                                .and_then(|x| x.if_mem16()?.if_arithmetic_add())
                                .and_either(|x| x.if_constant())
                                .map(|(c, _)| (screen_coord, divisor, c as u32))
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
    let vtable_fn_result_op = ctx.custom(0);
    for vtable in vtables {
        let init_func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let state = MiscClientSideAnalyzerState::Begin;
        let mut analyzer = MiscClientSideAnalyzer {
            result: &mut result,
            done: false,
            inline_depth: 0,
            vtable_fn_result_op,
            is_multiplayer,
            scmain_state,
            branch_start_states: Default::default(),
            binary,
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

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
enum MiscClientSideAnalyzerState {
    // Checking for this.vtable_fn() == 0
    Begin,
    // Checking for multiplayer == 0
    OnVtableFnZeroBranch,
    // Checking for is_paused if not found yet, once it is checking
    // for scmain_state == 3
    MultiplayerZeroBranch,
    // Checking for is_placing_building == 0
    ScMainStateThreeBranch,
    // Checking for is_targeting == 0
    IsPlacingBuildingFound,
    End,
}

impl analysis::AnalysisState for MiscClientSideAnalyzerState {
    fn merge(&mut self, newer: Self) {
        use MiscClientSideAnalyzerState::*;
        let (low, high) = match *self < newer {
            true => (*self, newer),
            false => (newer, *self),
        };
        match (low, high) {
            (a, b) if a == b => (),
            // When leaving the `this.vtable_fn() == 0` branch and
            // merging with `Begin`, merge to `End` (Nothing important to be found
            // after that)
            (Begin, _) => *self = End,
            // scmain_state == 3 branch is after `Multiplayer == 0` branch (searching pause game)
            // and its else branch join, so they merge to MultiplayerZeroBranch to
            // keep analysis
            (OnVtableFnZeroBranch, MultiplayerZeroBranch) => *self = high,
            // Otherwise merge to `End`
            (OnVtableFnZeroBranch, _) => *self = End,
            // However, rest of the checks are all inside scmain_state == 3, so
            // MultiplayerZeroBranch joining with higher state means end
            (MultiplayerZeroBranch, _) => *self = End,
            // is_placing_building == 0 also joins with else branch before is_targeting == 0
            // check.
            (ScMainStateThreeBranch, IsPlacingBuildingFound) => *self = high,
            (ScMainStateThreeBranch, _) => *self = End,
            (IsPlacingBuildingFound, _) => *self = End,
            (End, _) => *self = End,
        }
    }
}

struct MiscClientSideAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut MiscClientSide<'e>,
    done: bool,
    inline_depth: u8,
    vtable_fn_result_op: Operand<'e>,
    is_multiplayer: Operand<'e>,
    scmain_state: Operand<'e>,
    branch_start_states: HashMap<Rva, MiscClientSideAnalyzerState>,
    binary: &'a BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for MiscClientSideAnalyzer<'a, 'e, E> {
    type State = MiscClientSideAnalyzerState;
    type Exec = E;

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let rva = Rva((ctrl.address().as_u64() - self.binary.base.as_u64()) as u32);
        if let Some(state) = self.branch_start_states.remove(&rva) {
            if state == MiscClientSideAnalyzerState::MultiplayerZeroBranch {
                self.inline_depth = 0;
            }
            *ctrl.user_state() = state;
        }
    }

    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        use MiscClientSideAnalyzerState as State;
        match *ctrl.user_state() {
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

impl<'a, 'e, E: ExecutionState<'e>> MiscClientSideAnalyzer<'a, 'e, E> {
    fn state_begin(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        use MiscClientSideAnalyzerState as State;
        // Check for the this.vtable_fn() call and
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                // call [[ecx] + offset]
                let is_vtable_fn = ctrl.if_mem_word(dest)
                    .and_then(|x| x.if_arithmetic_add())
                    .and_either_other(|x| x.if_constant())
                    .and_then(|x| ctrl.if_mem_word(x))
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
                    let cond_ok = if_arithmetic_eq_neq(cond)
                        .and_then(|(l, r, _)| {
                            let op = Some((l, r))
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                                .map(|x| Operand::and_masked(x).0)?;
                            Some(op)
                        });
                    if let Some(op) = cond_ok {
                        if *ctrl.user_state() == State::ScMainStateThreeBranch {
                            self.result.is_placing_building = Some(op.clone());
                            *ctrl.user_state() = State::IsPlacingBuildingFound;
                        } else {
                            self.result.is_targeting = Some(op.clone());
                            self.done = true;
                            *ctrl.user_state() = State::End;
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
