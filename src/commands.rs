use bumpalo::collections::Vec as BumpVec;

use scarf::{DestOperand, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};
use scarf::operand::{ArithOpType, MemAccessSize, OperandCtx};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until, find_bytes};
use crate::analysis_state::{AnalysisState, StateEnum, IsReplayState, StepNetworkState};
use crate::call_tracker::{CallTracker};
use crate::switch::CompleteSwitch;
use crate::struct_layouts;
use crate::util::{
    ControlExt, MemAccessExt, OptionExt, OperandExt, read_u32_at,
    if_arithmetic_eq_neq, is_global, bumpvec_with_capacity, single_result_assign, ExecStateExt,
};

#[derive(Clone, Debug)]
pub struct Selections<'e> {
    pub unique_command_user: Option<Operand<'e>>,
    pub selections: Option<Operand<'e>>,
}

#[derive(Clone, Debug)]
pub struct StepNetwork<'e, Va: VirtualAddressTrait> {
    pub receive_storm_turns: Option<Va>,
    pub process_commands: Option<Va>,
    pub process_lobby_commands: Option<Va>,
    pub net_player_flags: Option<Operand<'e>>,
    pub player_turns: Option<Operand<'e>>,
    pub player_turns_size: Option<Operand<'e>>,
    pub network_ready: Option<Operand<'e>>,
    pub storm_command_user: Option<Operand<'e>>,
}

pub(crate) struct StepReplayCommands<'e, Va: VirtualAddressTrait> {
    pub replay_end: Option<Va>,
    pub replay_header: Option<Operand<'e>>,
}

pub(crate) struct PrintText<Va: VirtualAddressTrait> {
    pub print_text: Option<Va>,
    pub add_to_replay_data: Option<Va>,
}

pub(crate) struct Cloak<Va: VirtualAddressTrait> {
    pub start_cloaking: Option<Va>,
}

pub(crate) struct Morph<Va: VirtualAddressTrait> {
    pub prepare_build_unit: Option<Va>,
}

pub(crate) struct Colors<'e> {
    pub use_rgb: Option<Operand<'e>>,
    pub rgb_colors: Option<Operand<'e>>,
    pub disable_choice: Option<Operand<'e>>,
    pub use_map_set_rgb: Option<Operand<'e>>,
    pub game_lobby: Option<Operand<'e>>,
    pub in_lobby_or_game: Option<Operand<'e>>,
}

pub(crate) fn print_text<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands: E::VirtualAddress,
    process_commands_switch: &CompleteSwitch<'e>,
) -> PrintText<E::VirtualAddress> {
    struct Analyzer<'a, 'e, E: ExecutionState<'e>> {
        ctx: OperandCtx<'e>,
        result: &'a mut PrintText<E::VirtualAddress>,
        branch: E::VirtualAddress,
        before_switch: bool,
    }

    impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Call(dest) => {
                    if self.before_switch {
                        return;
                    }
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
                        if self.result.print_text.is_none() {
                            if let Some(mem) = arg2.if_mem8() {
                                let offset_1 = mem.with_offset_size(1, MemAccessSize::Mem8)
                                    .address_op(self.ctx);
                                if offset_1 == arg1 {
                                    self.result.print_text = Some(dest);
                                }
                            }
                        } else {
                            if arg2.if_constant() == Some(0x52) {
                                self.result.add_to_replay_data = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                Operation::Jump { to, .. } => {
                    if to.if_constant().is_none() {
                        if self.before_switch {
                            self.before_switch = false;
                            ctrl.clear_all_branches();
                            ctrl.end_branch();
                            ctrl.add_branch_with_current_state(self.branch);
                        } else {
                            ctrl.end_branch();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // print_text is called for packet 0x5c as print_text(data + 2, data[1])
    // And followed by add_to_replay_data(data, 0x52)
    let mut result = PrintText {
        print_text: None,
        add_to_replay_data: None,
    };
    let branch = match process_commands_switch.branch(binary, ctx, 0x5c) {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = Analyzer::<E> {
        before_switch: true,
        ctx,
        branch,
        result: &mut result,
    };
    let mut exec_state = E::initial_state(ctx, binary);
    // Set arg3 to 1 so the replay-specific switch will be skipped
    exec_state.move_resolved(
        &DestOperand::from_oper(analysis.arg_cache.on_entry(2)),
        ctx.const_1(),
    );
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, process_commands, exec_state, Default::default());
    analysis.analyze(&mut analyzer);
    result
}

pub(crate) fn command_lengths<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
) -> Vec<u32> {
    let rdata = analysis.binary_sections.rdata;
    static NEEDLE: &[u8] = &[
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0x1, 0, 0, 0,
        0x21, 0, 0, 0,
        0x21, 0, 0, 0,
        0x1, 0, 0, 0,
        0x1a, 0, 0, 0,
        0x1a, 0, 0, 0,
        0x1a, 0, 0, 0,
        0x8, 0, 0, 0,
        0x3, 0, 0, 0,
        0x5, 0, 0, 0,
        0x2, 0, 0, 0,
        0x1, 0, 0, 0,
        0x1, 0, 0, 0,
        0x5, 0, 0, 0,
        0x3, 0, 0, 0,
        0xa, 0, 0, 0,
        0xb, 0, 0, 0,
        0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff,
        0x1, 0, 0, 0,
    ];
    let bump = &analysis.bump;
    let results = find_bytes(bump, &rdata.data, NEEDLE);
    test_assert_eq!(results.len(), 1);
    let mut result = results.first().map(|&start| {
        let mut pos = NEEDLE.len() as u32;
        loop {
            let len = read_u32_at(&rdata, start + pos).unwrap_or_else(|| !1);
            if len != !0 && len > 0x200 {
                break;
            }
            pos += 4;
        }
        let mut vec = Vec::new();
        for i in 0..(pos / 4) {
            vec.push(read_u32_at(&rdata, start + i * 4).unwrap_or_else(|| !0));
        }
        vec
    }).unwrap_or_else(|| Vec::new());
    // This is not correct in the lookup table for some reason
    if let Some(cmd_37) = result.get_mut(0x37) {
        *cmd_37 = 7;
    }
    while result.last().cloned() == Some(!0) {
        result.pop();
    }
    result
}

pub(crate) fn send_command<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    firegraft: &crate::FiregraftAddresses<E::VirtualAddress>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let &button_sets = firegraft.buttonsets.first()?;
    let stim_func = struct_layouts::button_set_index_to_action(binary, button_sets, 0, 5)?;

    let mut analysis = FuncAnalysis::new(binary, ctx, stim_func);
    let mut analyzer = FindSendCommand::<E> {
        result: None,
        is_inlining: false,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindSendCommand<'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    is_inlining: bool,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSendCommand<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    // Check if calling send_command(&[COMMAND_STIM], 1)
                    let arg1 = ctrl.resolve_arg(0);
                    let arg1_addr = ctx.mem_access(arg1, 0, MemAccessSize::Mem8);
                    let arg1_inner = ctrl.read_memory(&arg1_addr);
                    if arg1_inner.if_constant() == Some(0x36) {
                        let arg2 = ctrl.resolve_arg(1);
                        if arg2.if_constant() == Some(1) {
                            if single_result_assign(Some(dest), &mut self.result) {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                    }

                    if !self.is_inlining {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.is_inlining = false;
                        if self.result.is_some() && !crate::test_assertions() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_process_fn_switch<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> Option<CompleteSwitch<'e>> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    // Set arg3 to 1; for process_commands skips over replay command switch,
    // process_lobby_commands doesn't care
    let mut exec_state = E::initial_state(ctx, binary);
    exec_state.move_to(
        &DestOperand::from_oper(actx.arg_cache.on_entry(2)),
        ctx.const_1(),
    );
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, func, exec_state, Default::default());
    let mut analyzer = AnalyzeFirstSwitch::<E> {
        result: None,
        phantom: Default::default(),
        first_branch: true,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AnalyzeFirstSwitch<'e, E: ExecutionState<'e>> {
    result: Option<CompleteSwitch<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
    first_branch: bool,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeFirstSwitch<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if E::VirtualAddress::SIZE == 8 {
            // Skip over 64bit stack_probe to keep rax same as the probe length.
            // arguments would be spilled to unreachable stack otherwise.
            if self.first_branch {
                if let Operation::Jump { .. } = *op {
                    self.first_branch = false;
                } else if let Operation::Call(..) = *op {
                    self.first_branch = false;
                    if ctrl.check_stack_probe() {
                        return;
                    }
                }
            }
        }
        ctrl.aliasing_memory_fix(op);
        if let Operation::Jump { to, .. } = *op {
            let to = ctrl.resolve(to);
            if to.if_constant().is_none() {
                let ctx = ctrl.ctx();
                let exec_state = ctrl.exec_state();
                self.result = CompleteSwitch::new(to, ctx, exec_state);
                ctrl.end_analysis();
            }
        } else {
            // Skip past sometimes occuring `stack_frame | 0` messing up things
            if E::VirtualAddress::SIZE == 4 {
                if let Operation::Move(_, value) = *op {
                    let value = ctrl.resolve(value);
                    let ctx = ctrl.ctx();
                    let skip = value.if_arithmetic_and()
                        .and_then(|(l, r)| {
                            r.if_constant().filter(|&x| x.wrapping_add(1) & x == 0)?;
                            let (l, r) = l
                                .if_arithmetic_rsh_const(8)
                                .unwrap_or(l)
                                .if_arithmetic_sub()?;
                            r.if_constant()?;
                            if l != ctx.register(4) {
                                None
                            } else {
                                Some(())
                            }
                        })
                        .is_some();
                    if skip {
                        ctrl.skip_operation();
                    }
                }
            }
        }
    }
}

pub(crate) fn command_user<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    game: Operand<'e>,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let command_ally = process_commands_switch.branch(binary, ctx, 0xe)?;
    let mut analysis = FuncAnalysis::new(binary, ctx, command_ally);
    let mut analyzer = CommandUserAnalyzer::<E> {
        result: None,
        inlining: false,
        game,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct CommandUserAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    game: Operand<'e>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CommandUserAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if !crate::test_assertions() && self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(ref dest, _) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem8 {
                        // The alliance command writes bytes to game + e544 + x * 0xc
                        let (base, offset) = ctrl.resolve_mem(mem).address();
                        if offset == 0xe544 {
                            let command_user = base.if_arithmetic_add()
                                .and_if_either_other(|x| x == self.game)
                                .and_then(|other| other.if_arithmetic_mul_const(0xc));
                            if single_result_assign(command_user, &mut self.result) {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { to, .. } => {
                if !self.inlining {
                    // Don't follow through the switch loop
                    if to.if_constant().is_none() {
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn selections<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Selections<'e> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = Selections {
        selections: None,
        unique_command_user: None,
    };
    let cancel_nuke_command = process_commands_switch.branch(binary, ctx, 0x2e);
    let cancel_nuke = match cancel_nuke_command {
        Some(s) => s,
        None => return result,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, cancel_nuke);
    let mut analyzer = SelectionsAnalyzer::<E> {
        sel_state: SelectionState::Start,
        result: &mut result,
        checked_calls: bumpvec_with_capacity(8, bump),
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

enum SelectionState<'e> {
    Start,
    LimitJumped(Operand<'e>),
}

struct SelectionsAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut Selections<'e>,
    sel_state: SelectionState<'e>,
    checked_calls: BumpVec<'acx, E::VirtualAddress>,
    inline_depth: u8,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SelectionsAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth < 3 {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        if !self.checked_calls.iter().any(|&x| x == dest) {
                            self.checked_calls.push(dest);
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.selections.is_some() && !crate::test_assertions() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { to, condition } => {
                // Don't follow through the switch loop in process_commands
                if self.inline_depth == 0 {
                    if to.if_constant().is_none() {
                        ctrl.end_branch();
                        return;
                    }
                }
                let condition = ctrl.resolve(condition);
                if let SelectionState::Start = self.sel_state {
                    if let Some((l, r)) = condition.if_arithmetic(ArithOpType::GreaterThan) {
                        if l.if_constant() == Some(0xc) {
                            self.sel_state = SelectionState::LimitJumped(r.clone());
                        }
                    }
                } else if let SelectionState::LimitJumped(selection_pos) = self.sel_state {
                    // Check if the condition is
                    // (selections + (unique_command_user * 0xc + selection_pos) * 4) == 0
                    let ctx = ctrl.ctx();
                    let x = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1 == ctx.const_0())
                        .and_then(|x| x.0.if_memory())
                        .and_then(|mem| {
                            mem.if_add_either(ctx, |x| {
                                x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                            })
                        });
                    if let Some((index, selections)) = x {
                        let unique_command_user = index.if_arithmetic_add()
                            .and_if_either_other(|x| x == selection_pos)
                            .and_then(|x| x.if_arithmetic_mul_const(0xc));
                        if let Some(unique_command_user) = unique_command_user {
                            single_result_assign(
                                Some(unique_command_user.clone()),
                                &mut self.result.unique_command_user,
                            );
                            let end = single_result_assign(
                                Some(selections.clone()),
                                &mut self.result.selections,
                            );
                            if end {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn is_replay<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let command = process_commands_switch.branch(binary, ctx, 0x5d)?;

    // The replay pause command does
    // if (is_replay) {
    //     process(cmd[1..5]);
    // }
    // Try check for that, should be fine even with inlining
    let exec_state = E::initial_state(ctx, binary);
    let state = IsReplayState {
        possible_result: None,
    };
    let state = AnalysisState::new(bump, StateEnum::IsReplay(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, command, exec_state, state);
    let mut analyzer = IsReplayAnalyzer::<E> {
        checked_calls: bumpvec_with_capacity(8, bump),
        result: None,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct IsReplayAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    checked_calls: BumpVec<'acx, E::VirtualAddress>,
    inline_depth: u8,
}

impl<'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    IsReplayAnalyzer<'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth < 2 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if !self.checked_calls.iter().any(|&x| x == dest) {
                            self.checked_calls.push(dest);
                            self.inline_depth += 1;
                            ctrl.inline(self, dest);
                            self.inline_depth -= 1;
                            if self.result.is_some() && !crate::test_assertions() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Move(_, val) => {
                let possible_result = ctrl.user_state().get::<IsReplayState>().possible_result;
                if possible_result.is_some() {
                    let val = ctrl.resolve(val);
                    let is_ok = val.if_mem32_offset(1).is_some();
                    if is_ok {
                        if single_result_assign(possible_result, &mut self.result) {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { to, condition } => {
                // Don't follow through the switch loop in process_commands
                if self.inline_depth == 0 {
                    if to.if_constant().is_none() {
                        ctrl.end_branch();
                        return;
                    }
                }
                let condition = ctrl.resolve(condition);
                let ctx = ctrl.ctx();
                let other = condition.if_arithmetic_eq()
                    .filter(|x| x.1 == ctx.const_0())
                    .map(|x| x.0)
                    .filter(|&x| is_global(x));

                ctrl.user_state().set(IsReplayState {
                    possible_result: other,
                });
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_step_network<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_network: E::VirtualAddress,
) -> StepNetwork<'e, E::VirtualAddress> {
    let mut result = StepNetwork {
        receive_storm_turns: None,
        net_player_flags: None,
        player_turns: None,
        player_turns_size: None,
        network_ready: None,
        storm_command_user: None,
        process_commands: None,
        process_lobby_commands: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let exec_state = E::initial_state(ctx, binary);
    let state = StepNetworkState {
        after_receive_storm_turns: false,
    };
    let state = AnalysisState::new(bump, StateEnum::StepNetwork(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, step_network, exec_state, state);
    let mut analyzer = AnalyzeStepNetwork::<E> {
        result: &mut result,
        inlining: false,
        process_command_inline_depth: 0,
        inline_limit: 0,
        storm_command_user_candidate: None,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeStepNetwork<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepNetwork<'e, E::VirtualAddress>,
    inlining: bool,
    process_command_inline_depth: u8,
    inline_limit: u8,
    storm_command_user_candidate: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeStepNetwork<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.result.network_ready.is_none() {
            if ctrl.user_state().get::<StepNetworkState>().after_receive_storm_turns {
                if let Operation::Move(ref dest, val) = *op {
                    if let DestOperand::Memory(mem) = dest {
                        let ctx = ctrl.ctx();
                        if ctrl.resolve(val) == ctx.const_1() {
                            self.result.network_ready = Some(ctx.memory(&ctrl.resolve_mem(mem)));
                        }
                    }
                } else if let Operation::Call(_) = op {
                    ctrl.user_state().set(StepNetworkState {
                        after_receive_storm_turns: false,
                    });
                }
            } else {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        // Check that receive_storm_turns didn't get inlined.
                        // receive_storm_turns calls storm_122 with same arguments
                        // but adds arg6 = 4.
                        let ok = Some(ctrl.resolve_arg(0))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve_arg(1))
                            .filter(|x| x.if_constant() == Some(0xc))
                            .map(|_| ctrl.resolve_arg(5))
                            .filter(|x| x.if_constant() != Some(0x4))
                            .is_some();
                        if ok {
                            let arg3 = ctrl.resolve_arg(2);
                            let arg4 = ctrl.resolve_arg(3);
                            let arg5 = ctrl.resolve_arg(4);
                            let ok = arg3.if_constant().is_some() &&
                                arg4.if_constant().is_some() &&
                                arg5.if_constant().is_some();
                            if ok {
                                self.result.receive_storm_turns = Some(dest);
                                self.result.player_turns = Some(arg3);
                                self.result.player_turns_size = Some(arg4);
                                self.result.net_player_flags = Some(arg5);
                                ctrl.user_state().set(StepNetworkState {
                                    after_receive_storm_turns: true,
                                });
                                return;
                            }
                        }
                        if !self.inlining {
                            self.inlining = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inlining = false;
                        }
                    }
                }
            }
        } else {
            let ctx = ctrl.ctx();
            let is_process_lobby_commands = self.result.process_commands.is_some();
            if !self.inlining {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        // process_commands(player_turns[7], turns_size[7], 0)
                        // process_lobby_commands(player_turns[7], turns_size[7], 7)
                        let ok =
                            ctrl.resolve_arg(0).if_memory()
                                .filter(|&x| {
                                    x.size == E::WORD_SIZE &&
                                        Some(ctx.mem_sub_const_op(
                                            &x,
                                            7 * E::VirtualAddress::SIZE as u64,
                                        )) == self.result.player_turns
                                })
                                .and_then(|_| ctrl.resolve_arg(1).if_mem32())
                                .filter(|&x| {
                                    Some(ctx.mem_sub_const_op(x, 7 * 4)) ==
                                        self.result.player_turns_size
                                })
                                .filter(|_| {
                                    let cmp = match is_process_lobby_commands {
                                        true => 7,
                                        false => 0,
                                    };
                                    ctrl.resolve_arg(2).if_constant() == Some(cmp)
                                })
                                .is_some();
                        if ok {
                            if !is_process_lobby_commands {
                                self.result.process_commands = Some(dest);
                                self.result.storm_command_user = self.storm_command_user_candidate;
                            } else {
                                self.result.process_lobby_commands = Some(dest);
                                ctrl.end_analysis();
                            }
                        } else {
                            let should_inline = if !is_process_lobby_commands {
                                self.process_command_inline_depth < 1 &&
                                    self.storm_command_user_candidate.is_none()
                            } else {
                                // Inline if
                                //   this == player_turns, arg1(u8) == 1, arg2(u8) == 0
                                // or (depth 2)
                                //   this == player_turns, arg1(u8) == 0
                                let this_ok = Some(ctrl.resolve_register(1)) ==
                                    self.result.player_turns;
                                let arg1 = ctrl.resolve_arg_thiscall(0);
                                let arg2 = ctrl.resolve_arg_thiscall(1);
                                if this_ok {
                                    (ctx.and_const(arg1, 0xff) == ctx.const_1() &&
                                        self.process_command_inline_depth < 1 &&
                                        ctx.and_const(arg2, 0xff) == ctx.const_0()) ||
                                    (self.process_command_inline_depth < 2 &&
                                        ctx.and_const(arg1, 0xff) == ctx.const_0())
                                } else {
                                    self.process_command_inline_depth < 2 &&
                                        arg2.if_constant() == Some(7) &&
                                        Some(ctx.sub_const(
                                            arg1,
                                            7 * E::VirtualAddress::SIZE as u64,
                                        )) == self.result.player_turns
                                }
                            };
                            if should_inline {
                                self.process_command_inline_depth += 1;
                                ctrl.inline(self, dest);
                                self.process_command_inline_depth -= 1;
                                if self.result.process_lobby_commands.is_some() {
                                    ctrl.end_analysis();
                                }
                            } else {
                                // Inline for is_observer_id
                                self.inlining = true;
                                self.inline_limit = 2;
                                ctrl.inline(self, dest);
                                self.inlining = false;
                                if self.inline_limit != 0 {
                                    ctrl.skip_operation();
                                    self.inline_limit = 0;
                                }
                            }
                        }
                    }
                } else {
                    if !is_process_lobby_commands {
                        if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                            if ctrl.resolve(value).if_constant() == Some(7) {
                                let dest = ctrl.resolve_mem(mem);
                                if dest.is_global() {
                                    self.storm_command_user_candidate = Some(ctx.memory(&dest));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn step_replay_commands<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands: E::VirtualAddress,
    game: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // step_replay_commands calls process_commands, and starts with comparision of global bool
    // is_ingame and frame count against replay limit.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();

    let mut result = None;
    let callers = functions.find_callers(analysis, process_commands);
    for caller in callers {
        let new = entry_of_until(binary, funcs, caller, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = IsStepReplayCommands::<E> {
                result: EntryOf::Retry,
                game,
                limit: 6,
                phantom: Default::default(),
            };
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry().map(|x| x.0);
        if single_result_assign(new, &mut result) {
            break;
        }
    }
    result
}

struct IsStepReplayCommands<'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    game: Operand<'e>,
    limit: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStepReplayCommands<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if matches!(op, Operation::Call(..) | Operation::Jump { .. }) {
            self.limit = match self.limit.checked_sub(1) {
                Some(s) => s,
                None => {
                    ctrl.end_analysis();
                    return;
                }
            }
        }
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let has_frame = condition.iter_no_mem_addr()
                    .any(|x| {
                        x.if_mem32_offset(0x14c)
                            .filter(|&x| x == self.game)
                            .is_some()
                    });
                if has_frame {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn replay_data<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Option<Operand<'e>> {
    // process_commands calls add_to_replay_data(data, len) after its switch,
    // which immediately checks replay_data.field0 == 0
    //
    // Also command length for case 0x15 is 0xb
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let branch = process_commands_switch.branch(binary, ctx, 0x15)?;

    let mut analysis = FuncAnalysis::new(binary, ctx, branch);
    let mut analyzer = FindReplayData::<E> {
        result: None,
        limit: 6,
        inline_depth: 0,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindReplayData<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    limit: u8,
    inline_depth: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindReplayData<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) if self.inline_depth == 0 => {
                if self.limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
                self.limit -= 1;
                if ctrl.resolve_arg(1).if_constant() == Some(0xb) {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let old_limit = self.limit;
                        self.inline_depth = 1;
                        self.limit = 12;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        self.limit = old_limit;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Call(dest) if self.inline_depth == 1 => {
                // There may be an intermediate function which calls
                // replay_data->add(player?, data, len)
                if self.limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
                self.limit -= 1;
                if ctrl.resolve_arg(2).if_constant() == Some(0xb) {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    ctrl.end_branch();
                }
            }
            Operation::Call(..) => {
                ctrl.end_branch();
            }
            Operation::Jump { condition, .. } if self.inline_depth != 0 => {
                if self.limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
                self.limit -= 1;
                let condition = ctrl.resolve(condition);
                let result = if_arithmetic_eq_neq(condition)
                    .filter(|x| x.1 == ctx.const_0())
                    .and_then(|x| x.0.if_mem32_offset(0))
                    .filter(|x| x.if_memory().is_some());
                if result.is_some() {
                    self.result = result;
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_step_replay_commands<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_replay_commands: E::VirtualAddress,
) -> StepReplayCommands<'e, E::VirtualAddress> {
    let mut result = StepReplayCommands {
        replay_end: None,
        replay_header: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, step_replay_commands);
    let mut analyzer = AnalyzeStepReplayCommands::<E> {
        result: &mut result,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeStepReplayCommands<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepReplayCommands<'e, E::VirtualAddress>,
    inlining: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeStepReplayCommands<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.inlining {
            match *op {
                Operation::Jump { .. } | Operation::Call(..) => {
                    ctrl.end_analysis();
                    return;
                }
                _ => (),
            }
            return;
        }
        if self.result.replay_header.is_none() {
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    // Signed gt
                    let result = condition.if_arithmetic_gt()
                        .and_then(|(l, _)| {
                            l.if_arithmetic_and_const(0xffff_ffff)?
                                .if_arithmetic_add_const(0x8000_0000)?
                                .if_mem32()
                        });
                    if let Some(result) = result {
                        if result.is_global() {
                            // End frame is at offset +1 of replay header
                            let ctx = ctrl.ctx();
                            self.result.replay_header =
                                Some(result.with_offset(0u64.wrapping_sub(1)).address_op(ctx));
                            let end_branch = ctrl.current_instruction_end();
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_address(end_branch);
                        }
                    }
                }
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inlining = false;
                    }
                }
                _ => (),
            }
        } else {
            match *op {
                Operation::Call(dest) => {
                    // Assuming that the only call after replay header frame count check
                    // is replay_end. If there's second then make result None and end.
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.result.replay_end.is_none() {
                            self.result.replay_end = Some(dest);
                        } else {
                            self.result.replay_end = None;
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
        }
    }
}

pub(crate) fn player_colors<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    process_lobby_commands_switch: &CompleteSwitch<'e>,
) -> Colors<'e> {
    let mut result = Colors {
        use_rgb: None,
        rgb_colors: None,
        disable_choice: None,
        use_map_set_rgb: None,
        game_lobby: None,
        in_lobby_or_game: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let branch = match process_lobby_commands_switch.branch(binary, ctx, 0x69) {
        Some(s) => s,
        None => return result,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, branch);
    let mut analyzer = AnalyzePlayerColors::<E> {
        result: &mut result,
        inline_depth: 0,
        state: PlayerColorState::First,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        jump_conditions: bumpvec_with_capacity(10, bump),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzePlayerColors<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut Colors<'e>,
    inline_depth: u8,
    state: PlayerColorState,
    call_tracker: CallTracker<'acx, 'e, E>,
    // (branch_start, preceding condition),
    jump_conditions: BumpVec<'acx, (E::VirtualAddress, Operand<'e>)>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum PlayerColorState {
    // Find write to any of the player color vars from command bytes
    // Keep track of the last branch condition to determine in_lobby_or_game
    First,
    // Handle rest of the color vars
    Rest,
    // Find vtable jump/call
    GameLobby,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzePlayerColors<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            PlayerColorState::First | PlayerColorState::Rest => {
                if self.check_color_write(ctrl, op) {
                    ctrl.clear_unchecked_branches();
                    if self.state == PlayerColorState::First {
                        let branch_start = ctrl.branch_start();
                        if let Some(&(_, condition)) = self.jump_conditions.iter()
                            .find(|x| x.0 == branch_start)
                        {
                            let condition = self.call_tracker.resolve_calls(condition);
                            self.result.in_lobby_or_game = condition.if_arithmetic_eq_neq_zero(ctx)
                                .map(|x| x.0)
                                .filter(|&x| is_global(x));
                        }
                        self.state = PlayerColorState::Rest;
                    } else {
                        let all_done = self.result.use_rgb.is_some() &&
                            self.result.rgb_colors.is_some() &&
                            self.result.disable_choice.is_some() &&
                            self.result.use_map_set_rgb.is_some();
                        if all_done {
                            self.state = PlayerColorState::GameLobby;
                        }
                    }
                } else {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            if self.inline_depth == 0 {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.use_rgb.is_some() {
                                    ctrl.end_analysis();
                                    return;
                                }
                            }
                            self.call_tracker.add_call(ctrl, dest);
                        }
                    } else if let Operation::Jump { condition, to } = *op {
                        if self.state == PlayerColorState::First {
                            let condition = ctrl.resolve(condition);
                            if condition.if_constant().is_none() {
                                self.jump_conditions.push(
                                    (ctrl.current_instruction_end(), condition),
                                );
                                if let Some(to) = ctrl.resolve_va(to) {
                                    self.jump_conditions.push((to, condition));
                                }
                            }
                        }
                    }
                }
            }
            PlayerColorState::GameLobby => {
                let dest = match *op {
                    Operation::Jump { to, condition } => {
                        if to.if_constant().is_none() && condition == ctx.const_1() {
                            Some(to)
                        } else {
                            None
                        }
                    }
                    Operation::Call(dest) => Some(dest),
                    _ => None,
                };
                if let Some(dest) = dest {
                    let dest = ctrl.resolve(dest);
                    if let Some(dest) = dest.if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        if matches!(*op, Operation::Call(..)) {
                            if self.inline_depth < 2 {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.game_lobby.is_some() {
                                    ctrl.end_analysis();
                                    return;
                                }
                            }
                            self.call_tracker.add_call(ctrl, dest);
                        }
                    } else {
                        if let Some(mem) = ctrl.if_mem_word(dest) {
                            let (base, _) = mem.address();
                            let this = ctrl.resolve_register(1);
                            if ctrl.if_mem_word(base).map(|x| x.address()) == Some((this, 0)) {
                                let resolved = self.call_tracker.resolve_calls(this);
                                if is_global(resolved) {
                                    self.result.game_lobby = Some(resolved);
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Operation::Jump { to, .. } = *op {
            if to.if_constant().is_none() {
                // Assuming switch jump
                ctrl.end_branch();
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> AnalyzePlayerColors<'a, 'acx, 'e, E> {
    fn check_color_write(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) -> bool {
        match *op {
            Operation::Call(..) => {
                // check memcpy calls
                let arg3 = ctrl.resolve_arg(2);
                if let Some(len) = arg3.if_constant() {
                    if len == 8 || len == 0x80 {
                        let arg2 = ctrl.resolve_arg(1);
                        let arg2_offset = arg2.if_arithmetic_add()
                            .and_then(|(_l, r)| r.if_constant());
                        if let Some(off) = arg2_offset {
                            let out = if off == 0x2 && len == 8 {
                                &mut self.result.use_map_set_rgb
                            } else if off == 0xa && len == 8 {
                                &mut self.result.disable_choice
                            } else if off == 0x1a && len == 0x80 {
                                &mut self.result.rgb_colors
                            } else {
                                return false;
                            };
                            let arg1 = ctrl.resolve_arg(0);
                            if is_global(arg1) {
                                *out = Some(arg1);
                                return true;
                            }
                        }
                    }
                }
                false
            }
            Operation::Move(DestOperand::Memory(ref dest), value)
                if dest.size == MemAccessSize::Mem8 =>
            {
                let value = ctrl.resolve(value);
                if value.if_mem8_offset(1).is_some() {
                    let dest = ctrl.resolve_mem(dest);
                    if dest.is_global() {
                        let ctx = ctrl.ctx();
                        self.result.use_rgb = Some(ctx.memory(&dest));
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }
}

pub(crate) fn cloak<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    process_commands: E::VirtualAddress,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Cloak<E::VirtualAddress> {

    let binary = actx.binary;
    let ctx = actx.ctx;

    // inline once to command_cloak(data), which should call
    // check_tech_use_requirements(), check retval == 1, and then there call start_cloaking
    // First branch in start_cloaking checks unit flag 0x100
    let mut result = Cloak {
        start_cloaking: None,
    };
    let branch = match process_commands_switch.branch(binary, ctx, 0x21) {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = CloakAnalyzer::<E> {
        state: CloakState::BeforeSwitch,
        inline_depth: 0,
        branch,
        result: &mut result,
        call_tracker: CallTracker::with_capacity(actx, 0, 0x20),
        arg_cache: &actx.arg_cache,
    };
    let mut exec_state = E::initial_state(ctx, binary);
    // Set arg3 to 1 so the replay-specific switch will be skipped
    exec_state.move_resolved(
        &DestOperand::from_oper(actx.arg_cache.on_entry(2)),
        ctx.const_1(),
    );
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, process_commands, exec_state, Default::default());
    analysis.analyze(&mut analyzer);
    result
}

struct CloakAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    state: CloakState,
    inline_depth: u8,
    result: &'a mut Cloak<E::VirtualAddress>,
    branch: E::VirtualAddress,
    call_tracker: CallTracker<'acx, 'e, E>,
    arg_cache: &'a ArgCache<'e, E>,
}

enum CloakState {
    BeforeSwitch,
    TechUseRetVal,
    FindStartCloaking,
    VerifyStartCloaking,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CloakAnalyzer<'a, 'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            CloakState::BeforeSwitch => {
                if let Operation::Jump { to, .. } = *op {
                    if to.if_constant().is_none() {
                        self.state = CloakState::TechUseRetVal;
                        ctrl.clear_all_branches();
                        ctrl.continue_at_address(self.branch);
                    }
                } else if let Operation::Call(..) = *op {
                    ctrl.check_stack_probe();
                }
            }
            CloakState::TechUseRetVal => {
                if let Operation::Jump { condition, to } = *op {
                    if to.if_constant().is_none() {
                        // Switch again
                        ctrl.end_analysis();
                        return;
                    }
                    let condition = ctrl.resolve(condition);
                    let ctx = ctrl.ctx();
                    if let Some((l, r, eq)) = condition.if_arithmetic_eq_neq() {
                        if r == ctx.const_1() && l.unwrap_and_mask().if_custom().is_some() {
                            self.state = CloakState::FindStartCloaking;
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.inline_depth == 0 {
                            let arg1 = ctrl.resolve_arg(0);
                            if arg1 == self.arg_cache.on_entry(0) {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                ctrl.end_analysis();
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            CloakState::FindStartCloaking => {
                if let Operation::Jump { .. } = *op {
                    ctrl.end_analysis();
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.state = CloakState::VerifyStartCloaking;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.start_cloaking.is_some() {
                            self.result.start_cloaking = Some(dest);
                            ctrl.end_analysis();
                        } else {
                            self.state = CloakState::FindStartCloaking;
                        }
                    }
                }
            }
            CloakState::VerifyStartCloaking => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let condition = self.call_tracker.resolve_calls(condition);
                    let ok = condition.if_arithmetic_and_const(0x1)
                        .and_then(|x| x.if_mem8_offset(E::struct_layouts().unit_flags() + 1))
                        .is_some();
                    if ok {
                        self.result.start_cloaking = Some(E::VirtualAddress::from_u64(0));
                    }
                    ctrl.end_analysis();
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
        }
    }
}

pub(crate) fn morph<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    process_commands: E::VirtualAddress,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Morph<E::VirtualAddress> {

    let binary = actx.binary;
    let ctx = actx.ctx;

    // Should be prepare_build_unit(this = _, a1 = Mem16[command_data + 1])
    let mut result = Morph {
        prepare_build_unit: None,
    };
    let branch = match process_commands_switch.branch(binary, ctx, 0x23) {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = MorphAnalyzer::<E> {
        state: MorphState::BeforeSwitch,
        inline_depth: 0,
        branch,
        result: &mut result,
        arg_cache: &actx.arg_cache,
    };
    let mut exec_state = E::initial_state(ctx, binary);
    // Set arg3 to 1 so the replay-specific switch will be skipped
    exec_state.move_resolved(
        &DestOperand::from_oper(actx.arg_cache.on_entry(2)),
        ctx.const_1(),
    );
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, process_commands, exec_state, Default::default());
    analysis.analyze(&mut analyzer);
    result
}

struct MorphAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    state: MorphState,
    inline_depth: u8,
    result: &'a mut Morph<E::VirtualAddress>,
    branch: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
}

enum MorphState {
    BeforeSwitch,
    OrderJump,
    PrepareBuildUnit,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for MorphAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            MorphState::BeforeSwitch => {
                if let Operation::Jump { to, .. } = *op {
                    if to.if_constant().is_none() {
                        self.state = MorphState::OrderJump;
                        ctrl.clear_all_branches();
                        ctrl.continue_at_address(self.branch);
                    }
                } else if let Operation::Call(..) = *op {
                    ctrl.check_stack_probe();
                }
            }
            MorphState::OrderJump => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.inline_depth == 0 {
                            let arg1 = ctrl.resolve_arg(0);
                            if arg1 == self.arg_cache.on_entry(0) {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((_, r, eq)) = condition.if_arithmetic_eq_neq() {
                        if r.if_constant() == Some(0x2a) {
                            self.state = MorphState::PrepareBuildUnit;
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq, to);
                        }
                    }
                }
            }
            MorphState::PrepareBuildUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg_thiscall(0);
                        let ok = a1.if_mem16_offset(1) == Some(self.arg_cache.on_entry(0));
                        if ok {
                            self.result.prepare_build_unit = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}
