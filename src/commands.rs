use bumpalo::collections::Vec as BumpVec;

use scarf::{BinaryFile, DestOperand, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};
use scarf::operand::{ArithOpType, MemAccessSize, OperandCtx};

use crate::{
    AnalysisCtx, ArgCache, ControlExt, EntryOf, OptionExt, if_callable_const,
    entry_of_until, single_result_assign, find_bytes, read_u32_at, if_arithmetic_eq_neq,
    bumpvec_with_capacity, OperandExt, FunctionFinder, is_global,
};
use crate::switch::CompleteSwitch;
use crate::struct_layouts;

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

pub(crate) fn print_text<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_commands_switch: &CompleteSwitch<'e>,
) -> Option<E::VirtualAddress> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        arg1: Operand<'e>,
        arg2: Operand<'e>,
        ctx: OperandCtx<'e>,
        result: Option<E::VirtualAddress>,
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    if let Some(dest) = dest.if_constant() {
                        let arg1 = ctrl.resolve(self.arg1);
                        let arg2 = ctrl.resolve(self.arg2);
                        if let Some(mem) = arg2.if_mem8() {
                            let offset_1 =
                                mem.with_offset_size(1, MemAccessSize::Mem8).address_op(self.ctx);
                            if offset_1 == arg1 {
                                let dest = E::VirtualAddress::from_u64(dest);
                                if single_result_assign(Some(dest), &mut self.result) {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
                Operation::Jump { to, .. } => {
                    if to.if_memory().is_some() {
                        ctrl.end_branch();
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // print_text is called for packet 0x5c as print_text(data + 2, data[1])
    let branch = process_commands_switch.branch(binary, ctx, 0x5c)?;

    let mut analyzer = Analyzer::<E> {
        arg1: analysis.arg_cache.on_call(0),
        arg2: analysis.arg_cache.on_call(1),
        ctx,
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, branch);
    analysis.analyze(&mut analyzer);
    analyzer.result
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
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;

    // Search for stim button action
    let stim_funcs = firegraft.buttonsets.iter().filter_map(|&buttons| {
        binary.read_address(buttons + E::VirtualAddress::SIZE).ok()
    }).filter_map(|marine_buttons| {
        let button_size = struct_layouts::button_size::<E::VirtualAddress>();
        let action_offset = struct_layouts::button_action_func::<E::VirtualAddress>();
        binary.read_address(marine_buttons + 5 * button_size + action_offset).ok()
    });

    let mut result = None;
    for stim_func in stim_funcs {
        let mut analysis = FuncAnalysis::new(binary, ctx, stim_func);
        let mut analyzer = FindSendCommand {
            result: None,
            binary,
            arg_cache,
            is_inlining: false,
        };
        analysis.analyze(&mut analyzer);
        if single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    result
}

struct FindSendCommand<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    is_inlining: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSendCommand<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = if_callable_const(self.binary, dest, ctrl) {
                    // Check if calling send_command(&[COMMAND_STIM], 1)
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let arg1_addr = ctx.mem_access(arg1, 0, MemAccessSize::Mem8);
                    let arg1_inner = ctrl.read_memory(&arg1_addr);
                    if arg1_inner.if_constant() == Some(0x36) {
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
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
                if let Operation::Move(_, value, None) = *op {
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
            Operation::Move(ref dest, _, _) => {
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

#[derive(Default, Copy, Clone, Debug)]
struct IsReplayState<'e> {
    possible_result: Option<Operand<'e>>,
}

impl<'e> analysis::AnalysisState for IsReplayState<'e> {
    fn merge(&mut self, newer: Self) {
        if self.possible_result != newer.possible_result {
            self.possible_result = None;
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsReplayAnalyzer<'acx, 'e, E> {
    type State = IsReplayState<'e>;
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
            Operation::Move(_, val, _) => {
                if ctrl.user_state().possible_result.is_some() {
                    let val = ctrl.resolve(val);
                    let is_ok = val.if_mem32_offset(1).is_some();
                    if is_ok {
                        let new = ctrl.user_state().possible_result;
                        if single_result_assign(new, &mut self.result) {
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

                ctrl.user_state().possible_result = other;
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
    let arg_cache = &analysis.arg_cache;

    let exec_state = E::initial_state(ctx, binary);
    let state = StepNetworkState {
        after_receive_storm_turns: false,
    };
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, step_network, exec_state, state);
    let mut analyzer = AnalyzeStepNetwork::<E> {
        result: &mut result,
        arg_cache,
        inlining: false,
        process_command_inline_depth: 0,
        inline_limit: 0,
        storm_command_user_candidate: None,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeStepNetwork<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepNetwork<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining: bool,
    process_command_inline_depth: u8,
    inline_limit: u8,
    storm_command_user_candidate: Option<Operand<'e>>,
}

#[derive(Default, Clone, Debug)]
struct StepNetworkState {
    after_receive_storm_turns: bool,
}

impl analysis::AnalysisState for StepNetworkState {
    fn merge(&mut self, newer: Self) {
        self.after_receive_storm_turns |= newer.after_receive_storm_turns;
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeStepNetwork<'a, 'e, E> {
    type State = StepNetworkState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.result.network_ready.is_none() {
            if ctrl.user_state().after_receive_storm_turns {
                if let Operation::Move(ref dest, val, None) = *op {
                    if let DestOperand::Memory(mem) = dest {
                        let ctx = ctrl.ctx();
                        if ctrl.resolve(val) == ctx.const_1() {
                            self.result.network_ready = Some(ctx.memory(&ctrl.resolve_mem(mem)));
                        }
                    }
                } else if let Operation::Call(_) = op {
                    ctrl.user_state().after_receive_storm_turns = false;
                }
            } else {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        // Check that receive_storm_turns didn't get inlined.
                        // receive_storm_turns calls storm_122 with same arguments
                        // but adds arg6 = 4.
                        let ok = Some(ctrl.resolve(self.arg_cache.on_call(0)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                            .filter(|x| x.if_constant() == Some(0xc))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(5)))
                            .filter(|x| x.if_constant() != Some(0x4))
                            .is_some();
                        if ok {
                            let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                            let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                            let arg5 = ctrl.resolve(self.arg_cache.on_call(4));
                            let ok = arg3.if_constant().is_some() &&
                                arg4.if_constant().is_some() &&
                                arg5.if_constant().is_some();
                            if ok {
                                self.result.receive_storm_turns = Some(dest);
                                self.result.player_turns = Some(arg3);
                                self.result.player_turns_size = Some(arg4);
                                self.result.net_player_flags = Some(arg5);
                                ctrl.user_state().after_receive_storm_turns = true;
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
                        let arg_cache = self.arg_cache;
                        let ok =
                            ctrl.resolve(arg_cache.on_call(0)).if_memory()
                                .filter(|&x| {
                                    x.size == E::WORD_SIZE &&
                                        Some(ctx.mem_sub_const_op(
                                            &x,
                                            7 * E::VirtualAddress::SIZE as u64,
                                        )) == self.result.player_turns
                                })
                                .and_then(|_| ctrl.resolve(arg_cache.on_call(1)).if_mem32())
                                .filter(|&x| {
                                    Some(ctx.mem_sub_const_op(x, 7 * 4)) ==
                                        self.result.player_turns_size
                                })
                                .filter(|_| {
                                    let cmp = match is_process_lobby_commands {
                                        true => 7,
                                        false => 0,
                                    };
                                    ctrl.resolve(arg_cache.on_call(2)).if_constant() == Some(cmp)
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
                                let this_ok = Some(ctrl.resolve(ctx.register(1))) ==
                                    self.result.player_turns;
                                let arg1 =
                                    ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                                let arg2 =
                                    ctrl.resolve(self.arg_cache.on_thiscall_call(1));
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
                        if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                            if ctrl.resolve(value).if_constant() == Some(7) {
                                let dest = ctrl.resolve_mem(mem);
                                if is_global(dest.address().0) {
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

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, branch);
    let mut analyzer = FindReplayData::<E> {
        result: None,
        limit: 6,
        inline_depth: 0,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindReplayData<'a, 'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    limit: u8,
    inline_depth: u8,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindReplayData<'a, 'e, E> {
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
                if ctrl.resolve(self.arg_cache.on_call(1)).if_constant() == Some(0xb) {
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
                if ctrl.resolve(self.arg_cache.on_call(2)).if_constant() == Some(0xb) {
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
