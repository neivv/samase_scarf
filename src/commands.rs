use scarf::{BinaryFile, DestOperand, Operand, OperandType, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};
use scarf::operand::{ArithOpType, MemAccessSize, OperandCtx};

use crate::{
    Analysis, ArgCache, EntryOf, EntryOfResult, OptionExt, if_callable_const, find_callers,
    entry_of_until, single_result_assign, find_bytes, read_u32_at, if_arithmetic_eq_neq,
};

#[derive(Clone, Debug)]
pub struct ProcessCommands<'e, Va: VirtualAddressTrait> {
    pub process_commands: Option<Va>,
    pub storm_command_user: Option<Operand<'e>>,
    pub switch: Option<crate::switch::CompleteSwitch<Va>>,
}

#[derive(Clone, Debug)]
pub struct Selections<'e> {
    pub unique_command_user: Option<Operand<'e>>,
    pub selections: Option<Operand<'e>>,
}

#[derive(Clone, Debug)]
pub struct StepNetwork<'e, Va: VirtualAddressTrait> {
    pub step_network: Option<Va>,
    pub receive_storm_turns: Option<Va>,
    pub menu_screen_id: Option<Operand<'e>>,
    pub net_player_flags: Option<Operand<'e>>,
    pub player_turns: Option<Operand<'e>>,
    pub player_turns_size: Option<Operand<'e>>,
    pub network_ready: Option<Operand<'e>>,
}

pub fn print_text<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
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
                        if let Some(addr) = arg2.if_mem8() {
                            let addr_plus_1 = self.ctx.add_const(addr, 1);
                            if addr_plus_1 == arg1 {
                                let dest =
                                    <E::VirtualAddress as VirtualAddressTrait>::from_u64(dest);
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

    // print_text is called for packet 0x5c as print_text(data + 2, data[1])
    let process_commands = analysis.process_commands();
    let switch = process_commands.switch.as_ref()?;
    let branch = switch.branch(0x5c)?;

    let binary = analysis.binary;
    let ctx = analysis.ctx;

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

pub fn command_lengths<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Vec<u32> {
    let rdata = analysis.binary.section(b".rdata\0\0").unwrap();
    let needle = [
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
    let results = find_bytes(&rdata.data, &needle[..]);
    test_assert_eq!(results.len(), 1);
    results.first().map(|&start| {
        let mut pos = needle.len() as u32;
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
    }).unwrap_or_else(|| Vec::new())
}

pub fn send_command<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let firegraft = analysis.firegraft_addresses();

    let binary = analysis.binary;
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;

    // Search for stim button action
    let stim_funcs = firegraft.buttonsets.iter().filter_map(|&buttons| {
        binary.read_address(buttons + 4).ok()
    }).filter_map(|marine_buttons| {
        binary.read_address(marine_buttons + 0x6c).ok()
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
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = if_callable_const(self.binary, dest, ctrl) {
                    // Check if calling send_command(&[COMMAND_STIM], 1)
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let arg1_inner = ctrl.resolve(ctrl.ctx().mem8(arg1));
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

pub fn process_commands<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> ProcessCommands<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];

    let switches = analysis.switch_tables().iter().filter(|switch| {
        switch.cases.len() >= 0x38 && switch.cases.len() < 0x60
    }).filter_map(|switch| {
        crate::switch::full_switch_info(analysis, switch).and_then(|(mut switch, entry)| {
            let offset = switch.cases.windows(0x1f).enumerate().find(|&(_, win)| {
                let low_bound = win[0];
                let high_bound = win[0x1e];
                let win = &win[1..];
                let first = win[0];
                let second = win[4];
                low_bound != high_bound && first != low_bound && first != high_bound &&
                    win.iter().cloned().take(4).all(|x| x == first) &&
                    win.iter().cloned().skip(4).take(8).all(|x| x == second) &&
                    win.iter().cloned().skip(0xd).take(3).all(|x| x == first) &&
                    win.iter().cloned().skip(0x11).take(12).all(|x| x == first)
            }).map(|(i, _)| switch.offset + i as u32 + switch.offset - 0x37);
            match offset {
                Some(x) => {
                    switch.offset = x;
                    Some((switch, entry))
                }
                None => None,
            }
        })
    }).collect::<Vec<_>>();
    let switches = switches.into_iter().flat_map(|(switch, process_commands)| {
        let switch = &switch;
        let mut callers = find_callers(analysis, process_commands)
            .into_iter()
            .map(move |caller| (switch.clone(), caller, process_commands))
            .collect::<Vec<_>>();
        callers.sort();
        callers.dedup();
        callers
    });
    let mut result = None;
    for (switch, caller, process_commands) in switches {
        let val = entry_of_until(binary, funcs, caller, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = FindStormCommandUser::<E> {
                result: None,
                call_found: false,
                caller,
            };
            analysis.analyze(&mut analyzer);
            if let Some(result) = analyzer.result {
                EntryOf::Ok((process_commands, result, switch.clone()))
            } else if analyzer.call_found {
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
        Some((a, b, c)) => ProcessCommands {
            process_commands: Some(a),
            storm_command_user: Some(b),
            switch: Some(c),
        },
        None => ProcessCommands {
            process_commands: None,
            storm_command_user: None,
            switch: None,
        },
    }
}

struct FindStormCommandUser<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    call_found: bool,
    caller: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindStormCommandUser<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(ref dest, val, _) => {
                if let DestOperand::Memory(mem) = dest {
                    let val = ctrl.resolve(val);
                    if val.if_constant() == Some(7) {
                        let dest = ctrl.resolve(mem.address);
                        if op_is_fully_defined(dest) {
                            self.result = Some(ctrl.ctx().mem32(dest));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Call(..) => {
                if ctrl.address() == self.caller {
                    self.call_found = true;
                }
            }
            _ => (),
        }
    }
}

fn op_is_fully_defined(op: Operand<'_>) -> bool {
    op.iter().all(|x| match x.ty() {
        OperandType::Memory(_) | OperandType::Constant(_) | OperandType::Arithmetic(_) => true,
        _ => false
    })
}

pub fn command_user<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let process_commands = analysis.process_commands();
    let game = analysis.game()?;
    process_commands.switch.as_ref().and_then(|sw| {
        let command_ally = sw.branch(0xe)?;
        let mut analysis = FuncAnalysis::new(binary, ctx, command_ally);
        let mut analyzer = CommandUserAnalyzer::<E> {
            result: None,
            inlining: false,
            game,
            phantom: Default::default(),
        };
        analysis.analyze(&mut analyzer);
        analyzer.result
    })
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
                        let addr = ctrl.resolve(mem.address);
                        let offset = ctrl.ctx().sub(addr, self.game);
                        let command_user = offset.if_arithmetic_add()
                            .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                            .and_then(|(c, other)| match c == 0xe544 {
                                true => other.if_arithmetic_mul(),
                                false => None,
                            })
                            .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                            .and_then(|(c, other)| match c == 0xc {
                                true => Some(other),
                                false => None,
                            });
                        if single_result_assign(command_user, &mut self.result) {
                            ctrl.end_analysis();
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

pub fn selections<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Selections<'e> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let process_commands = analysis.process_commands();
    let mut result = Selections {
        selections: None,
        unique_command_user: None,
    };
    let cancel_nuke_command = process_commands.switch.as_ref()
        .and_then(|sw| sw.branch(0x2e));
    let cancel_nuke = match cancel_nuke_command {
        Some(s) => s,
        None => return result,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, cancel_nuke);
    let mut analyzer = SelectionsAnalyzer::<E> {
        sel_state: SelectionState::Start,
        result: &mut result,
        checked_calls: Vec::new(),
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

enum SelectionState<'e> {
    Start,
    LimitJumped(Operand<'e>),
}

struct SelectionsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut Selections<'e>,
    sel_state: SelectionState<'e>,
    checked_calls: Vec<E::VirtualAddress>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SelectionsAnalyzer<'a, 'e, E> {
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
                    let x = condition.if_arithmetic_eq()
                        .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                        .and_then(|(c, other)| match c == 0 {
                            true => Some(other),
                            false => None,
                        })
                        .and_then(|other| other.if_memory())
                        .and_then(|mem| mem.address.if_arithmetic_add())
                        .and_then(|(l, r)| Operand::either(l, r, |x| x.if_arithmetic_mul()));
                    if let Some(((l, r), selections)) = x {
                        let unique_command_user = Operand::either(l, r, |x| x.if_constant())
                            .and_then(|(c, other)| match c == 4 {
                                true => Some(other),
                                false => None,
                            })
                            .and_then(|other| other.if_arithmetic_add())
                            .and_then(|(l, r)| {
                                Operand::either(l, r, |x| match x == selection_pos {
                                    true => Some(()),
                                    false => None,
                                })
                            })
                            .and_then(|((), other)| other.if_arithmetic_mul())
                            .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                            .and_then(|(c, other)| match c == 0xc {
                                true => Some(other),
                                false => None,
                            });
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

pub fn is_replay<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let process_commands = analysis.process_commands();
    let command = process_commands.switch.as_ref()
        .and_then(|sw| sw.branch(0x5d))?;

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
        checked_calls: Vec::new(),
        result: None,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct IsReplayAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    checked_calls: Vec<E::VirtualAddress>,
    inline_depth: u8,
}

#[derive(Default, Clone, Debug)]
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

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsReplayAnalyzer<'e, E> {
    type State = IsReplayState<'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth < 2 {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
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
                    let is_ok = val.if_mem32()
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_either(|x| x.if_constant().filter(|&c| c == 1))
                        .is_some();
                    if is_ok {
                        let new = ctrl.user_state().possible_result.clone();
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
                let other = condition.if_arithmetic_eq()
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                    .filter(|other| other.iter().all(|x| !x.is_undefined()));

                ctrl.user_state().possible_result = other;
            }
            _ => (),
        }
    }
}

pub fn step_network<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> StepNetwork<'e, E::VirtualAddress> {
    let mut result = StepNetwork {
        step_network: None,
        receive_storm_turns: None,
        menu_screen_id: None,
        net_player_flags: None,
        player_turns: None,
        player_turns_size: None,
        network_ready: None,
    };
    let process_lobby_commands = match analysis.process_lobby_commands() {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    // step_network calls process_lobby_commands 2~3 frames deep
    // Recognize step_network from its first comparision being
    // menu_screen_id == MENU_SCREEN_EXIT (0x21 currently, but allow matching higher constants,
    // 1.16.1 had 0x19)
    let mut repeat_limit = 3;
    let mut entries = vec![process_lobby_commands];
    'outer: while repeat_limit > 0 {
        repeat_limit -= 1;
        let mut new_entries = Vec::new();
        for child in entries {
            let callers = find_callers(analysis, child);
            for caller in callers {
                let val = entry_of_until(binary, funcs, caller, |entry| {
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    let mut analyzer = IsStepNetwork::<E> {
                        result: EntryOf::Retry,
                        child,
                        inlining: false,
                        first_branch: true,
                    };
                    analysis.analyze(&mut analyzer);
                    analyzer.result
                });
                match val {
                    EntryOfResult::Ok(a, menu_screen_id) => {
                        result.step_network = Some(a);
                        result.menu_screen_id = Some(menu_screen_id);
                        break 'outer;
                    }
                    EntryOfResult::Entry(e) => {
                        new_entries.push(e);
                    }
                    EntryOfResult::None => (),
                }
            }
        }
        entries = new_entries;
        entries.sort();
        entries.dedup();
    }
    let arg_cache = &analysis.arg_cache;
    if let Some(step_network) = result.step_network {
        let exec_state = E::initial_state(ctx, binary);
        let state = StepNetworkState {
            after_receive_storm_turns: false,
        };
        let mut analysis =
            FuncAnalysis::custom_state(binary, ctx, step_network, exec_state, state);
        let mut analyzer = AnalyzeStepNetwork::<E> {
            result: &mut result,
            arg_cache,
            inlining: false,
        };
        analysis.analyze(&mut analyzer);
    }
    result
}

struct IsStepNetwork<'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    child: E::VirtualAddress,
    inlining: bool,
    first_branch: bool,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStepNetwork<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.first_branch {
                        if !self.inlining {
                            self.inlining = true;
                            ctrl.inline(self, dest);
                            self.inlining = false;
                            ctrl.skip_operation();
                        }
                    } else {
                        if self.child == dest {
                            self.result = EntryOf::Stop;
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.first_branch {
                    let condition = ctrl.resolve(condition);
                    let menu_screen_id = if_arithmetic_eq_neq(condition)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c > 0x20 && c < 0x80));
                    if let Some(menu_screen_id) = menu_screen_id {
                        self.result = EntryOf::Ok(menu_screen_id.clone());
                        ctrl.end_analysis();
                    }
                    self.first_branch = false;
                }
            }
            _ => (),
        }
    }
}

struct AnalyzeStepNetwork<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepNetwork<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining: bool,
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
        if ctrl.user_state().after_receive_storm_turns {
            if let Operation::Move(ref dest, val, None) = *op {
                if let DestOperand::Memory(mem) = dest {
                    if ctrl.resolve(val).if_constant() == Some(1) {
                        self.result.network_ready =
                            Some(ctrl.ctx().mem_variable_rc(mem.size, mem.address));
                        ctrl.end_analysis();
                    }
                }
            } else if let Operation::Call(_) = op {
                ctrl.user_state().after_receive_storm_turns = false;
            }
        } else {
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
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
                        if self.result.receive_storm_turns.is_some() {
                            ctrl.end_analysis();
                        }
                        self.inlining = false;
                    }
                }
            }
        }
    }
}
