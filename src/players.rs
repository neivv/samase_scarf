use std::rc::Rc;

use smallvec::SmallVec;

use scarf::{DestOperand, Operand, OperandContext, Operation, VirtualAddress, ExecutionStateX86};
use scarf::analysis::{self, AnalysisState, Control, FuncAnalysis};
use scarf::operand::{MemAccess, MemAccessSize, OperandType, Register, ArithOpType};
use scarf::operand_helpers::*;

use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};

use crate::{Analysis};
use crate::OptionExt;

type BinaryFile = scarf::BinaryFile<VirtualAddress>;

#[derive(Default)]
pub struct NetPlayers {
    // Array, struct size
    pub net_players: Option<(Rc<Operand>, usize)>,
    pub init_net_player: Option<VirtualAddress>,
}

// Search for `player_ai_flags |= 0x2`
// followed by `cmp player_type, 0x1`
#[derive(Copy, Clone)]
enum PlayersState {
    Start,
    PlayerAiFlagsUpdated,
}
impl AnalysisState for PlayersState {
    fn merge(&mut self, newer: PlayersState) {
        if let PlayersState::PlayerAiFlagsUpdated = newer {
            *self = newer;
        }
    }
}

struct PlayersAnalyzer<'a> {
    result: Option<Rc<Operand>>,
    ctx: &'a OperandContext,
    in_child_func: bool,
    child_func_state: Option<PlayersState>,
}

impl<'a> scarf::Analyzer<'a> for PlayersAnalyzer<'a> {
    type State = PlayersState;
    type Exec = ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Jump { to, condition } => {
                let condition = ctrl.resolve(condition);
                if condition.if_constant().unwrap_or(0) != 0 {
                    if to.if_memory().is_some() {
                        // Reached switch jump?
                        ctrl.end_analysis();
                    }
                }
                if let PlayersState::PlayerAiFlagsUpdated = ctrl.user_state() {
                    // Mem8[players + player_id * 0x24 + 8] == 1
                    let players = condition.if_arithmetic_eq()
                        .and_then(|(l, r)| {
                            // Accept both (x == 1) == 0 and (x == 1)
                            Operand::either(l, r, |x| x.if_constant())
                                .and_then(|(c, other)| match c {
                                    0 => {
                                        other.if_arithmetic_eq()
                                            .and_either_other(|x| {
                                                x.if_constant().filter(|&c| c == 1)
                                            })
                                    }
                                    1 => Some(other),
                                    _ => None
                                })
                        })
                        .and_then(|x| x.if_mem8())
                        .and_then(|addr| collect_arith_add_terms(addr))
                        .filter(|terms| terms.constant >= 8)
                        .and_then(|mut terms| {
                            let ok = terms.remove_one(|x, negate| {
                                // Don't accept (x & 0x7f) * 0x24 (Observer ids)
                                !negate && x.if_arithmetic_mul()
                                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0x24))
                                    .filter(|x| x.if_arithmetic_and().is_none())
                                    .is_some()
                            });
                            if ok {
                                terms.constant -= 8;
                                Some(Operand::simplified(terms.join(self.ctx)))
                            } else {
                                None
                            }
                        });
                    if crate::single_result_assign(players, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Call(dest) => {
                if !self.in_child_func {
                    if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                        self.in_child_func = true;
                        let dest = VirtualAddress::from_u64(dest);
                        ctrl.analyze_with_current_state(self, dest);
                        if let Some(state) = self.child_func_state.take() {
                            *ctrl.user_state() = state;
                        }
                        if self.result.is_some() && !crate::test_assertions() {
                            ctrl.end_analysis();
                        }
                        self.in_child_func = false;
                    }
                }
            }
            Operation::Move(to, val, None) => {
                match ctrl.user_state() {
                    PlayersState::Start => if let DestOperand::Memory(mem) = to {
                        let val = ctrl.resolve(val);
                        let is_or_const_2 = val.if_arithmetic_or()
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 2))
                            .and_then(|other| other.if_memory())
                            .map(|mem| &mem.address);
                        if let Some(other_addr) = is_or_const_2 {
                            let addr = ctrl.resolve(&mem.address);
                            if addr == *other_addr {
                                *ctrl.user_state() = PlayersState::PlayerAiFlagsUpdated;
                                self.child_func_state = Some(PlayersState::PlayerAiFlagsUpdated);
                            }
                        }
                    },
                    PlayersState::PlayerAiFlagsUpdated => (),
                }
            }
            _ => (),
        }
    }
}

pub fn players<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> Option<Rc<Operand>> {
    let binary = analysis.binary;
    let aiscript = analysis.aiscript_hook();
    let aiscript = (*aiscript).as_ref()?;
    let start_town_case = VirtualAddress(binary.read_u32(aiscript.switch_table + 0x3 * 4).ok()?);

    let mut analyzer = PlayersAnalyzer {
        result: None,
        ctx,
        in_child_func: false,
        child_func_state: None,
    };

    let mut interner = scarf::exec_state::InternMap::new();
    let exec_state = ExecutionStateX86::new(ctx, &mut interner);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        start_town_case,
        exec_state,
        PlayersState::Start,
        interner,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}


struct AddTerms<'a> {
    terms: SmallVec<[(&'a Rc<Operand>, bool); 8]>,
    constant: u64,
}

impl<'a> AddTerms<'a> {
    fn collect(&mut self, operand: &'a Rc<Operand>, negate: bool) {
        match operand.ty {
            OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Add => {
                self.collect(&arith.left, negate);
                self.collect(&arith.right, negate);
            }
            OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Sub => {
                self.collect(&arith.left, negate);
                self.collect(&arith.right, !negate);
            }
            OperandType::Constant(c) => {
                if negate {
                    self.constant = self.constant.wrapping_sub(c);
                } else {
                    self.constant = self.constant.wrapping_add(c);
                }
            }
            _ => self.terms.push((operand, negate)),
        }
    }

    pub fn remove_one<F>(&mut self, mut func: F) -> bool
    where F: FnMut(&'a Rc<Operand>, bool) -> bool
    {
        let remove_index = match self.terms.iter().position(|x| func(x.0, x.1)) {
            Some(s) => s,
            None => return false,
        };
        if self.terms.iter().skip(remove_index + 1).any(|x| func(x.0, x.1)) {
            return false;
        }
        self.terms.remove(remove_index);
        true
    }

    pub fn join(&self, ctx: &OperandContext) -> Rc<Operand> {
        use scarf::operand_helpers::*;
        let mut tree = match self.terms.get(0) {
            Some(&(op, negate)) => if negate {
                operand_sub(ctx.constant(self.constant), op.clone())
            } else {
                if self.constant == 0 {
                    op.clone()
                } else {
                    operand_add(ctx.constant(self.constant), op.clone())
                }
            },
            None => return ctx.constant(self.constant),
        };
        for &(op, neg) in self.terms.iter().skip(1) {
            tree = match neg {
                false => operand_add(tree, op.clone()),
                true => operand_sub(tree, op.clone()),
            };
        }
        Operand::simplified(tree)
    }
}

fn collect_arith_add_terms<'a>(operand: &'a Rc<Operand>) -> Option<AddTerms<'a>> {
    let mut terms = AddTerms {
        terms: Default::default(),
        constant: 0,
    };
    match operand.ty {
        OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Add => {
            terms.collect(&arith.left, false);
            terms.collect(&arith.right, false);
            Some(terms)
        }
        OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Sub => {
            terms.collect(&arith.left, false);
            terms.collect(&arith.right, true);
            Some(terms)
        }
        _ => None,
    }
}

pub fn local_player_id<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Rc<Operand>> {
    #[derive(Copy, Clone)]
    enum State {
        Start,
        PlayerFieldAccessSeen,
    }

    impl AnalysisState for State {
        fn merge(&mut self, newer: State) {
            if let State::PlayerFieldAccessSeen = newer {
                *self = newer;
            }
        }
    }

    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<Rc<Operand>>,
        in_child_func: bool,
        child_func_state: Option<State>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }

    // Search for [primary_selection].player access followed by
    // jump condition [local_player_id] == player
    // Since the full code is `player = if unit { unit.player } else { 0xff }`,
    // [local_player_id] == player comparision can't be relied to have actual
    // field memaccess for `player`, it can be undefined or 0xff as well.
    // Hopefully local_player_id doesn't become ever encrypted..
    impl<'a, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, E> {
        type State = State;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            fn is_maybe_player_op(mem: &MemAccess) -> bool {
                let has_add = mem.address.if_arithmetic_add()
                    .and_either(|x| x.if_constant().filter(|&c| c == 0x4c))
                    .is_some();
                mem.size == MemAccessSize::Mem8 && has_add
            }

            match op {
                Operation::Jump { condition, .. } => {
                    if let State::PlayerFieldAccessSeen = ctrl.user_state() {
                        let condition = ctrl.resolve(condition);
                        let local_player_id = crate::if_arithmetic_eq_neq(&condition)
                            .and_then(|(l, r, _eq)| {
                                // if the comparision ends up being
                                // [local_player_id] == [unit + 0x4c], check for
                                // 0x4c add in address
                                Operand::either(l, r, |x| {
                                    x.if_memory()
                                        .filter(|mem| !is_maybe_player_op(mem))
                                        .map(|_| x)
                                })
                            })
                            .map(|(mem, _)| mem.clone());
                        if crate::single_result_assign(local_player_id, &mut self.result) {
                            ctrl.end_analysis();
                        } else {
                            // Still end the branch on test builds
                            if self.result.is_some() {
                                ctrl.end_branch();
                            }
                        }
                    }
                }
                Operation::Call(dest) => {
                    if !self.in_child_func {
                        if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                            self.in_child_func = true;
                            let dest = E::VirtualAddress::from_u64(dest);
                            ctrl.analyze_with_current_state(self, dest);
                            if let Some(state) = self.child_func_state.take() {
                                *ctrl.user_state() = state;
                            }
                            self.in_child_func = false;
                        }
                    }
                }
                Operation::Move(_, val, None) => {
                    match ctrl.user_state() {
                        State::Start => {
                            let val = ctrl.resolve(val);
                            let has_player_field_access = val.iter_no_mem_addr()
                                .any(|x| {
                                    x.if_mem8()
                                        .and_then(|addr| addr.if_arithmetic_add())
                                        .and_either_other(|x| {
                                            x.if_constant().filter(|&c| c == 0x4c)
                                        })
                                        .and_then(|x| x.if_mem32())
                                        .is_some()
                                });
                            if has_player_field_access {
                                *ctrl.user_state() = State::PlayerFieldAccessSeen;
                            }
                        }
                        State::PlayerFieldAccessSeen => (),
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let rclick = analysis.game_screen_rclick().game_screen_rclick?;

    let mut analyzer = Analyzer {
        result: None,
        in_child_func: false,
        child_func_state: None,
        phantom: Default::default(),
    };

    let mut interner = scarf::exec_state::InternMap::new();
    let exec_state = E::initial_state(ctx, binary, &mut interner);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        rclick,
        exec_state,
        State::Start,
        interner,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindInitNetPlayer {
    result: Option<VirtualAddress>,
    arg3: Rc<Operand>,
    arg4: Rc<Operand>,
    in_child_func: bool,
}

impl<'a> scarf::Analyzer<'a> for FindInitNetPlayer {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Jump { to, .. } => {
                if to.if_memory().is_some() {
                    // Don't go through switch
                    ctrl.end_branch();
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                    let dest = VirtualAddress::from_u64(dest);
                    // Check that
                    // arg3 == mem16[data + 4],
                    // arg4 == mem16[data + 6],
                    let arg3 = ctrl.resolve(&self.arg3);
                    let arg4 = ctrl.resolve(&self.arg4);
                    let arg3_base = arg3.if_mem16()
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 4));
                    let arg4_base = arg4.if_mem16()
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 6));
                    match (arg3_base, arg4_base) {
                        (Some(a), Some(b)) if a == b => {
                            if crate::single_result_assign(Some(dest), &mut self.result) {
                                ctrl.end_analysis();
                            }
                        }
                        _ => (),
                    }
                    if !self.in_child_func {
                        self.in_child_func = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.in_child_func = false;
                    }
                }
            }
            _ => (),
        }
    }
}

struct FindNetPlayerArr<'exec> {
    result: Option<(Rc<Operand>, usize)>,
    binary: &'exec BinaryFile,
    ctx: &'exec OperandContext,
    delay_eax_move: Option<Rc<Operand>>,
}

impl<'exec> scarf::Analyzer<'exec> for FindNetPlayerArr<'exec> {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'exec>;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
        fn is_arg1(operand: &Rc<Operand>) -> bool {
            operand.if_memory()
                .and_then(|x| x.address.if_arithmetic_add())
                .and_either_other(|x| x.if_constant().filter(|&c| c == 4))
                .and_then(|x| x.if_register())
                .filter(|x| x.0 == 4)
                .is_some()
        }
        fn base_mul(operand: &Rc<Operand>) -> Option<(&Rc<Operand>, u64, &Rc<Operand>)> {
            operand
                .if_arithmetic_add()
                .and_either(|x| {
                    x.if_arithmetic_mul()
                        .and_either(|x| x.if_constant())
                })
                .map(|((mul, other), base)| {
                    (base, mul, other)
                })
        }
        if let Some(value) = self.delay_eax_move.take() {
            let exec_state = ctrl.exec_state();
            let eax = DestOperand::Register64(Register(0));
            exec_state.0.move_resolved(&eax, value, exec_state.1);
        }
        match op {
            Operation::Call(dest) => {
                if crate::seems_assertion_call(ctrl, self.binary) {
                    return;
                }
                if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                    let mut analyzer = CollectReturnValues::new(self.ctx);
                    ctrl.analyze_with_current_state(&mut analyzer, VirtualAddress::from_u64(dest));
                    if !analyzer.return_values.is_empty() {
                        if let Some((base, mul, other)) = base_mul(&analyzer.return_values[0]) {
                            let mut arg1_seen = is_arg1(other);
                            let mut base = base;
                            let all_match = (&analyzer.return_values[1..]).iter().all(|other| {
                                match base_mul(other) {
                                    Some(o) => {
                                        if is_arg1(&o.2) {
                                            arg1_seen = true;
                                            base = o.0;
                                        }
                                        o.1 == mul
                                    }
                                    None => false,
                                }
                            });
                            if all_match && arg1_seen {
                                self.delay_eax_move = Some(operand_add(
                                    base.clone(),
                                    operand_mul(
                                        self.ctx.constant(mul),
                                        mem32(operand_add(
                                            self.ctx.register(4),
                                            self.ctx.const_4(),
                                        )),
                                    ),
                                ));
                            }
                        }
                    }
                }
            }
            Operation::Move(dest, val, None) => {
                // Check for Mem16[base + arg1 * mul + 6] = arg4
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem16 {
                        let addr = ctrl.resolve(&mem.address);
                        let val = ctrl.resolve(&val);
                        let is_arg4 = val.if_memory()
                            .and_then(|x| x.address.if_arithmetic_add())
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 0x10))
                            .and_then(|x| x.if_register())
                            .filter(|x| x.0 == 4)
                            .is_some();
                        if is_arg4 {
                            if let Some((base, size, rest)) = base_mul(&addr) {
                                if is_arg1(&rest) {
                                    let base = Operand::simplified(operand_sub(
                                        base.clone(),
                                        self.ctx.constant(6),
                                    ));
                                    self.result = Some((base, size as usize));
                                }
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

struct CollectReturnValues {
    eax: Rc<Operand>,
    return_values: Vec<Rc<Operand>>,
}

impl CollectReturnValues {
    fn new(ctx: &OperandContext) -> CollectReturnValues {
        CollectReturnValues {
            return_values: Vec::with_capacity(4),
            eax: ctx.register(0),
        }
    }
}

impl<'exec> scarf::Analyzer<'exec> for CollectReturnValues {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'exec>;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
        if let Operation::Return(..) = op {
            let eax = ctrl.resolve(&self.eax);
            self.return_values.push(eax);
        }
    }
}

pub fn net_players<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> NetPlayers {
    let mut result = NetPlayers::default();
    let lobby_cmd_switch = match analysis.process_lobby_commands_switch() {
        Some(s) => s.0,
        None => return result,
    };
    let cmd_3f = match lobby_cmd_switch.branch(0x3f) {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let mut analyzer = FindInitNetPlayer {
        result: None,
        arg3: mem32(operand_add(ctx.register(4), ctx.const_8())),
        arg4: mem32(operand_add(ctx.register(4), ctx.constant(0xc))),
        in_child_func: false,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, cmd_3f);
    analysis.analyze(&mut analyzer);
    result.init_net_player = analyzer.result;
    if let Some(init_net_player) = analyzer.result {
        let mut analyzer = FindNetPlayerArr {
            result: None,
            binary,
            ctx,
            delay_eax_move: None,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, init_net_player);
        analysis.analyze(&mut analyzer);
        result.net_players = analyzer.result;
    }
    result
}
