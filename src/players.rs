use bumpalo::collections::Vec as BumpVec;

use scarf::{DestOperand, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{MemAccessSize};

use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::analysis_state::{AnalysisState, StateEnum, LocalPlayerState};
use crate::struct_layouts;
use crate::switch::CompleteSwitch;
use crate::analysis::{AnalysisCtx, ArgCache};
use crate::util::{
    ControlExt, OptionExt, OperandExt, bumpvec_with_capacity, seems_assertion_call,
    single_result_assign,
};

pub struct NetPlayers<'e, Va: VirtualAddress> {
    // Array, struct size
    pub net_players: Option<(Operand<'e>, usize)>,
    pub init_net_player: Option<Va>,
}

pub(crate) fn local_player_id<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    rclick: E::VirtualAddress,
) -> Option<Operand<'e>> {
    struct Analyzer<'acx, 'e, E: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        in_child_func: bool,
        phantom: std::marker::PhantomData<(*const E, &'e (), &'acx ())>,
    }

    // Search for [primary_selection].player access followed by
    // jump condition [local_player_id] == player
    // Since the full code is `player = if unit { unit.player } else { 0xff }`,
    // [local_player_id] == player comparision can't be relied to have actual
    // field memaccess for `player`, it can be undefined or 0xff as well.
    // Hopefully local_player_id doesn't become ever encrypted..
    impl<'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'acx, 'e, E> {
        type State = AnalysisState<'acx, 'e>;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Jump { condition, .. } => {
                    if let LocalPlayerState::PlayerFieldAccessSeen =
                        ctrl.user_state().get::<LocalPlayerState>()
                    {
                        let condition = ctrl.resolve(condition);
                        let local_player_id = condition.if_arithmetic_eq_neq()
                            .and_then(|(l, r, _)| {
                                Some((l, r))
                                    .and_either_other(|x| {
                                        // Check for [local_player_id] == player
                                        x.if_mem8_offset(
                                                struct_layouts::unit_player::<E::VirtualAddress>()
                                            )
                                    })
                                    .or_else(|| {
                                        // Check for [local_player_id] == 0xff or undef
                                        Some((l, r))
                                            .and_if_either_other(|x| {
                                                x.if_constant() == Some(0xff) ||
                                                    x.is_undefined()
                                            })
                                    })

                            })
                            .filter(|x| x.if_memory().is_some());
                        if single_result_assign(local_player_id, &mut self.result) {
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.in_child_func = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.in_child_func = false;
                        }
                    }
                }
                Operation::Move(_, val, None) => {
                    match *ctrl.user_state().get::<LocalPlayerState>() {
                        LocalPlayerState::Start => {
                            let val = ctrl.resolve(val);
                            let has_player_field_access = val.iter_no_mem_addr()
                                .any(|x| {
                                    x.if_mem8_offset(
                                            struct_layouts::unit_player::<E::VirtualAddress>()
                                        )
                                        .and_then(|x| ctrl.if_mem_word(x))
                                        .is_some()
                                });
                            if has_player_field_access {
                                ctrl.user_state().set(LocalPlayerState::PlayerFieldAccessSeen);
                            }
                        }
                        LocalPlayerState::PlayerFieldAccessSeen => (),
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut analyzer = Analyzer {
        result: None,
        in_child_func: false,
        phantom: Default::default(),
    };

    let state = AnalysisState::new(bump, StateEnum::LocalPlayerId(LocalPlayerState::Start));
    let exec_state = E::initial_state(ctx, binary);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        rclick,
        exec_state,
        state,
    );
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindInitNetPlayer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    in_child_func: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindInitNetPlayer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { to, .. } => {
                if to.if_memory().is_some() {
                    // Don't go through switch
                    ctrl.end_branch();
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    // Check that
                    // arg3 == mem16[data + 4],
                    // arg4 == mem16[data + 6],
                    let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                    let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                    let arg3_base = arg3.if_mem16_offset(4);
                    let arg4_base = arg4.if_mem16_offset(6);
                    match (arg3_base, arg4_base) {
                        (Some(a), Some(b)) if a == b => {
                            if single_result_assign(Some(dest), &mut self.result) {
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

struct FindNetPlayerArr<'acx, 'e, E: ExecutionState<'e>> {
    result: Option<(Operand<'e>, usize)>,
    delay_eax_move: Option<Operand<'e>>,
    bump: &'acx bumpalo::Bump,
    arg_cache: &'acx ArgCache<'e, E>,
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindNetPlayerArr<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn base_mul<'e>(operand: Operand<'e>) -> Option<(Operand<'e>, u64, Operand<'e>)> {
            operand
                .if_arithmetic_add()
                .and_either(|x| x.if_mul_with_const())
                .map(|((other, mul), base)| {
                    (base, mul, other)
                })
        }
        if let Some(value) = self.delay_eax_move.take() {
            let exec_state = ctrl.exec_state();
            let eax = DestOperand::Register64(0);
            exec_state.move_resolved(&eax, value);
        }
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if seems_assertion_call(ctrl, self.arg_cache) {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let mut analyzer = CollectReturnValues::<E>::new(self.bump);
                    ctrl.analyze_with_current_state(&mut analyzer, dest);
                    if !analyzer.return_values.is_empty() {
                        if let Some((base, mul, other)) = base_mul(analyzer.return_values[0]) {
                            let mut arg1_seen = other == self.arg_cache.on_entry(0);
                            let mut base = base;
                            let all_match = (&analyzer.return_values[1..]).iter().all(|&other| {
                                match base_mul(other) {
                                    Some(o) => {
                                        if o.2 == self.arg_cache.on_entry(0) {
                                            arg1_seen = true;
                                            base = o.0;
                                        }
                                        o.1 == mul
                                    }
                                    None => false,
                                }
                            });
                            if all_match && arg1_seen {
                                self.delay_eax_move = Some(ctx.add(
                                    base,
                                    ctx.mul_const(
                                        self.arg_cache.on_entry(0),
                                        mul,
                                    ),
                                ));
                            }
                        }
                    }
                }
            }
            Operation::Move(ref dest, val, None) => {
                // Check for Mem16[base + arg1 * mul + 6] = arg4
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem16 {
                        let addr = ctrl.resolve_mem(mem).address_op(ctx);
                        let val = ctrl.resolve(val);
                        if val == ctx.and_const(self.arg_cache.on_entry(3), 0xffff) {
                            if let Some((base, size, rest)) = base_mul(addr) {
                                if ctx.and_const(rest, 0xff) ==
                                    ctx.and_const(self.arg_cache.on_entry(0), 0xff)
                                {
                                    let base = ctx.sub_const(base, 6);
                                    self.result = Some((base, size as usize));
                                    ctrl.end_analysis();
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

struct CollectReturnValues<'acx, 'e, E: ExecutionState<'e>> {
    return_values: BumpVec<'acx, Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'acx, 'e, E: ExecutionState<'e>> CollectReturnValues<'acx, 'e, E> {
    fn new(bump: &'acx bumpalo::Bump) -> CollectReturnValues<'acx, 'e, E> {
        CollectReturnValues {
            return_values: bumpvec_with_capacity(4, bump),
            phantom: Default::default(),
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CollectReturnValues<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Return(..) = op {
            let eax = ctrl.ctx().register(0);
            let eax = ctrl.resolve(eax);
            self.return_values.push(eax);
        }
    }
}

pub(crate) fn net_players<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    lobby_cmd_switch: &CompleteSwitch<'e>,
) -> NetPlayers<'e, E::VirtualAddress> {
    let mut result = NetPlayers {
        net_players: None,
        init_net_player: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let cmd_3f = match lobby_cmd_switch.branch(binary, ctx, 0x3f) {
        Some(s) => s,
        None => return result,
    };
    let mut analyzer = FindInitNetPlayer {
        result: None,
        arg_cache: &actx.arg_cache,
        in_child_func: false,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, cmd_3f);
    analysis.analyze(&mut analyzer);
    result.init_net_player = analyzer.result;
    if let Some(init_net_player) = analyzer.result {
        let mut analyzer = FindNetPlayerArr::<E> {
            result: None,
            delay_eax_move: None,
            bump,
            arg_cache: &actx.arg_cache,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, init_net_player);
        analysis.analyze(&mut analyzer);
        result.net_players = analyzer.result;
    }
    result
}
