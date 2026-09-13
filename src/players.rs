use bumpalo::collections::Vec as BumpVec;

use scarf::{DestOperand, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{MemAccessSize};

use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::analysis_find::FunctionFinder;
use crate::analysis_state::{AnalysisState, StateEnum, LocalPlayerState};
use crate::switch::CompleteSwitch;
use crate::analysis::{AnalysisCtx, ArgCache};
use crate::util::{
    ControlExt, OptionExt, OperandExt, bumpvec_with_capacity, seems_assertion_call, ExecStateExt,
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
                                        x.if_mem8_offset(E::struct_layouts().unit_player())
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
                Operation::Move(_, val) => {
                    match *ctrl.user_state().get::<LocalPlayerState>() {
                        LocalPlayerState::Start => {
                            let val = ctrl.resolve(val);
                            let has_player_field_access = val.iter_no_mem_addr()
                                .any(|x| {
                                    x.if_mem8_offset(E::struct_layouts().unit_player())
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

struct FindInitNetPlayer<'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    in_child_func: bool,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindInitNetPlayer<'e, E> {
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
                if let Some(dest) = ctrl.resolve_va(dest) {
                    // Check that
                    // arg3 == mem16[data + 4],
                    // arg4 == mem16[data + 6],
                    let arg3 = ctrl.resolve_arg(2);
                    let arg4 = ctrl.resolve_arg(3);
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
            ctrl.set_register(0, value);
        }
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if seems_assertion_call(ctrl) {
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
            Operation::Move(ref dest, val) => {
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
    let mut analyzer = FindInitNetPlayer::<E> {
        result: None,
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

pub(crate) struct PlayerColorFuncs<'e, Va: VirtualAddress> {
    // get_player_color(out: *RGBA[4], player_id) resolves the color used to draw a player.
    // (get_player_color(out, local_player_id) covers the local player, so the near-identical
    // get_local_player_color wrapper isn't exposed separately.)
    pub get_player_color: Option<Va>,
    // get_force_color(out, force) -> force_colors[force - 1 clamped to 0..7]
    pub get_force_color: Option<Va>,
    // get_player_force_color(out, player): like get_player_color, but in color mode 2 tints by the
    // player's force/team (force_colors[player.force - 1]) rather than by relationship to the local
    // player; in other modes it just calls get_player_color. Used by minimap force markers and
    // player-list UI.
    pub get_player_force_color: Option<Va>,
    // The 8 team/force colors (the standard player colors). get_force_color / get_player_force_color
    // look up force_colors[player.force - 1] (clamped 0..7) to draw a player in its team's color in
    // color mode 2, where players are colored by absolute team rather than relative to you (minimap
    // force markers, or an observer's whole view). The relationship (self/ally/enemy) and normal
    // color paths read main_palette instead.
    pub force_colors: Option<Operand<'e>>,
}

/// Finds the functions that resolve a player to a draw color, and the color tables they read.
///
/// All of them branch on `minimap_color_mode`, so the candidate set is found by
/// `find_functions_using_global(minimap_color_mode)`. `get_player_color` is the one that indexes
/// `rgb_colors` by its own player argument (when `use_rgb_colors` is set); on builds without
/// `rgb_colors` it is found instead as the candidate that `draw_image` calls. `force_colors` is
/// recognized as the `RGBA[4]` (`<< 4`) table other than `rgb_colors` that the resolver reads
/// through the `get_force_color` helper.
pub(crate) fn player_color_funcs<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    minimap_color_mode: Operand<'e>,
    rgb_colors: Option<Operand<'e>>,
    draw_image: Option<E::VirtualAddress>,
) -> PlayerColorFuncs<'e, E::VirtualAddress> {
    let mut result = PlayerColorFuncs {
        get_player_color: None,
        get_force_color: None,
        get_player_force_color: None,
        force_colors: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let Some(mode_addr) = minimap_color_mode.if_memory()
        .and_then(|x| x.if_constant_address())
        .map(|x| E::VirtualAddress::from_u64(x))
    else {
        return result;
    };
    // rgb_colors only exists from patch 1.23.1a on (custom player colors); when present it gives
    // the cleanest discriminator. `rgb_addr == 0` means "not available", which just disables the
    // rgb-based path (the draw_image fallback below still finds get_player_color).
    let rgb_addr = rgb_colors.and_then(|x| x.if_constant()).unwrap_or(0);
    let arg1 = actx.arg_cache.on_entry(1);
    let global_refs = functions.find_functions_using_global(actx, mode_addr);
    let mut checked = bumpvec_with_capacity(8, &actx.bump);
    for global_ref in &global_refs {
        let entry = global_ref.func_entry;
        if checked.contains(&entry) {
            continue;
        }
        checked.push(entry);
        let mut analyzer = PlayerColorFuncsAnalyzer::<E> {
            rgb_addr,
            arg1,
            data: actx.binary_sections.data,
            rdata: actx.binary_sections.rdata,
            inline_depth: 0,
            cur_callee: E::VirtualAddress::from_u64(0),
            rgb_by_arg: false,
            force_colors: None,
            get_force_color: None,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        analysis.analyze(&mut analyzer);
        // Only commit anything from a function actually confirmed to be a color resolver (i.e. it
        // indexes rgb_colors by its own player argument at the top level), so that the many other
        // minimap_color_mode users (drawing code, etc.) that touch the same tables don't pollute
        // the results.
        if analyzer.rgb_by_arg && result.get_player_color.is_none() {
            result.get_player_color = Some(entry);
        }
        if analyzer.rgb_by_arg {
            if result.force_colors.is_none() {
                result.force_colors = analyzer.force_colors;
            }
            if result.get_force_color.is_none() {
                result.get_force_color = analyzer.get_force_color;
            }
        }
    }

    // When the rgb_colors-based discrimination didn't find get_player_color (pre-1.23.1a builds,
    // before custom player colors existed, have no rgb_colors), fall back to a build-stable
    // anchor: draw_image calls get_player_color to tint unit sprites, so the minimap_color_mode
    // user that draw_image calls is get_player_color. The color tables are then captured by
    // re-running the resolver analyzer on it.
    if result.get_player_color.is_none() {
        if let Some(draw_image) = draw_image {
            let mut collect = CollectCallTargets::<E> {
                calls: bumpvec_with_capacity(0x40, &actx.bump),
                phantom: Default::default(),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, draw_image);
            analysis.analyze(&mut collect);
            for global_ref in &global_refs {
                let entry = global_ref.func_entry;
                if !collect.calls.contains(&entry) {
                    continue;
                }
                let mut analyzer = PlayerColorFuncsAnalyzer::<E> {
                    rgb_addr,
                    arg1,
                    data: actx.binary_sections.data,
                    rdata: actx.binary_sections.rdata,
                    inline_depth: 0,
                    cur_callee: E::VirtualAddress::from_u64(0),
                    rgb_by_arg: false,
                    force_colors: None,
                    get_force_color: None,
                    phantom: Default::default(),
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                result.get_player_color = Some(entry);
                result.force_colors = analyzer.force_colors;
                result.get_force_color = analyzer.get_force_color;
                break;
            }
        }
    }

    // get_player_force_color is the minimap_color_mode user (other than get_player_color) that
    // directly reads force_colors -- it branches on the color mode and, in alliance mode, indexes
    // force_colors by player.force. (The other force_colors users, init_force_colors and
    // get_force_color, don't touch minimap_color_mode.) Iterating the minimap_color_mode users
    // rather than the force_colors users keeps this robust to function-boundary detection picking a
    // mid-function entry for the (later) force_colors access, as happens on some builds.
    if let Some(force_colors) = result.force_colors {
        if let Some(force_addr) = force_colors.if_constant() {
            let mut checked = bumpvec_with_capacity(8, &actx.bump);
            for global_ref in &global_refs {
                let entry = global_ref.func_entry;
                if Some(entry) == result.get_player_color || checked.contains(&entry) {
                    continue;
                }
                checked.push(entry);
                let mut analyzer = ReferencesForceColors::<E> {
                    force_addr,
                    found: false,
                    phantom: Default::default(),
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                if analyzer.found {
                    result.get_player_force_color = Some(entry);
                    break;
                }
            }
        }
    }
    result
}

/// Stops with `found = true` once the analyzed function references `force_addr` directly
/// (`force_colors[idx]`, i.e. an add with `force_addr` as the constant base).
struct ReferencesForceColors<'e, E: ExecutionState<'e>> {
    force_addr: u64,
    found: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for ReferencesForceColors<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Move(ref dest, val) = *op {
            let ctx = ctrl.ctx();
            let val = ctrl.resolve(val);
            let mut check = |op: Operand<'e>| {
                if op.if_arithmetic_add().and_either(|x| x.if_constant()).map(|x| x.0) ==
                    Some(self.force_addr)
                {
                    self.found = true;
                }
            };
            check(val);
            if let Some(mem) = val.if_memory() {
                check(mem.address_op(ctx));
            }
            if let DestOperand::Memory(ref mem) = *dest {
                check(ctrl.resolve_mem(mem).address_op(ctx));
            }
            if self.found {
                ctrl.end_analysis();
            }
        }
    }
}

/// Collects the distinct direct call targets of a function.
struct CollectCallTargets<'acx, 'e, E: ExecutionState<'e>> {
    calls: BumpVec<'acx, E::VirtualAddress>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CollectCallTargets<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if !self.calls.contains(&dest) {
                    self.calls.push(dest);
                }
            }
        }
    }
}

struct PlayerColorFuncsAnalyzer<'e, E: ExecutionState<'e>> {
    rgb_addr: u64,
    arg1: Operand<'e>,
    data: &'e scarf::BinarySection<E::VirtualAddress>,
    rdata: &'e scarf::BinarySection<E::VirtualAddress>,
    inline_depth: u8,
    cur_callee: E::VirtualAddress,
    // Per-candidate findings, committed by the caller only if this turns out to be a resolver.
    rgb_by_arg: bool,
    force_colors: Option<Operand<'e>>,
    get_force_color: Option<E::VirtualAddress>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlayerColorFuncsAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                // Inline one level deep so that the get_force_color(out, force) helper
                // (and through it force_colors) is reached from get_player_color.
                if self.inline_depth == 0 {
                    if seems_assertion_call(ctrl) {
                        return;
                    }
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_depth = 1;
                        let prev = self.cur_callee;
                        self.cur_callee = dest;
                        ctrl.analyze_with_current_state(self, dest);
                        self.cur_callee = prev;
                        self.inline_depth = 0;
                    }
                }
            }
            Operation::Move(ref dest, val) => {
                let ctx = ctrl.ctx();
                let val = ctrl.resolve(val);
                // 32-bit computes the table element address into a register (`add eax, base`),
                // 64-bit folds it into the load operand (`movups xmm, [base + idx*0x10]`), so
                // check both the resolved value and any memory address it touches.
                self.check_table_access(ctx, val);
                if let Some(mem) = val.if_memory() {
                    self.check_table_access(ctx, mem.address_op(ctx));
                }
                if let DestOperand::Memory(ref mem) = *dest {
                    let addr = ctrl.resolve_mem(mem).address_op(ctx);
                    self.check_table_access(ctx, addr);
                }
            }
            _ => (),
        }
    }
}

impl<'e, E: ExecutionState<'e>> PlayerColorFuncsAnalyzer<'e, E> {
    /// True if `base` points into initialized data (and so is a real table, rather than e.g. the
    /// module base that 64-bit rip-relative address arithmetic can leave behind).
    fn in_data(&self, base: u64) -> bool {
        let addr = E::VirtualAddress::from_u64(base);
        self.data.contains(addr) || self.rdata.contains(addr)
    }

    /// Matches `table_base + index * 0x10` operands (the address of `rgb_colors[player]`, or of
    /// `force_colors[force]` inside the get_force_color helper) and records the per-candidate
    /// finding. (The normal-color path indexes `main_palette`.)
    fn check_table_access(&mut self, ctx: scarf::OperandCtx<'e>, val: Operand<'e>) {
        let Some((base, index)) = val.if_arithmetic_add()
            .and_either(|x| x.if_constant())
        else {
            return;
        };
        if base <= 0x1000 {
            return;
        }
        let Some((index, stride)) = index.if_mul_with_const() else {
            return;
        };
        if stride != 0x10 {
            return;
        }
        if base == self.rgb_addr {
            // rgb_colors[player] indexed by the function's own player argument identifies
            // get_player_color (other rgb_colors users index by a unit's player, local_player_id,
            // etc).
            if self.inline_depth == 0 {
                if ctx.and_const(index, 0xff) == ctx.and_const(self.arg1, 0xff) {
                    self.rgb_by_arg = true;
                }
            }
        } else if self.inline_depth != 0 && self.in_data(base) {
            // force_colors lives in the get_force_color helper one call deep.
            if self.force_colors.is_none() {
                self.force_colors = Some(ctx.constant(base));
                self.get_force_color = Some(self.cur_callee);
            }
        }
    }
}

pub(crate) struct RandomizePlayerColors<'e, Va: VirtualAddress> {
    pub randomize_player_colors: Option<Va>,
    // game.player_color_preference[player], an u8[..] of the per-player lobby color choice
    // (0x16 == "random"); randomize_player_colors fills the random ones in on game start.
    pub player_color_preference: Option<Operand<'e>>,
}

/// `randomize_player_colors` resets each unassigned player's color preference to 0x16 (== random)
/// before picking a random one for it via the synced rng, looping over the 8 player slots.
///
/// Anchored on the `use_map_set_rgb_color` reference, then confirmed by two signatures together:
///  - it writes `Mem8[game + loop_index + off] = 0x16`; on scarf's first loop iteration
///    `loop_index` is 0, so `addr - game` is the pure constant `off`, giving
///    `player_color_preference == game + off`.
///  - it calls `rand_synced` (directly or through the rand_synced_range wrapper) to pick colors.
///
/// Both are needed because other lobby code (e.g. construct_game_lobby_screen) also defaults the
/// preference array to 0x16, but does not roll the rng.
pub(crate) fn randomize_player_colors<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    use_map_set_rgb_color: Operand<'e>,
    game: Operand<'e>,
    rand_synced: E::VirtualAddress,
) -> RandomizePlayerColors<'e, E::VirtualAddress> {
    let mut result = RandomizePlayerColors {
        randomize_player_colors: None,
        player_color_preference: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    // use_map_set_rgb_color is stored as a bare global address (the memcpy dst), but be lenient.
    let Some(global_addr) = use_map_set_rgb_color.if_constant()
        .or_else(|| use_map_set_rgb_color.if_memory().and_then(|x| x.if_constant_address()))
        .map(|x| E::VirtualAddress::from_u64(x))
    else {
        return result;
    };
    let global_refs = functions.find_functions_using_global(actx, global_addr);
    let mut checked = bumpvec_with_capacity(8, &actx.bump);
    for global_ref in &global_refs {
        let entry = global_ref.func_entry;
        if checked.contains(&entry) {
            continue;
        }
        checked.push(entry);
        let mut analyzer = RandomizePlayerColorsAnalyzer::<E> {
            game,
            rand_synced,
            inline_depth: 0,
            player_color_preference: None,
            calls_rng: false,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        analysis.analyze(&mut analyzer);
        if analyzer.calls_rng {
            if let Some(pref) = analyzer.player_color_preference {
                result.randomize_player_colors = Some(entry);
                result.player_color_preference = Some(pref);
                break;
            }
        }
    }
    result
}

struct RandomizePlayerColorsAnalyzer<'e, E: ExecutionState<'e>> {
    game: Operand<'e>,
    rand_synced: E::VirtualAddress,
    inline_depth: u8,
    player_color_preference: Option<Operand<'e>>,
    calls_rng: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for RandomizePlayerColorsAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if dest == self.rand_synced {
                        self.calls_rng = true;
                        self.check_done(ctrl);
                    } else if self.inline_depth == 0 && !self.calls_rng {
                        // Inline one level so the rand_synced call inside the rand_synced_range
                        // wrapper is seen.
                        self.inline_depth = 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        self.check_done(ctrl);
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val) => {
                if self.inline_depth == 0 && mem.size == MemAccessSize::Mem8 {
                    if ctrl.resolve(val).if_constant() == Some(0x16) {
                        let ctx = ctrl.ctx();
                        let addr = ctrl.resolve_mem(mem).address_op(ctx);
                        // addr == game + off on the loop's first (index 0) iteration.
                        if let Some(off) = ctx.sub(addr, self.game).if_constant() {
                            if off > 0x1000 && self.player_color_preference.is_none() {
                                self.player_color_preference = Some(addr);
                                self.check_done(ctrl);
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'e, E: ExecutionState<'e>> RandomizePlayerColorsAnalyzer<'e, E> {
    fn check_done(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.calls_rng && self.player_color_preference.is_some() {
            ctrl.end_analysis();
        }
    }
}
