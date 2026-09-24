use bumpalo::collections::Vec as BumpVec;
use scarf::{DestOperand, FlagUpdate, FlagArith, MemAccessSize, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until_with_limit};
use crate::call_tracker::{CallTracker};
use crate::util::{
    ControlExt, ExecStateExt, MemAccessExt, OperandExt, OptionExt, bumpvec_with_capacity,
    is_global, single_result_assign,
};

pub struct MapTileFlags<'e, Va: VirtualAddress> {
    pub map_tile_flags: Option<Operand<'e>>,
    pub update_visibility_point: Option<Va>,
}

#[derive(Clone, Copy)]
pub struct RunTriggers<'e, Va: VirtualAddress> {
    pub conditions: Option<Va>,
    pub actions: Option<Va>,
    pub trigger_execution_timer: Option<Operand<'e>>,
    /// The function main_game_loop calls to step triggers; it contains
    /// trigger_execution_timer countdown and calls run_player_triggers.
    pub step_triggers: Option<Va>,
}

impl<'e, Va: VirtualAddress> Default for RunTriggers<'e, Va> {
    fn default() -> Self {
        RunTriggers {
            conditions: None,
            actions: None,
            trigger_execution_timer: None,
            step_triggers: None,
        }
    }
}

#[derive(Clone, Copy, Default)]
pub struct TriggerUnitCountCaches<'e> {
    pub completed_units: Option<Operand<'e>>,
    pub all_units: Option<Operand<'e>>,
}

pub(crate) fn map_tile_flags<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_nuke_track: E::VirtualAddress,
) -> MapTileFlags<'e, E::VirtualAddress> {
    struct Analyzer<'a, 'b, 'c, F: ExecutionState<'b>> {
        result: &'c mut MapTileFlags<'b, F::VirtualAddress>,
        analysis: &'a AnalysisCtx<'b, F>,
    }
    impl<'a, 'b, 'c, F: ExecutionState<'b>> scarf::Analyzer<'b> for
        Analyzer<'a, 'b, 'c, F>
    {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'b, '_, '_, Self>, op: &Operation<'b>) {
            let offset = F::struct_layouts().unit_nuke_dot_sprite();
            match *op {
                Operation::Call(dest) => {
                    // order_nuke_track calls update_visibility_point([unit + 0xd0])
                    // But it also calls set_sprite_elevation, so the first match
                    // isn't necessarily correct
                    let arg_this = ctrl.resolve_register(1);
                    let ok = ctrl.if_mem_word_offset(arg_this, offset).is_some();
                    if ok {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let result = tile_flags_from_update_visibility_point(
                                self.analysis,
                                dest,
                            );
                            if let Some(result) = result {
                                self.result.map_tile_flags = Some(result);
                                self.result.update_visibility_point = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                Operation::Move(ref dest, _) => {
                    // Ignore moves to [unit + 0xd0]
                    if let DestOperand::Memory(mem) = dest {
                        let (_, dest_off) = ctrl.resolve_mem(mem).address();
                        if dest_off == offset {
                            ctrl.skip_operation();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut result = MapTileFlags {
        map_tile_flags: None,
        update_visibility_point: None,
    };

    let mut analyzer = Analyzer {
        result: &mut result,
        analysis,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, order_nuke_track);
    analysis.analyze(&mut analyzer);
    result
}

fn tile_flags_from_update_visibility_point<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    addr: E::VirtualAddress,
) -> Option<Operand<'e>> {
    struct Analyzer<'e, F: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<(*const F, &'e ())>,
    }
    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation<'f>) {
            match *op {
                Operation::Move(_, from) => {
                    let from = ctrl.resolve(from);
                    let ctx = ctrl.ctx();
                    // Check for mem_any[map_tile_flags + 4 * (x + y * map_width)]
                    let result = from.if_memory()
                        .and_then(|x| {
                            x.if_add_either_other(ctx, |x| {
                                let x = x.if_arithmetic_mul_const(4)?
                                    .unwrap_sext();
                                Operand::and_masked(x).0.if_arithmetic_add()
                            })
                        });
                    if let Some(result) = result {
                        self.result = Some(result.clone());
                        ctrl.end_analysis();
                    }
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: None,
        phantom: Default::default(),
    };

    let mut analysis = FuncAnalysis::new(analysis.binary, analysis.ctx, addr);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub(crate) fn run_triggers<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    rng_enable: Operand<'e>,
    step_objects: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> RunTriggers<'e, E::VirtualAddress> {
    let mut result = RunTriggers::default();
    // Search for main_game_loop which calls step_objects
    // main_game_loop also calls run_triggers -> run_player_triggers
    // rng is enabled for the run_triggers_call, use that to filter out most
    // of main_game_loop.
    let callers = functions.find_callers(analysis, step_objects);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
    for caller in callers {
        entry_of_until_with_limit(binary, &funcs, caller, 128, |entry| {
            let mut analyzer = RunTriggersAnalyzer::<E> {
                inline_depth: 0,
                jump_limit: 0,
                rng_enabled: false,
                caller_ref: caller,
                entry_of: EntryOf::Retry,
                result: &mut result,
                rng_enable,
                next_func_return_id: 0,
                trigger_player: None,
                decremented_timer: None,
                reset_timer: None,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        if result.conditions.is_some() {
            break;
        }
    }

    result
}

struct RunTriggersAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    inline_depth: u8,
    // Prevent unnecessary inlining when rng isn't enabled
    jump_limit: u8,
    rng_enabled: bool,
    rng_enable: Operand<'e>,
    caller_ref: E::VirtualAddress,
    entry_of: EntryOf<()>,
    result: &'a mut RunTriggers<'e, E::VirtualAddress>,
    next_func_return_id: u32,
    trigger_player: Option<Operand<'e>>,
    decremented_timer: Option<Operand<'e>>,
    reset_timer: Option<Operand<'e>>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for RunTriggersAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.caller_ref && ctrl.current_instruction_end() > self.caller_ref {
            self.entry_of = EntryOf::Stop;
        }
        let ctx = ctrl.ctx();
        if self.rng_enabled && self.inline_depth >= 2 {
            // Analyzing run_player_triggers
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    let base_index = ctrl.if_mem_word(dest)
                        .and_then(|mem| {
                            let (index, base) = mem.address();
                            let base = E::VirtualAddress::from_u64(base);
                            let index =
                                index.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())?;
                            Some((base, index))
                        });
                    if let Some((base, index)) = base_index {
                        if let Some(mem) = index.if_mem8() {
                            // For some reason the trigger pointer is aligned past linked list
                            // prev/next, but check for x + 8 offsets as well to be safe
                            // The trigger structure is same size in 32/64bit outside
                            // those linked list prev/next.
                            let offset = mem.address().1;
                            let two_words = u64::from(E::VirtualAddress::SIZE * 2);
                            if offset == 0xf || offset == 0xf + two_words {
                                // Condition is at trigger + 8 + 0xf
                                single_result_assign(Some(base), &mut self.result.conditions);
                            } else if offset == 0x15a || offset == 0x15a + two_words {
                                // Action is at trigger + 8 + 0x148 + 0x1a
                                single_result_assign(Some(base), &mut self.result.actions);
                            }
                            let res = &self.result;
                            if res.conditions.is_some() && res.actions.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                    if self.inline_depth == 2 {
                        if let Some(dest) = dest.if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                        }
                    }
                }
                Operation::Jump { condition, to } => {
                    // Always assume that Comparison of Mem8[x] < 0x18 or 0x3c is true
                    // to not get confused from assertion of action / condition id
                    let condition = ctrl.resolve(condition);
                    let should_assume_unconditional = condition.if_arithmetic_gt()
                        .and_then(|(l, r)| {
                            // Could check the offsets too like at call?
                            if let Some(c) = r.if_constant() {
                                if c == 0x17 || c == 0x3b {
                                    l.if_mem8()?;
                                    return Some(false);
                                }
                            } else if let Some(c) = l.if_constant() {
                                if c == 0x18 || c == 0x3c {
                                    r.if_mem8()?;
                                    return Some(true);
                                }
                            }
                            None
                        });
                    if let Some(always_jump) = should_assume_unconditional {
                        let dest = match always_jump {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.continue_at_address(dest);
                    }
                }
                _ => (),
            }
            return;
        }
        fn is_complex_address<'e>(op: Operand<'e>) -> bool {
            fn recurse<'e>(op: Operand<'e>, limit: u32) -> Option<u32> {
                use scarf::OperandType;
                match *op.ty() {
                    OperandType::Arithmetic(ref a) => {
                        let limit = recurse(a.left, limit)?;
                        recurse(a.right, limit)?
                            .checked_sub(1)
                    }
                    OperandType::Memory(ref mem) => {
                        recurse(mem.address().0, limit)?
                            .checked_sub(1)
                    }
                    _ => limit.checked_sub(1),
                }
            }
            recurse(op, 24).is_none()
        }
        match *op {
            Operation::SetFlags(ref arith) => {
                // Assume that complex mem addresses are volatile
                if !self.rng_enabled && arith.ty == FlagArith::Sub {
                    let left = ctrl.resolve(arith.left);
                    let right = ctrl.resolve(arith.right);
                    if left == right {
                        if let Some(mem) = left.if_memory() {
                            if is_complex_address(mem.address().0) {
                                ctrl.skip_operation();
                                let exec_state = ctrl.exec_state();
                                exec_state.update(&Operation::SetFlags(
                                    FlagUpdate {
                                        left: arith.left,
                                        right: ctx.new_undef(),
                                        ty: FlagArith::Sub,
                                        size: arith.size,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val) => {
                let dest = ctrl.resolve_mem(mem);
                let is_setting_rng_enable = self.rng_enable.if_memory()
                    .is_some_and(|x| x == &dest);
                if is_setting_rng_enable {
                    if let Some(c) = ctrl.resolve(val).if_constant() {
                        self.rng_enabled = c != 0;
                    }
                }
                // run_triggers counts trigger_execution_timer down every frame, and once it
                // reaches zero it runs the triggers and reloads the timer with 0x1e.
                // Nearby sibling timers are stepped with the exact same read-subtract-store
                // shape, so the reload constant is what separates them from this one;
                // require the countdown store and the 0x1e store to be for the same global.
                if self.rng_enabled && self.inline_depth == 1 &&
                    dest.size == MemAccessSize::Mem16 && dest.is_global()
                {
                    let val = ctrl.resolve(val);
                    // The old timer value may have been made undefined by an unrelated call
                    // in between the load and the store.
                    let is_countdown = Operand::and_masked(val).0
                        .if_arithmetic_sub_const(1)
                        .is_some_and(|x| x.if_memory() == Some(&dest) || x.is_undefined());
                    if is_countdown {
                        self.decremented_timer = Some(ctx.memory(&dest));
                    } else if val.if_constant() == Some(0x1e) {
                        self.reset_timer = Some(ctx.memory(&dest));
                    }
                    if self.decremented_timer.is_some() &&
                        self.decremented_timer == self.reset_timer
                    {
                        single_result_assign(
                            self.decremented_timer,
                            &mut self.result.trigger_execution_timer,
                        );
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.jump_limit != 0 {
                    self.jump_limit -= 1;
                    if self.jump_limit == 0 {
                        ctrl.end_analysis();
                    }
                }
                if self.inline_depth != 0 && self.rng_enabled {
                    // check for if (next_trigger_player() < 8)
                    let condition = ctrl.resolve(condition);
                    let is_jae_8 = condition.if_arithmetic_gt()
                        .filter(|x| x.1.if_constant() == Some(7))
                        .map(|x| Operand::and_masked(x.0).0);
                    if let Some(trigger_player) = is_jae_8 {
                        self.trigger_player = Some(trigger_player);
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if !self.rng_enabled {
                        if self.inline_depth == 0 {
                            self.inline_depth += 1;
                            self.jump_limit = 10;
                            ctrl.analyze_with_current_state(self, dest);
                            self.jump_limit = 0;
                            self.inline_depth -= 1;
                        }
                    } else {
                        if self.inline_depth == 0 {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.conditions.is_some() {
                                if self.result.step_triggers.is_none() {
                                    self.result.step_triggers = Some(dest);
                                }
                                ctrl.end_analysis();
                            }
                        } else {
                            if let Some(player) = self.trigger_player {
                                let arg1 = ctrl.resolve_arg(0);
                                if arg1.unwrap_and_mask() == player {
                                    self.inline_depth += 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                    if self.result.conditions.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }

                            let custom = ctx.custom(self.next_func_return_id);
                            self.next_func_return_id = self.next_func_return_id
                                .wrapping_add(1);
                            ctrl.do_call_with_result(custom);
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn trigger_unit_count_caches<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    conditions: E::VirtualAddress,
    game: Operand<'e>,
) -> TriggerUnitCountCaches<'e> {
    let mut result = TriggerUnitCountCaches::default();
    // Find the caches by looking for a memcpy calls from game arrays
    // in condition #2 Command
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let cond_command = match binary.read_address(conditions + 2 * E::VirtualAddress::SIZE) {
        Ok(o) => o,
        Err(_) => return result,
    };
    let mut analyzer = CountCacheAnalyzer::<E> {
        result: &mut result,
        inline_depth: 0,
        game,
        entry_esp: ctx.register(4),
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, cond_command);
    analysis.analyze(&mut analyzer);
    result
}

struct CountCacheAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    inline_depth: u8,
    result: &'a mut TriggerUnitCountCaches<'e>,
    game: Operand<'e>,
    entry_esp: Operand<'e>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CountCacheAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let arg3 = ctrl.resolve_arg(2);
                if arg3.if_constant() == Some(0xe4 * 12 * 4) {
                    let arg2 = ctrl.resolve_arg(1);
                    let ctx = ctrl.ctx();
                    if let Some(offset) = ctx.sub(arg2, self.game).if_constant() {
                        let arg1 = ctrl.resolve_arg(0);
                        if offset == 0x5cf4 {
                            self.result.completed_units = Some(arg1);
                        } else if offset == 0x3234 {
                            self.result.all_units = Some(arg1);
                        }
                        let res = &self.result;
                        if res.all_units.is_some() && res.completed_units.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
                if self.inline_depth < 2 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_depth += 1;
                        let old_esp = self.entry_esp;
                        self.entry_esp = ctrl.get_new_esp_for_call();
                        ctrl.analyze_with_current_state(self, dest);
                        self.entry_esp = old_esp;
                        self.inline_depth -= 1;
                        let res = &self.result;
                        if res.all_units.is_some() && res.completed_units.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let ctx = ctrl.ctx();
                if condition == ctx.const_1() {
                    if ctrl.resolve_register(4) == self.entry_esp {
                        // Tail call
                        ctrl.pop_stack();
                        self.operation(ctrl, &Operation::Call(to));
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) struct InitTerrain<'e, Va: VirtualAddress> {
    pub init_terrain: Option<Va>,
    pub tileset_indexed_map_tiles: Option<Operand<'e>>,
    pub vx4_map_tiles: Option<Operand<'e>>,
    pub terrain_framebuf: Option<Operand<'e>>,
    pub repulse_state: Option<Operand<'e>>,
    pub tileset_data: Option<Operand<'e>>,
    pub tile_default_flags: Option<Operand<'e>>,
    pub tileset_cv5: Option<Operand<'e>>,
    pub tileset_vx4ex: Option<Operand<'e>>,
    pub minitile_graphics: Option<Operand<'e>>,
    pub minitile_data: Option<Operand<'e>>,
    pub foliage_state: Option<Operand<'e>>,
    pub creep_original_tiles: Option<Operand<'e>>,
    pub creep_tile_borders: Option<Operand<'e>>,
}

pub(crate) fn init_terrain<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    init_game: E::VirtualAddress,
    init_images: E::VirtualAddress,
) -> InitTerrain<'e, E::VirtualAddress> {
    let mut result = InitTerrain {
        init_terrain: None,
        tileset_indexed_map_tiles: None,
        vx4_map_tiles: None,
        terrain_framebuf: None,
        repulse_state: None,
        tileset_data: None,
        tile_default_flags: None,
        tileset_cv5: None,
        tileset_vx4ex: None,
        minitile_graphics: None,
        minitile_data: None,
        foliage_state: None,
        creep_original_tiles: None,
        creep_tile_borders: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;
    let mut analyzer = InitTerrainAnalyzer::<E> {
        result: &mut result,
        arg_cache,
        state: InitTerrainState::FindInitTerrain,
        previous_call: E::VirtualAddress::from_u64(0),
        init_images,
        malloc: E::VirtualAddress::from_u64(0),
        inline_depth: 0,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        entry_esp: ctx.register(4),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_game);
    analysis.analyze(&mut analyzer);
    let init_terrain_candidate = analyzer.previous_call;
    if init_terrain_candidate != E::VirtualAddress::from_u64(0) {
        analyzer.state = InitTerrainState::AllocatedBuffers;
        let mut analysis = FuncAnalysis::new(binary, ctx, init_terrain_candidate);
        analysis.analyze(&mut analyzer);
        if result.tileset_indexed_map_tiles.is_some() {
            result.init_terrain = Some(init_terrain_candidate);
        }
    }
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum InitTerrainState {
    /// Walk init_game until init_images call, init_terrain should be the one before.
    FindInitTerrain,
    /// init_terrain should allocate the following buffers:
    /// tileset_indexed_map_tiles(0x20000)
    /// vx4_tile_ids(0x20000)
    /// terrain_framebuf(variable)
    /// map_tile_flags(0x40000) (Not needed)
    /// repulse(0x7239) (May need inlining)
    AllocatedBuffers,
    /// Get tileset_data + 0x520 (0x540 on 64bit) * tileset_id
    /// Inline once, make tileset_date pointer Custom for later checks
    TilesetData,
    /// Reads from tileset_data fields to globals
    /// Has inline to init_creep(tileset_indexed_map_tiles, _, map_width_tiles, map_height_tiles)
    /// in middle.
    TilesetBuffers,
    /// Find 0x180008 byte memset in foliage struct
    Foliage,
}

struct InitTerrainAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    /// Kept as 0 in init_terrain, even though analysis starts with init_game
    inline_depth: u8,
    result: &'a mut InitTerrain<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    previous_call: E::VirtualAddress,
    init_images: E::VirtualAddress,
    /// Set at first allocation, later ones are checked to be same call
    malloc: E::VirtualAddress,
    state: InitTerrainState,
    call_tracker: CallTracker<'acx, 'e, E>,
    entry_esp: Operand<'e>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    InitTerrainAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            InitTerrainState::FindInitTerrain => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.init_images {
                            ctrl.end_analysis();
                        } else {
                            self.previous_call = dest;
                        }
                    }
                }
            }
            InitTerrainState::AllocatedBuffers => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg1_c = arg1.if_constant().unwrap_or(u64::MAX);
                        let ok = if self.malloc != E::VirtualAddress::from_u64(0) {
                            dest == self.malloc
                        } else {
                            arg1_c == 0x20000
                        };
                        if ok {
                            if self.malloc == E::VirtualAddress::from_u64(0) {
                                self.malloc = dest;
                            }
                            let custom_id = if arg1_c == 0x20000 {
                                0
                            } else if arg1_c == u64::MAX {
                                1
                            } else if arg1_c == 0x7239 {
                                2
                            } else {
                                return;
                            };
                            ctrl.do_call_with_result(ctx.custom(custom_id));
                        } else if self.malloc != E::VirtualAddress::from_u64(0) {
                            // Inline a bit once one malloc has been seen
                            if self.inline_depth == 0 {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                            } else {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size != E::WORD_SIZE {
                        return;
                    }
                    let value = ctrl.resolve(value);
                    if let Some(custom) = value.if_custom() {
                        let mem = ctrl.resolve_mem(mem);
                        let dest_op = ctx.memory(&mem);
                        let result = &mut self.result;
                        if custom == 0 {
                            if result.tileset_indexed_map_tiles.is_none() {
                                result.tileset_indexed_map_tiles = Some(dest_op);
                            } else {
                                result.vx4_map_tiles = Some(dest_op);
                            }
                        } else if custom == 1 {
                            result.terrain_framebuf = Some(dest_op);
                        } else if custom == 2 {
                            result.repulse_state = Some(dest_op);
                        }
                        let all_done = result.tileset_indexed_map_tiles.is_some() &&
                            result.vx4_map_tiles.is_some() &&
                            result.terrain_framebuf.is_some() &&
                            result.repulse_state.is_some();
                        if all_done {
                            self.state = InitTerrainState::TilesetData;
                        }
                    }
                }
                if self.inline_depth != 0 {
                    if let Operation::Jump { .. } = *op {
                        ctrl.end_analysis();
                    }
                }
            }
            InitTerrainState::TilesetData => {
                if self.inline_depth == 0 {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_depth = 1;
                            ctrl.inline(self, dest);
                            ctrl.skip_operation();
                            self.inline_depth = 0;
                        }
                    }
                } else {
                    if let Operation::Jump { .. } = *op {
                        ctrl.end_analysis();
                    }
                }
                if let Operation::Move(ref dest, value) = *op {
                    let value = ctrl.resolve(value);
                    let size = E::struct_layouts().tileset_data_size();
                    let result = value.if_arithmetic_add()
                        .and_either_other(|x| x.if_arithmetic_mul_const(size));
                    if let Some(result) = result {
                        self.result.tileset_data = Some(result);
                        ctrl.skip_operation();
                        ctrl.move_unresolved(dest, ctx.custom(8));
                        self.state = InitTerrainState::TilesetBuffers;
                    }
                }
            }
            InitTerrainState::TilesetBuffers => {
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size != E::WORD_SIZE {
                        return;
                    }
                    let mem = ctrl.resolve_mem(mem);
                    if !mem.is_global() {
                        return;
                    }
                    let value = ctrl.resolve(value);
                    if let Some(custom) = value.if_custom() {
                        let dest_op = Some(ctx.memory(&mem));
                        if custom == 4 {
                            single_result_assign(dest_op, &mut self.result.creep_original_tiles);
                        } else if custom == 5 {
                            single_result_assign(dest_op, &mut self.result.creep_tile_borders);
                        }
                    }
                    let offset = ctrl.if_mem_word(value)
                        .filter(|x| x.address().0.if_custom() == Some(8))
                        .map(|x| x.address().1)
                        .filter(|&x| x < 0x580);
                    if let Some(offset) = offset {
                        let dest_op = ctx.memory(&mem);
                        let word_size = E::VirtualAddress::SIZE as u64;
                        let result = &mut self.result;
                        if offset == 0 {
                            result.minitile_graphics = Some(dest_op);
                        } else if offset == 1 * word_size {
                            result.minitile_data = Some(dest_op);
                        } else if offset == 3 * word_size {
                            result.tileset_cv5 = Some(dest_op);
                        } else if offset == 5 * word_size {
                            result.tileset_vx4ex = Some(dest_op);
                        } else if offset == E::struct_layouts().tileset_data_tile_default_flags() {
                            result.tile_default_flags = Some(dest_op);
                        };
                        let all_done = result.minitile_graphics.is_some() &&
                            result.minitile_data.is_some() &&
                            result.tileset_cv5.is_some() &&
                            result.tileset_vx4ex.is_some() &&
                            result.tile_default_flags.is_some();
                        if all_done {
                            self.state = InitTerrainState::Foliage;
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    let arg1 = ctrl.resolve_arg(0);
                    let inline = self.inline_depth == 0 &&
                        arg1.if_custom() == Some(0) &&
                        ctrl.resolve_arg(2).if_mem16_offset(0xe4).is_some();
                    if inline {
                        self.inline_depth += 1;
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            ctrl.analyze_with_current_state(self, dest);
                        }
                        self.inline_depth -= 1;
                    } else {
                        // Check malloc(map_tile_width * map_tile_height [* 2])
                        // * 2 = creep_original_tiles => custom(4)
                        // * 1 = creep_tile_borders => custom(5)
                        let (inner, custom_id) = match arg1.if_arithmetic_mul_const(2) {
                            Some(x) => (x, 4),
                            None => (arg1, 5),
                        };
                        let is_tile_mul = inner.unwrap_sext()
                            .if_arithmetic_mul()
                            .and_either_other(|x| x.if_mem16_offset(0xe4))
                            .and_then(|x| x.if_mem16_offset(0xe6))
                            .is_some();
                        if is_tile_mul {
                            ctrl.do_call_with_result(ctx.custom(custom_id));
                        }
                    }
                }
            }
            InitTerrainState::Foliage => {
                let is_call = matches!(*op, Operation::Call(..));
                let dest = match *op {
                    Operation::Call(dest) => ctrl.resolve_va(dest),
                    Operation::Jump { condition, to } => {
                        if condition == ctx.const_1() &&
                            ctrl.resolve_register(4) == self.entry_esp
                        {
                            ctrl.resolve_va(to)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(dest) = dest {
                    let arg_fn = if is_call {
                        ArgCache::on_call
                    } else {
                        ArgCache::on_entry
                    };
                    let arg1 = ctrl.resolve(arg_fn(&self.arg_cache, 0));
                    let arg3 = ctrl.resolve(arg_fn(&self.arg_cache, 2));
                    if arg3.if_constant() == Some(0x180008) {
                        let arg1 = self.call_tracker.resolve_calls(arg1);
                        if is_global(arg1) {
                            self.result.foliage_state = Some(
                                ctx.sub_const(arg1, E::struct_layouts().foliage_tile_data())
                            );
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    if self.inline_depth == 0 && is_call {
                        if arg1.if_custom().is_some() || is_global(arg1) {
                            self.inline_depth = 1;
                            self.entry_esp = ctrl.get_new_esp_for_call();
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            self.entry_esp = ctx.register(4);
                            if self.result.foliage_state.is_some() {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
                if self.inline_depth != 0 {
                    if let Operation::Jump { .. } = *op {
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy, Default)]
pub(crate) struct StepTriggersState<'e> {
    pub player_trigger_lists: Option<Operand<'e>>,
    pub trigger_elapsed_time_tick_timer: Option<Operand<'e>>,
    pub leaderboard_refresh_timer: Option<Operand<'e>>,
    pub player_trigger_wait_active_flags: Option<Operand<'e>>,
    pub player_trigger_wait_timers: Option<Operand<'e>>,
    pub player_trigger_victory_states: Option<Operand<'e>>,
    pub player_trigger_active_flags: Option<Operand<'e>>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum StepTriggersBranch<'e> {
    /// Branch taken when the Mem16 countdown timer was 0 before being decremented.
    TimerExpired(Operand<'e>),
    /// Branch taken when the Mem8 global is nonzero.
    FlagSet(Operand<'e>),
}

/// Finds the static trigger runtime state that step_triggers(elapsed_ticks) advances
/// every frame. The per-frame timer / wait update is either inlined to step_triggers or
/// a separate function that is called with elapsed_ticks, which gets inlined here.
///
/// - Countdown timers are Mem16 globals stored as `timer - 1`, followed by a jump on the
///   old value being 0.
///   - trigger_elapsed_time_tick_timer: its expiration increments the elapsed game
///     seconds (game + 0xe608).
///   - leaderboard_refresh_timer: the other timer that is reloaded with 0xf in the first
///     block of its expiration branch.
/// - player_trigger_wait_timers[player] is compared against u32::MAX right after
///   checking player_trigger_wait_active_flags[player] to be nonzero.
/// - player_trigger_victory_states is zeroed as a whole (at least 4 bytes) once
///   trigger_execution_timer expires.
/// - player_trigger_active_flags[player] is checked to be nonzero just before checking
///   game player victory state (game + 0xe610 + player).
/// - Victory states and active flags are also found from update_trigger_victory_states,
///   see `trigger_flags_from_update_victory_states`.
/// - player_trigger_lists[player].count is compared against 0 for the current trigger
///   player; the list header is `{ next, prev, count }`, three words.
pub(crate) fn step_triggers_state<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_triggers: E::VirtualAddress,
    trigger_execution_timer: Operand<'e>,
    game: Operand<'e>,
) -> StepTriggersState<'e> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;
    let mut result = StepTriggersState::default();
    let mut analyzer = StepTriggersStateAnalyzer::<E> {
        result: &mut result,
        trigger_execution_timer,
        game,
        elapsed_ticks: ctx.and_const(actx.arg_cache.on_entry(0), 0xffff_ffff),
        inline_depth: 0,
        next_custom: 0,
        branch_starts: bumpvec_with_capacity(0x20, bump),
        current_branch: None,
        last_countdown: None,
        leaderboard_candidates: bumpvec_with_capacity(4, bump),
        calls_after_player_loop: bumpvec_with_capacity(8, bump),
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, step_triggers);
    analysis.analyze(&mut analyzer);
    let leaderboard_candidates = analyzer.leaderboard_candidates;
    let calls_after_player_loop = analyzer.calls_after_player_loop;
    for &timer in leaderboard_candidates.iter() {
        if Some(timer) != result.trigger_elapsed_time_tick_timer {
            single_result_assign(Some(timer), &mut result.leaderboard_refresh_timer);
        }
    }
    // Neither of the above is visible on all builds: some 32-bit builds clear victory
    // states with an SSE store that doesn't get analyzed as a memory write, and old builds
    // don't check player_trigger_active_flags in step_triggers. Both can also be found from
    // update_trigger_victory_states, which step_triggers calls after running player
    // triggers.
    let need_fallback = result.player_trigger_victory_states.is_none() ||
        result.player_trigger_active_flags.is_none();
    if need_fallback || crate::util::test_assertions() {
        for &func in calls_after_player_loop.iter() {
            if let Some((active_flags, victory_states)) =
                trigger_flags_from_update_victory_states::<E>(actx, func)
            {
                single_result_assign(
                    Some(active_flags),
                    &mut result.player_trigger_active_flags,
                );
                single_result_assign(
                    Some(victory_states),
                    &mut result.player_trigger_victory_states,
                );
                break;
            }
        }
    }
    result
}

/// update_trigger_victory_states counts players whose victory state is >= 3 among
/// players with player_trigger_active_flags set:
/// `if player_trigger_active_flags[i] != 0 { if player_trigger_victory_states[i] >= 3 {`
///
/// Returns (player_trigger_active_flags, player_trigger_victory_states).
fn trigger_flags_from_update_victory_states<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> Option<(Operand<'e>, Operand<'e>)> {
    struct Analyzer<'acx, 'e, E: ExecutionState<'e>> {
        /// Branch start addresses for when a Mem8 global is nonzero.
        flag_set_branches: BumpVec<'acx, (E::VirtualAddress, u64)>,
        current_flag: Option<u64>,
        result: Option<(Operand<'e>, Operand<'e>)>,
        ops_left: u32,
    }

    impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'acx, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
            let address = ctrl.address();
            self.current_flag = self.flag_set_branches.iter()
                .find(|x| x.0 == address)
                .map(|x| x.1);
        }

        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if self.ops_left == 0 {
                ctrl.end_analysis();
                return;
            }
            self.ops_left -= 1;
            let ctx = ctrl.ctx();
            match *op {
                Operation::Call(..) => {
                    ctrl.do_call_with_result(ctx.custom(0));
                }
                Operation::Jump { condition, to } => {
                    let condition = ctrl.resolve(condition);
                    let comparison = match condition.if_arithmetic_eq_neq_zero(ctx) {
                        Some((x, _)) if x.if_arithmetic_gt().is_some() => x,
                        _ => condition,
                    };
                    if let Some(active_flags) = self.current_flag {
                        let victory_states = comparison.if_arithmetic_gt_le_const(2)
                            .and_then(|(x, _)| Operand::and_masked(x).0.if_mem8())
                            .and_then(|x| x.if_constant_address())
                            .filter(|&x| x != active_flags);
                        if let Some(victory_states) = victory_states {
                            self.result = Some((
                                ctx.constant(active_flags),
                                ctx.constant(victory_states),
                            ));
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    let flag_check = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|(x, is_eq)| {
                            let addr = Operand::and_masked(x).0
                                .if_mem8()?
                                .if_constant_address()?;
                            Some((addr, is_eq))
                        });
                    if let Some((flag, is_eq)) = flag_check {
                        let neq_address = match is_eq {
                            true => Some(ctrl.current_instruction_end()),
                            false => ctrl.resolve_va(to),
                        };
                        if let Some(addr) = neq_address {
                            self.flag_set_branches.push((addr, flag));
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        flag_set_branches: bumpvec_with_capacity(8, &actx.bump),
        current_flag: None,
        result: None,
        ops_left: 2000,
    };
    let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct StepTriggersStateAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepTriggersState<'e>,
    trigger_execution_timer: Operand<'e>,
    game: Operand<'e>,
    elapsed_ticks: Operand<'e>,
    inline_depth: u8,
    next_custom: u32,
    branch_starts: BumpVec<'acx, (E::VirtualAddress, StepTriggersBranch<'e>)>,
    current_branch: Option<StepTriggersBranch<'e>>,
    /// Timer that was decremented in the current branch.
    last_countdown: Option<Operand<'e>>,
    leaderboard_candidates: BumpVec<'acx, Operand<'e>>,
    /// Functions called from step_triggers after player_trigger_lists was seen.
    calls_after_player_loop: BumpVec<'acx, E::VirtualAddress>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    StepTriggersStateAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let address = ctrl.address();
        self.current_branch = self.branch_starts.iter().rev()
            .find(|x| x.0 == address)
            .map(|x| x.1);
        self.last_countdown = None;
    }

    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth == 0 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if ctrl.resolve_arg_u32(0) == self.elapsed_ticks {
                            self.inline_depth = 1;
                            let old_branch = self.current_branch;
                            ctrl.analyze_with_current_state(self, dest);
                            self.current_branch = old_branch;
                            self.last_countdown = None;
                            self.inline_depth = 0;
                            return;
                        }
                    }
                }
                if self.inline_depth == 0 && self.result.player_trigger_lists.is_some() {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if !self.calls_after_player_loop.contains(&dest) {
                            self.calls_after_player_loop.push(dest);
                        }
                    }
                }
                let custom = ctx.custom(self.next_custom);
                self.next_custom = self.next_custom.wrapping_add(1);
                ctrl.do_call_with_result(custom);
            }
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                let dest = ctrl.resolve_mem(mem);
                let value = ctrl.resolve(value);
                let dest_op = ctx.memory(&dest);
                if dest.size == MemAccessSize::Mem32 &&
                    ctx.sub(dest.address_op(ctx), self.game).if_constant() == Some(0xe608)
                {
                    let is_increment = Operand::and_masked(value).0
                        .if_arithmetic_add_const(1)
                        .is_some();
                    if is_increment {
                        if let Some(StepTriggersBranch::TimerExpired(timer)) =
                            self.current_branch
                        {
                            single_result_assign(
                                Some(timer),
                                &mut self.result.trigger_elapsed_time_tick_timer,
                            );
                        }
                    }
                    return;
                }
                if !dest.is_global() {
                    return;
                }
                if dest.size == MemAccessSize::Mem16 {
                    // The old timer value may have been made undefined by merging
                    // with a branch that wrote to a neighbouring global.
                    let is_countdown = Operand::and_masked(value).0
                        .if_arithmetic_sub_const(1)
                        .is_some_and(|x| x == dest_op || x.contains_undefined());
                    if is_countdown {
                        self.last_countdown = Some(dest_op);
                    } else if value.if_constant() == Some(0xf) {
                        let expired = StepTriggersBranch::TimerExpired(dest_op);
                        if self.current_branch == Some(expired) &&
                            !self.leaderboard_candidates.contains(&dest_op)
                        {
                            self.leaderboard_candidates.push(dest_op);
                        }
                    }
                } else if value.if_constant() == Some(0) {
                    let expired = StepTriggersBranch::TimerExpired(self.trigger_execution_timer);
                    if self.current_branch == Some(expired) &&
                        self.result.player_trigger_victory_states.is_none()
                    {
                        if let Some(addr) = dest.if_constant_address() {
                            self.result.player_trigger_victory_states =
                                Some(ctx.constant(addr));
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if let Some(StepTriggersBranch::FlagSet(flags)) = self.current_branch {
                    // player_trigger_wait_timers[player] == u32::MAX
                    let timers = condition.if_arithmetic_eq_neq()
                        .map(|(l, r, _)| (l, r))
                        .and_if_either_other(|x| x.if_constant() == Some(0xffff_ffff))
                        .and_then(|x| x.if_mem32())
                        .and_then(|x| x.if_constant_address());
                    let flags = flags.if_memory().and_then(|x| x.if_constant_address());
                    if let (Some(timers), Some(flags)) = (timers, flags) {
                        single_result_assign(
                            Some(ctx.constant(flags)),
                            &mut self.result.player_trigger_wait_active_flags,
                        );
                        single_result_assign(
                            Some(ctx.constant(timers)),
                            &mut self.result.player_trigger_wait_timers,
                        );
                    }
                }
                let Some((x, is_eq)) = condition.if_arithmetic_eq_neq_zero(ctx) else {
                    return;
                };
                let x = Operand::and_masked(x).0;
                let (eq_address, neq_address) = match is_eq {
                    true => (ctrl.resolve_va(to), Some(ctrl.current_instruction_end())),
                    false => (Some(ctrl.current_instruction_end()), ctrl.resolve_va(to)),
                };
                if let Some(timer) = self.last_countdown.take() {
                    let checks_timer = x == timer || x.contains_undefined();
                    if let (true, Some(addr)) = (checks_timer, eq_address) {
                        self.branch_starts.push((addr, StepTriggersBranch::TimerExpired(timer)));
                    }
                }
                if let Some(mem) = x.if_mem8() {
                    if let Some(StepTriggersBranch::FlagSet(flags)) = self.current_branch {
                        let is_game_victory_state =
                            ctx.sub(mem.address_op(ctx), self.game).if_constant() ==
                                Some(0xe610);
                        if is_game_victory_state {
                            single_result_assign(
                                flags.if_memory()
                                    .and_then(|x| x.if_constant_address())
                                    .map(|x| ctx.constant(x)),
                                &mut self.result.player_trigger_active_flags,
                            );
                        }
                    }
                    if let (Some(_), Some(addr)) = (mem.if_constant_address(), neq_address) {
                        self.branch_starts.push((addr, StepTriggersBranch::FlagSet(x)));
                    }
                }
                if self.inline_depth == 0 {
                    // player_trigger_lists[player].count == 0
                    let word_size = E::VirtualAddress::SIZE as u64;
                    let lists = ctrl.if_mem_word(x)
                        .and_then(|mem| {
                            let (index, offset) = mem.address();
                            let index = index.if_arithmetic_mul_const(word_size * 3)?;
                            if index.if_constant().is_some() {
                                return None;
                            }
                            offset.checked_sub(word_size * 2)
                        });
                    if let Some(lists) = lists {
                        single_result_assign(
                            Some(ctx.constant(lists)),
                            &mut self.result.player_trigger_lists,
                        );
                    }
                }
            }
            _ => (),
        }
    }
}
