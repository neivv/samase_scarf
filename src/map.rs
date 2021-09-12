use scarf::{DestOperand, FlagUpdate, FlagArith, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{
    AnalysisCtx, ArgCache, ControlExt, EntryOf, OperandExt, entry_of_until_with_limit,
    single_result_assign, FunctionFinder,
};
use crate::struct_layouts;

pub struct MapTileFlags<'e, Va: VirtualAddress> {
    pub map_tile_flags: Option<Operand<'e>>,
    pub update_visibility_point: Option<Va>,
}

#[derive(Clone, Copy)]
pub struct RunTriggers<Va: VirtualAddress> {
    pub conditions: Option<Va>,
    pub actions: Option<Va>,
}

impl<Va: VirtualAddress> Default for RunTriggers<Va> {
    fn default() -> Self {
        RunTriggers {
            conditions: None,
            actions: None,
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
            let offset = struct_layouts::unit_nuke_dot_sprite::<F::VirtualAddress>();
            match *op {
                Operation::Call(dest) => {
                    // order_nuke_track calls update_visibility_point([unit + 0xd0])
                    // But it also calls set_sprite_elevation, so the first match
                    // isn't necessarily correct
                    let ctx = ctrl.ctx();
                    let arg_this = ctrl.resolve(ctx.register(1));
                    let ok = ctrl.if_mem_word(arg_this)
                        .and_then(|x| x.if_arithmetic_add_const(offset))
                        .is_some();
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
                Operation::Move(ref dest, _, _) => {
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
                Operation::Move(_, from, None) => {
                    let from = ctrl.resolve(from);
                    // Check for mem_any[map_tile_flags + 4 * (x + y * map_width)]
                    let result = from.if_memory()
                        .and_then(|x| x.address.if_arithmetic_add())
                        .and_then(|(l, r)| Operand::either(l, r, |x| {
                            let x = x.if_arithmetic_mul_const(4)?
                                .unwrap_sext();
                            Operand::and_masked(x).0.if_arithmetic_add()
                        }))
                        .map(|(_, map_tile_flags)| map_tile_flags);
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
) -> RunTriggers<E::VirtualAddress> {
    let mut result = RunTriggers::default();
    // Search for main_game_loop which calls step_objects
    // main_game_loop also calls run_triggers -> run_player_triggers
    // rng is enabled for the run_triggers_call, use that to filter out most
    // of main_game_loop.
    let callers = functions.find_callers(analysis, step_objects);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
    let arg_cache = &analysis.arg_cache;
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
                arg_cache,
                next_func_return_id: 0,
                trigger_player: None,
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
    result: &'a mut RunTriggers<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    next_func_return_id: u32,
    trigger_player: Option<Operand<'e>>,
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
                        .and_then(|x| x.if_arithmetic_add())
                        .and_then(|(l, r)| {
                            let base = E::VirtualAddress::from_u64(r.if_constant()?);
                            let index =
                                l.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())?;
                            Some((base, index))
                        });
                    if let Some((base, index)) = base_index {
                        if let Some(offset) = index.if_mem8()
                            .and_then(|x| x.if_arithmetic_add())
                            .and_then(|x| x.1.if_constant())
                        {
                            // For some reason the trigger pointer is aligned past linked list
                            // prev/next, but check for x + 8 offsets as well to be safe
                            // The trigger structure is same size in 32/64bit outside
                            // those linked list prev/next.
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
                        if let Some(addr) = left.if_memory().map(|x| x.address) {
                            if is_complex_address(addr) {
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
            Operation::Move(DestOperand::Memory(ref mem), val, None) => {
                let dest = ctrl.resolve_mem(mem);
                let is_setting_rng_enable = self.rng_enable.if_memory()
                    .filter(|&x| x == &dest)
                    .is_some();
                if is_setting_rng_enable {
                    if let Some(c) = ctrl.resolve(val).if_constant() {
                        self.rng_enabled = c != 0;
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
                                ctrl.end_analysis();
                            }
                        } else {
                            if let Some(player) = self.trigger_player {
                                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                                if Operand::and_masked(arg1).0 == player {
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
    let arg_cache = &analysis.arg_cache;
    let mut analyzer = CountCacheAnalyzer::<E> {
        result: &mut result,
        arg_cache,
        inline_depth: 0,
        game,
        entry_esp: ctx.register(4),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, cond_command);
    analysis.analyze(&mut analyzer);
    result
}

struct CountCacheAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    inline_depth: u8,
    result: &'a mut TriggerUnitCountCaches<'e>,
    arg_cache: &'a ArgCache<'e, E>,
    game: Operand<'e>,
    entry_esp: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CountCacheAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                if arg3.if_constant() == Some(0xe4 * 12 * 4) {
                    let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                    let ctx = ctrl.ctx();
                    if let Some(offset) = ctx.sub(arg2, self.game).if_constant() {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
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
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
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
                    if ctrl.resolve(ctx.register(4)) == self.entry_esp {
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
