use bumpalo::collections::Vec as BumpVec;

use scarf::{MemAccess, Operand, Operation, DestOperand, MemAccessSize};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_state::{AnalysisState, StateEnum, FindCreateBulletState};
use crate::call_tracker::CallTracker;
use crate::linked_list::DetectListAdd;
use crate::switch::{self, CompleteSwitch};
use crate::struct_layouts;
use crate::util::{
    bumpvec_with_capacity, ControlExt, MemAccessExt, OptionExt, OperandExt, is_global,
    seems_assertion_call,
};

pub(crate) struct BulletCreation<'e, Va: VirtualAddress> {
    pub first_active_bullet: Option<Operand<'e>>,
    pub last_active_bullet: Option<Operand<'e>>,
    pub first_free_bullet: Option<Operand<'e>>,
    pub last_free_bullet: Option<Operand<'e>>,
    pub create_bullet: Option<Va>,
    pub active_iscript_unit: Option<Operand<'e>>,
}

pub(crate) struct StepBulletFrame<Va: VirtualAddress> {
    pub step_moving_bullet_frame: Option<Va>,
}

pub(crate) struct StepMovingBulletFrame<'e, Va: VirtualAddress> {
    pub flingy_flags_tmp: Option<Operand<'e>>,
    pub flingy_x_old: Option<Operand<'e>>,
    pub flingy_y_old: Option<Operand<'e>>,
    pub flingy_x_new: Option<Operand<'e>>,
    pub flingy_y_new: Option<Operand<'e>>,
    pub flingy_exact_x_new: Option<Operand<'e>>,
    pub flingy_exact_y_new: Option<Operand<'e>>,
    pub flingy_flags_new: Option<Operand<'e>>,
    pub flingy_show_end_walk_anim: Option<Operand<'e>>,
    pub flingy_show_start_walk_anim: Option<Operand<'e>>,
    pub flingy_speed_used_for_move: Option<Operand<'e>>,
    pub map_width_pixels: Option<Operand<'e>>,
    pub map_height_pixels: Option<Operand<'e>>,
    pub flingy_update_target_dir: Option<Va>,
    pub step_flingy_speed: Option<Va>,
    pub step_flingy_movement_start_end: Option<Va>,
    pub step_flingy_position: Option<Va>,
    pub move_sprite: Option<Va>,
    pub step_flingy_turning: Option<Va>,
}

pub(crate) struct DoMissileDamage<Va: VirtualAddress> {
    pub hit_unit: Option<Va>,
    pub unit_was_hit: Option<Va>,
    pub disable_unit: Option<Va>,
    pub ai_unit_was_hit: Option<Va>,
    pub lookup_sound_id: Option<Va>,
    pub play_sound_at_unit: Option<Va>,
    pub kill_unit: Option<Va>,
    pub unit_max_energy: Option<Va>,
    pub splash_lurker: Option<Va>,
    pub splash_full: Option<Va>,
    pub for_each_unit_in_area: Option<Va>,
}

pub(crate) struct HitUnit<Va: VirtualAddress> {
    pub hallucination_hit: Option<Va>,
    pub do_weapon_damage: Option<Va>,
}

pub(crate) struct DoWeaponDamage<Va: VirtualAddress> {
    pub damage_unit: Option<Va>,
    pub show_shield_overlay_for_direction: Option<Va>,
    pub show_shield_overlay: Option<Va>,
    pub unit_update_strength: Option<Va>,
    pub unit_calculate_strength: Option<Va>,
}

struct FindCreateBullet<'a, 'acx, 'e, E: ExecutionState<'e>> {
    is_inlining: bool,
    result: Option<E::VirtualAddress>,
    active_iscript_unit: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    calls_seen: u32,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    FindCreateBullet<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if arg1.if_mem8().is_some() {
                            self.is_inlining = true;
                            let ecx = ctrl.resolve(ctx.register(1));
                            self.active_iscript_unit = Some(ecx);
                            ctrl.user_state().get::<FindCreateBulletState>().calls_seen = 0;
                            self.calls_seen = 0;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.is_some() && self.calls_seen == 2 {
                                ctrl.end_analysis();
                            } else {
                                self.calls_seen = 0;
                                self.is_inlining = false;
                                self.result = None;
                                self.active_iscript_unit = None;
                            }
                        }
                    }
                }

                let unit = ctrl.resolve(self.arg_cache.on_call(5));
                if let Some(active_unit) = self.active_iscript_unit {
                    if unit != active_unit {
                        return;
                    }
                }
                let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                let is_player = arg4
                    .if_mem8_offset(struct_layouts::unit_player::<E::VirtualAddress>())
                    .map(|x| x == unit)
                    .unwrap_or(false);
                if !is_player {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(to) {
                    if let Some(s) = self.result {
                        if s != dest {
                            return;
                        }
                    }
                    self.result = Some(dest);
                    self.active_iscript_unit = Some(unit);
                    let state = ctrl.user_state().get::<FindCreateBulletState>();
                    let new_calls_seen = state.calls_seen + 1;
                    if new_calls_seen > self.calls_seen {
                        self.calls_seen = new_calls_seen;
                    }
                    state.calls_seen = new_calls_seen;
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if condition == ctx.const_1() {
                    if to.if_constant().is_none() {
                        // Reached switch jump?
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

struct FindBulletLists<'acx, 'e, E: ExecutionState<'e>> {
    is_inlining: bool,
    // first active, first_free
    active_bullets: Option<(Operand<'e>, Operand<'e>)>,
    list_add_tracker: DetectListAdd<'e, E>,
    first_free: Option<Operand<'e>>,
    last_free: Option<Operand<'e>>,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindBulletLists<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        self.list_add_tracker.operation(ctrl, op);
        match *op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.is_inlining = false;
                        if self.active_bullets.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                if mem.size != E::WORD_SIZE {
                    return;
                }
                let ctx = ctrl.ctx();
                let dest = ctrl.resolve_mem(mem);
                let dest_value = ctx.memory(&dest);
                let value = ctrl.resolve(value);
                // first_free_bullet = (*first_free_bullet).next, e.g.
                // mov [first_free_bullet], [[first_free_bullet] + 4]
                let first_free_next = ctrl.mem_word(
                    dest_value,
                    E::VirtualAddress::SIZE as u64,
                );
                if value == first_free_next {
                    self.first_free = Some(dest_value);
                    self.list_add_tracker.reset(dest_value);
                    if let Some(last) = self.last_ptr_first_known(dest_value) {
                        self.last_free = Some(last);
                    }
                    return;
                }
                // last_free_bullet = (*first_free_bullet).prev
                // But not (*(*first_free_bullet).next).prev = (*first_free_bullet).prev
                if let Some(inner) = ctrl.if_mem_word_offset(value, 0)
                    .and_then(|x| ctrl.if_mem_word(x))
                {
                    let inner_op = inner.address_op(ctx);
                    let (dest_base, dest_offset) = dest.address();
                    if inner.if_constant_address() != Some(dest_offset) &&
                        dest_base.iter().all(|x| x != inner_op)
                    {
                        if self.is_unpaired_first_ptr(inner) {
                            self.last_free = Some(dest_value);
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner_op, dest_value));
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.list_add_tracker.branch_start(ctrl);
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let ctx = ctrl.ctx();
        if let Some(result) = self.list_add_tracker.result(ctx) {
            self.active_bullets = Some((result.head, result.tail));
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> FindBulletLists<'acx, 'e, E> {
    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1)
    }

    fn is_unpaired_first_ptr(&self, first: &MemAccess<'e>) -> bool {
        if let Some(_) = self.first_free
            .and_then(|x| x.if_memory())
            .filter(|x| x.address() == first.address())
        {
            return self.last_free.is_none();
        }
        false
    }
}

pub(crate) fn bullet_creation<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    iscript_switch: E::VirtualAddress,
) -> BulletCreation<'e, E::VirtualAddress> {
    let mut result = BulletCreation {
        first_active_bullet: None,
        last_active_bullet: None,
        first_free_bullet: None,
        last_free_bullet: None,
        create_bullet: None,
        active_iscript_unit: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let useweapon = match switch::simple_switch_branch(binary, iscript_switch, 0x28) {
        Some(o) => o,
        None => return result,
    };
    let mut analyzer = FindCreateBullet {
        is_inlining: false,
        result: None,
        active_iscript_unit: None,
        calls_seen: 0,
        arg_cache: &analysis.arg_cache,
        phantom: Default::default(),
    };
    let exec_state = E::initial_state(ctx, binary);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        useweapon,
        exec_state,
        AnalysisState::new(
            bump,
            StateEnum::CreateBullet(FindCreateBulletState {
                calls_seen: 0,
            }),
        ),
    );
    analysis.analyze(&mut analyzer);
    result.create_bullet = analyzer.result;
    result.active_iscript_unit = analyzer.active_iscript_unit;
    if let Some(create_bullet) = analyzer.result {
        let mut analyzer = FindBulletLists::<E> {
            is_inlining: false,
            active_bullets: None,
            list_add_tracker: DetectListAdd::new(None),
            first_free: None,
            last_free: None,
            last_ptr_candidates: bumpvec_with_capacity(8, bump),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, create_bullet);
        analysis.analyze(&mut analyzer);
        if let Some((first, last)) = analyzer.active_bullets {
            result.first_active_bullet = Some(first);
            result.last_active_bullet = Some(last);
        }
        result.first_free_bullet = analyzer.first_free;
        result.last_free_bullet = analyzer.last_free;
    }
    result
}

pub(crate) fn analyze_step_bullet_frame<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_bullets: Option<E::VirtualAddress>,
    step_bullet_frame: Option<E::VirtualAddress>,
    first_active_bullet: Operand<'e>,
) -> StepBulletFrame<E::VirtualAddress> {
    let mut result = StepBulletFrame {
        step_moving_bullet_frame: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    // If step_bullet_frame doesn't exist, it's inlined and hopefully step_bullets does.
    // Technically both of them could be inlined which would be bit ugh, and this analysis
    // would have to be moved to be yet another part of the massive step_objects analysis.
    let (func, this) = if let Some(step) = step_bullet_frame {
        (step, ctx.register(1))
    } else {
        let step_bullets = match step_bullets {
            Some(s) => s,
            None => return result,
        };
        (step_bullets, first_active_bullet)
    };
    let mut analyzer = StepBulletFrameAnalyzer::<E> {
        result: &mut result,
        switch_jumped: false,
        this,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    result
}

struct StepBulletFrameAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepBulletFrame<E::VirtualAddress>,
    switch_jumped: bool,
    this: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for StepBulletFrameAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if !self.switch_jumped {
            if let Operation::Jump { condition, to } = *op {
                if condition == ctx.const_1() {
                    let to = ctrl.resolve(to);
                    let exec = ctrl.exec_state();
                    if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                        let binary = ctrl.binary();
                        if let Some(branch) = switch.branch(binary, ctx, 1) {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_address(branch);
                            self.switch_jumped = true;
                        }
                    }
                }
            } else if let Operation::Call(..) = *op {
                ctrl.skip_call_preserve_esp();
            }
        } else {
            let dest = match *op {
                Operation::Call(dest) => Some(dest),
                Operation::Jump { condition, to } => {
                    let esp = ctx.register(4);
                    if condition == ctx.const_1() && ctrl.resolve(esp) == esp {
                        // Tail call
                        Some(to)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(dest) = dest.and_then(|x| ctrl.resolve_va(x)) {
                let this = ctrl.resolve(ctx.register(1));
                if this == self.this {
                    self.result.step_moving_bullet_frame = Some(dest);
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) fn analyze_step_moving_bullet_frame<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_moving_bullet_frame: E::VirtualAddress,
) -> StepMovingBulletFrame<'e, E::VirtualAddress> {
    let mut result = StepMovingBulletFrame {
        flingy_flags_tmp: None,
        flingy_x_old: None,
        flingy_y_old: None,
        flingy_x_new: None,
        flingy_y_new: None,
        flingy_exact_x_new: None,
        flingy_exact_y_new: None,
        flingy_flags_new: None,
        flingy_show_end_walk_anim: None,
        flingy_show_start_walk_anim: None,
        flingy_speed_used_for_move: None,
        map_width_pixels: None,
        map_height_pixels: None,
        flingy_update_target_dir: None,
        step_flingy_speed: None,
        step_flingy_movement_start_end: None,
        step_flingy_position: None,
        move_sprite: None,
        step_flingy_turning: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = StepMovingAnalyzer::<E> {
        state: StepMovingState::FlingyFlagsTmp,
        inline_depth: 0,
        inlining_move_flingy: false,
        verifying_func: false,
        result: &mut result,
        arg_cache: &actx.arg_cache,
        current_func: E::VirtualAddress::from_u64(0),
        start_end_other_state: None,
        start_end_candidate: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, step_moving_bullet_frame);
    analysis.analyze(&mut analyzer);
    result
}

struct StepMovingAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    state: StepMovingState,
    inline_depth: u8,
    inlining_move_flingy: bool,
    verifying_func: bool,
    result: &'a mut StepMovingBulletFrame<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    current_func: E::VirtualAddress,
    start_end_other_state: Option<(E, E::VirtualAddress)>,
    start_end_candidate: Option<Operand<'e>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepMovingState {
    /// Find write of flingy.flags to global
    /// Allow inlining twice at start of the function
    FlingyFlagsTmp,
    /// Check for flingy_update_target_dir, step_flingy_speed, step_flingy_movement_start_end,
    /// step_flingy_position calls each in order.
    /// flingy_update_target_dir may be inlined though.
    /// verify with:
    /// flingy_update_target_dir: starts with comparision of next_move_waypoint.x, pos.x
    ///     May be inlined and missing
    /// step_flingy_speed: starts with jump of flingy_movement_type
    /// step_flingy_movement_start_end: starts with jump of flags & 2
    ///     flags & 2 == 0 path may write to startwalk anim,
    ///     endwalk anim is another global written
    /// step_flingy_position: writes flingy_speed to flingy_speed_used_for_move
    FlingyFuncs,
    AnalyzeStartEndStartWalk,
    AnalyzeStartEndEndWalk,
    /// old_flingy_x,y = flingy_pos.x,y
    /// flingy_pos.x,y = new_flingy_x,y (Skip operation for move_sprite below)
    /// flingy_exact_pos.x,y = new_flingy_exact_x,y
    /// new_flingy_flags = flingy_flags (this way because bullet)
    /// Ends on move_sprite(flingy.x, flingy.y)
    /// May have to inline to this.move_flingy(), in that case no variables other than
    /// new_flingy_flags have been found.
    FlingyVarWrites,
    /// Another func which starts with flags & 2 comparision (inside move_flingy like
    /// in previous state)
    StepFlingyTurning,
    /// May inline out from FlingyFlagsTmp inline.
    /// Check flingy.position.x >= map_width_pixels and
    /// flingy.position.y >= map_height_pixels
    MapWidthHeight,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for StepMovingAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let flingy_flags_offset = struct_layouts::flingy_flags::<E::VirtualAddress>();
        let movement_type_offset = struct_layouts::flingy_movement_type::<E::VirtualAddress>();
        let next_move_wp_offset = struct_layouts::flingy_next_move_waypoint::<E::VirtualAddress>();
        let pos_offset = struct_layouts::flingy_pos::<E::VirtualAddress>();
        let exact_pos_offset = struct_layouts::flingy_exact_pos::<E::VirtualAddress>();
        let speed_offset = struct_layouts::flingy_speed::<E::VirtualAddress>();
        let ctx = ctrl.ctx();
        let ecx = ctx.register(1);
        match self.state {
            StepMovingState::FlingyFlagsTmp => {
                match *op {
                    Operation::Jump { .. } => {
                        ctrl.end_analysis();
                    }
                    Operation::Call(dest) => {
                        if self.inline_depth < 2 {
                            if let Some(dest) = ctrl.resolve_va(dest) {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != StepMovingState::FlingyFlagsTmp {
                                    self.state = StepMovingState::MapWidthHeight;
                                }
                            }
                        }
                    }
                    Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                        let value = ctrl.resolve(value);
                        if value.if_mem8_offset(flingy_flags_offset) == Some(ecx) {
                            let mem = ctrl.resolve_mem(mem);
                            if mem.is_global() {
                                self.result.flingy_flags_tmp = Some(ctx.memory(&mem));
                                self.state = StepMovingState::FlingyFuncs;
                            }
                        }


                    }
                    _ => (),
                }
            }
            StepMovingState::FlingyFuncs => {
                if !self.verifying_func {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            if ctrl.resolve(ecx) == ecx {
                                self.verifying_func = true;
                                self.current_func = dest;
                                ctrl.analyze_with_current_state(self, dest);
                                self.verifying_func = false;
                                if self.result.step_flingy_position.is_some() {
                                    self.state = StepMovingState::FlingyVarWrites;
                                } else {
                                    self.state = StepMovingState::FlingyFuncs;
                                }
                            }
                        }
                    }
                } else {
                    if let Operation::Jump { condition, to } = *op {
                        let condition = ctrl.resolve(condition);
                        let pos_cmp = self.result.flingy_update_target_dir.is_none() &&
                            condition.if_arithmetic_eq_neq()
                                .map(|x| (x.0, x.1))
                                .and_if_either_other(|x| {
                                    x.if_mem16_offset(next_move_wp_offset) == Some(ecx)
                                })
                                .filter(|x| x.if_mem16_offset(pos_offset) == Some(ecx))
                                .is_some();
                        if pos_cmp {
                            self.result.flingy_update_target_dir = Some(self.current_func);
                            ctrl.end_analysis();
                            return;
                        }

                        let speed_cmp = self.result.step_flingy_speed.is_none() &&
                            condition.if_arithmetic_eq_neq()
                                .filter(|x| x.1.if_constant().is_some())
                                .and_then(|x| x.0.if_mem8_offset(movement_type_offset)) ==
                                    Some(ecx);
                        if speed_cmp {
                            self.result.step_flingy_speed = Some(self.current_func);
                            ctrl.end_analysis();
                            return;
                        }

                        if self.result.step_flingy_movement_start_end.is_none() {
                            let start_end_cmp = condition.if_arithmetic_eq_neq_zero(ctx)
                                .and_then(|x| {
                                    x.0.if_arithmetic_and_const(2)?
                                        .if_mem8_offset(flingy_flags_offset)
                                        .filter(|&x| x == ecx)?;
                                    Some(x.1)
                                });
                            if let Some(follow) = start_end_cmp {
                                let to = match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                };
                                let no_jump = ctrl.current_instruction_end();
                                let (next_addr, other_addr) = match follow {
                                    true => (to, no_jump),
                                    false => (no_jump, to),
                                };
                                self.result.step_flingy_movement_start_end =
                                    Some(self.current_func);
                                self.state = StepMovingState::AnalyzeStartEndStartWalk;
                                self.start_end_other_state =
                                    Some((ctrl.exec_state().clone(), other_addr));
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(next_addr);
                                return;
                            }
                        }
                        ctrl.end_analysis();
                    } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                        if self.result.step_flingy_position.is_none() {
                            let value = ctrl.resolve(value);
                            if value.if_mem32_offset(speed_offset) == Some(ecx) {
                                self.result.step_flingy_position = Some(self.current_func);
                                let mem = ctrl.resolve_mem(&mem);
                                if mem.is_global() {
                                    self.result.flingy_speed_used_for_move =
                                        Some(ctx.memory(&mem));
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            StepMovingState::AnalyzeStartEndStartWalk |
                StepMovingState::AnalyzeStartEndEndWalk =>
            {
                if let Operation::Move(DestOperand::Memory(ref mem), _, None) = *op {
                    if mem.size == MemAccessSize::Mem8 {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            let val = ctx.memory(&mem);
                            if self.result.flingy_show_start_walk_anim != Some(val) {
                                self.start_end_candidate = Some(ctx.memory(&mem));
                            }
                        }
                    }
                } else if let Operation::Jump { .. } = *op {
                    self.start_end_candidate = None;
                } else if let Operation::Return(..) = *op {
                    if let Some(result) = self.start_end_candidate {
                        if self.state == StepMovingState::AnalyzeStartEndStartWalk {
                            self.result.flingy_show_start_walk_anim = Some(result);
                            self.state = StepMovingState::AnalyzeStartEndEndWalk;
                            if let Some(next) = self.start_end_other_state.take() {
                                ctrl.clear_unchecked_branches();
                                ctrl.add_branch_with_state(next.1, next.0, Default::default());
                            }
                        } else {
                            self.result.flingy_show_end_walk_anim = Some(result);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            StepMovingState::FlingyVarWrites => {
                if let Operation::Move(DestOperand::Memory(ref dest), value, None) = *op {
                    let dest = ctrl.resolve_mem(dest);
                    let value = ctrl.resolve(value);
                    if dest.address().0 == ecx && is_global(value) {
                        let offset = dest.address().1;
                        if offset == pos_offset {
                            self.result.flingy_x_new = Some(value);
                        } else if offset == pos_offset + 2 {
                            self.result.flingy_y_new = Some(value);
                        } else if offset == exact_pos_offset {
                            self.result.flingy_exact_x_new = Some(value);
                        } else if offset == exact_pos_offset + 4 {
                            self.result.flingy_exact_y_new = Some(value);
                        }
                        // Skip operation so that self.pos.x can be checked for move_sprite arg
                        ctrl.skip_operation();
                    } else if let Some(mem) = value.if_memory() {
                        if mem.address().0 == ecx {
                            let offset = mem.address().1;
                            if dest.is_global() {
                                let dest_op = ctx.memory(&dest);
                                if offset == flingy_flags_offset {
                                    self.result.flingy_flags_new = Some(dest_op);
                                } else if offset == pos_offset {
                                    self.result.flingy_x_old = Some(dest_op);
                                } else if offset == pos_offset + 2 {
                                    self.result.flingy_y_old = Some(dest_op);
                                }
                            }
                        }
                    }
                } if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ecx);
                        if this == ecx && !self.inlining_move_flingy {
                            if self.result.flingy_flags_new.is_some() &&
                                self.result.flingy_x_old.is_none() &&
                                self.result.flingy_x_new.is_none()
                            {
                                self.inlining_move_flingy = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inlining_move_flingy = false;
                                self.state = StepMovingState::MapWidthHeight;
                                return;
                            }
                        }
                        let ok = struct_layouts::if_unit_sprite::<E::VirtualAddress>(this) ==
                            Some(ecx);
                        if ok {
                            let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                            let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                            let ok = arg1.if_mem16_offset(pos_offset) == Some(ecx) &&
                                arg2.if_mem16_offset(pos_offset + 2) == Some(ecx);
                            if ok {
                                self.result.move_sprite = Some(dest);
                                self.state = StepMovingState::StepFlingyTurning;
                            }
                        }
                    }
                }
            }
            StepMovingState::StepFlingyTurning => {
                if !self.verifying_func {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            if ctrl.resolve(ecx) == ecx {
                                self.verifying_func = true;
                                self.current_func = dest;
                                ctrl.analyze_with_current_state(self, dest);
                                self.verifying_func = false;
                                if self.result.step_flingy_turning.is_some() {
                                    if self.inline_depth >= 2 || self.inlining_move_flingy {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else {
                    if let Operation::Jump { condition, .. } = *op {
                        let condition = ctrl.resolve(condition);
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| {
                                x.0.if_arithmetic_and_const(2)?
                                    .if_mem8_offset(flingy_flags_offset)
                            }) == Some(ecx);
                        if ok {
                            self.result.step_flingy_turning = Some(self.current_func);
                            self.state = StepMovingState::MapWidthHeight;
                            ctrl.end_analysis();
                            return;
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            StepMovingState::MapWidthHeight => {
                if self.result.map_height_pixels.is_some() &&
                    self.result.map_width_pixels.is_some()
                {
                    ctrl.end_analysis();
                    return;
                }
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    // signed greater or equal jump, so annoying to match
                    let result = condition.if_arithmetic_eq_neq()
                        .map(|x| (x.0, x.1))
                        .and_either(|x| {
                            // l should be width/height global,
                            // r is x + 8000_0000
                            let (l, r) = x.if_arithmetic_gt()?;
                            if !is_global(l) {
                                return None;
                            }
                            let mem = Operand::and_masked(r).0
                                .if_arithmetic_add_const(0x8000_0000)?
                                .unwrap_sext()
                                .if_mem16()?;
                            let (base, offset) = mem.address();
                            if base == ecx {
                                Some((offset, l))
                            } else {
                                None
                            }
                        })
                        .map(|x| x.0);
                    if let Some((offset, val)) = result {
                        if offset == pos_offset {
                            self.result.map_width_pixels = Some(val);
                        } else if offset == pos_offset + 2 {
                            self.result.map_height_pixels = Some(val);
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn do_missile_damage<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    iscript_switch: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = actx.ctx;
    let binary = actx.binary;
    // Search for iscript opcode 0x1b, calling into
    // do_missile_dmg(this = active_iscript_bullet)
    let switch_branch = switch::simple_switch_branch(binary, iscript_switch, 0x1b)?;
    let mut analyzer = DoMissileDmgAnalyzer::<E> {
        result: None,
        arg_cache: &actx.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, switch_branch);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct DoMissileDmgAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for DoMissileDmgAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if seems_assertion_call(ctrl, self.arg_cache) {
                ctrl.end_branch();
                return;
            }
            if let Some(dest) = ctrl.resolve_va(dest) {
                let ctx = ctrl.ctx();
                let this = ctrl.resolve(ctx.register(1));
                if ctrl.if_mem_word(this).is_some() {
                    self.result = Some(dest);
                    ctrl.end_analysis();
                }
            }
        } else if let Operation::Jump { condition, to } = *op {
            let ctx = ctrl.ctx();
            if condition == ctx.const_1() && to.if_constant().is_none() {
                // Looped back to switch
                ctrl.end_branch();
            }
        }
    }
}

pub(crate) fn analyze_do_missile_damage<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    do_missile_damage: E::VirtualAddress,
) -> DoMissileDamage<E::VirtualAddress> {
    let mut result = DoMissileDamage {
        hit_unit: None,
        unit_was_hit: None,
        disable_unit: None,
        ai_unit_was_hit: None,
        lookup_sound_id: None,
        play_sound_at_unit: None,
        kill_unit: None,
        unit_max_energy: None,
        splash_lurker: None,
        splash_full: None,
        for_each_unit_in_area: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = MissileDamageAnalyzer::<E> {
        state: MissileDamageState::FindSwitch,
        inline_depth: 0,
        result: &mut result,
        arg_cache: &actx.arg_cache,
        switch: None,
        unit_was_hit_state: None,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        increment_kill_scores_seen: false,
        entry_esp: ctx.register(4),
        other_splash_branch: None,
        for_each_unit_in_area_candidate: E::VirtualAddress::from_u64(0),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, do_missile_damage);
    analysis.analyze(&mut analyzer);
    // Note: This switch is a bit fragile, requiring BinaryFile to not contain
    // zero-inited mutable bytes.
    // As the switch is on weapons_dat_behaviour[x], CompleteSwitch::branch confuses
    // it with u8-packed cases if weapons_dat_behaviour array is readable by
    // BinaryFile.
    if let Some((switch, exec)) = analyzer.switch.take() {
        let branches = [
            (1, MissileDamageState::Type1Branch),
            (2, MissileDamageState::SplashBranch),
            (4, MissileDamageState::DisableUnit),
            (7, MissileDamageState::AiUnitWasHit),
            (9, MissileDamageState::Sounds),
            (0xe, MissileDamageState::KillUnit),
        ];
        for (branch, state) in branches {
            if let Some(addr) = switch.branch(binary, ctx, branch) {
                let mut analysis = FuncAnalysis::with_state(binary, ctx, addr, exec.clone());
                analyzer.state = state;
                analysis.analyze(&mut analyzer);
            }
        }
    }
    if result.for_each_unit_in_area.is_none() {
        result.splash_lurker = None;
        result.splash_full = None;
    }
    result
}

struct MissileDamageAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    state: MissileDamageState,
    inline_depth: u8,
    result: &'a mut DoMissileDamage<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    switch: Option<(CompleteSwitch<'e>, E)>,
    unit_was_hit_state: Option<(E::VirtualAddress, E)>,
    call_tracker: CallTracker<'acx, 'e, E>,
    increment_kill_scores_seen: bool,
    entry_esp: Operand<'e>,
    other_splash_branch: Option<(E, E::VirtualAddress)>,
    for_each_unit_in_area_candidate: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum MissileDamageState {
    /// Find switch jumping on weapons_dat_effect[this.weapon_id]
    FindSwitch,
    /// On switch branch 1, find jump on this.flags & 1 (is bullet missing)
    Type1Branch,
    /// flag_1 == 0 branch, find hit_unit(this = this.target, this, dmg_div)
    HitUnit,
    /// flag_1 != 0 branch, find unit_was_hit(this = this.target, this.parent, 1)
    UnitWasHit,
    /// On switch branch 4 (lockdown), find
    /// do_lockdown(this = this, 0x83) (maybe inlined) {
    ///     this.target_lockdown_timer = 0x83;
    ///     disable_unit(this = this.target)
    /// }
    DisableUnit,
    /// On switch branch 7 (broodlings), find
    /// ai_unit_was_hit(a1 = this.target, this.parent, 1, 0)
    ///     a4 is not checked since it may be implicitly set from previous != 0 jump
    AiUnitWasHit,
    /// On switch branch 9 (irradiate), find
    /// play_sound_at_unit(sound_id, this.target, 1, 0)
    /// where sound_id is return value of lookup_sound_id (or constant in older versions)
    Sounds,
    /// On switch branch 0xe (consume), find
    /// do_consume(this = this.parent, this.target) {
    ///     increment_kill_scores(a1 = this.target, this.parent.player_id)
    ///     kill_unit(this = this.target)
    ///     if (this.parent.energy + 0x3200 > unit_max_energy) {
    ///         ..
    ///     }
    /// }
    KillUnit,
    UnitMaxEnergy,
    /// Find comparison of x == 6d (Lurker weapon); either a jump or conditional move,
    /// then run the following code twice and search for for_each_unit_in_area(_, func, _)
    /// with different funcs.
    SplashBranch,
    SplashPostComparison,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    MissileDamageAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let target_offset = struct_layouts::unit_target::<E::VirtualAddress>();
        let parent_offset = struct_layouts::bullet_parent::<E::VirtualAddress>();
        let ecx = ctx.register(1);
        match self.state {
            MissileDamageState::FindSwitch => {
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        if to.if_constant().is_none() {
                            let exec = ctrl.exec_state();
                            if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                                self.switch = Some((switch, exec.clone()));
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            MissileDamageState::Type1Branch => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_const(0).map(|x| (x, true))
                        .or_else(|| Some((condition, false)))
                        .and_then(|x| {
                            x.0.if_arithmetic_and_const(0x1)?
                                .if_mem8_offset(
                                    struct_layouts::bullet_flags::<E::VirtualAddress>()
                                )?;
                            Some(x.1)
                        });
                    if let Some(jump_on_zero) = result {
                        let jump_addr = match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        };
                        let no_jump_addr = ctrl.current_instruction_end();
                        let (continue_addr, other_addr) = match jump_on_zero {
                            true => (jump_addr, no_jump_addr),
                            false => (no_jump_addr, jump_addr),
                        };
                        self.state = MissileDamageState::HitUnit;
                        let exec = ctrl.exec_state();
                        self.unit_was_hit_state = Some((other_addr, exec.clone()));
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_address(continue_addr);

                    }
                }
            }
            MissileDamageState::HitUnit | MissileDamageState::UnitWasHit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ecx);
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        let ok = if self.state == MissileDamageState::HitUnit {
                            ctrl.if_mem_word_offset(this, target_offset) == Some(ecx) &&
                                arg1 == ecx
                        } else {
                            let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                            ctrl.if_mem_word_offset(this, target_offset) == Some(ecx) &&
                                ctrl.if_mem_word_offset(arg1, parent_offset) == Some(ecx) &&
                                arg2 == ctx.const_1()
                        };

                        if ok {
                            if self.state == MissileDamageState::HitUnit {
                                self.result.hit_unit = Some(dest);
                                if let Some((addr, state)) = self.unit_was_hit_state.take() {
                                    ctrl.clear_unchecked_branches();
                                    ctrl.add_branch_with_state(addr, state, Default::default());
                                    self.state = MissileDamageState::UnitWasHit;
                                }
                            } else {
                                self.result.unit_was_hit = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            MissileDamageState::DisableUnit => {
                let call_dest = if let Operation::Call(dest) = *op {
                    Some(dest)
                } else if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() &&
                        ctrl.resolve(ctx.register(4)) == self.entry_esp
                    {
                        // Tail call
                        Some(to)
                    } else {
                        None
                    }
                } else {
                    None
                };

                if let Some(dest) = call_dest {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ecx);
                        let this_target =
                            ctrl.if_mem_word_offset(this, target_offset) == Some(ecx);
                        if this_target {
                            let timer_offset =
                                struct_layouts::unit_lockdown_timer::<E::VirtualAddress>();
                            let lockdown_timer = ctx.mem8(ecx, timer_offset);
                            if ctrl.resolve(lockdown_timer).if_constant() == Some(0x83) {
                                self.result.disable_unit = Some(dest);
                                ctrl.end_analysis();
                            } else if self.inline_depth == 0 {
                                let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                                if arg1.if_constant() == Some(0x83) {
                                    let old_esp = self.entry_esp;
                                    self.inline_depth = 1;
                                    self.entry_esp = ctrl.get_new_esp_for_call();
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth = 0;
                                    self.entry_esp = old_esp;
                                    if self.result.disable_unit.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), _, _) = *op {
                    // Just move 0x83 always to lockdown timer value to not having
                    // to handle min/max checks
                    let mem = ctrl.resolve_mem(mem);
                    if mem.address().1 ==
                        struct_layouts::unit_lockdown_timer::<E::VirtualAddress>()
                    {
                        ctrl.move_resolved(&DestOperand::Memory(mem), ctx.constant(0x83));
                        ctrl.skip_operation();
                    }
                }
            }
            MissileDamageState::AiUnitWasHit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                        let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                        let ok = ctrl.if_mem_word_offset(arg1, target_offset) == Some(ecx) &&
                            ctrl.if_mem_word_offset(arg2, parent_offset) == Some(ecx) &&
                            arg3 == ctx.const_1() &&
                            arg4 == ctx.const_0();

                        if ok {
                            self.result.ai_unit_was_hit = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    ctrl.update_jump_register_to_const(condition, to);
                }
            }
            MissileDamageState::Sounds => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let arg1 = Operand::and_masked(arg1).0;
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                        let ok = (arg1.if_custom().is_some() || arg1.if_constant().is_some()) &&
                            ctrl.if_mem_word_offset(arg2, target_offset) == Some(ecx) &&
                            arg3 == ctx.const_1();
                        if ok {
                            self.result.play_sound_at_unit = Some(dest);
                            if let Some(custom) = arg1.if_custom() {
                                if let Some(func) = self.call_tracker.custom_id_to_func(custom) {
                                    self.result.lookup_sound_id = Some(func);
                                }
                            }
                            ctrl.end_analysis();
                            return;
                        }
                        self.call_tracker.add_call_preserve_esp(ctrl, dest);
                    }
                }
            }
            MissileDamageState::KillUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ecx);
                        if self.inline_depth == 0 {
                            let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                            let inline =
                                ctrl.if_mem_word_offset(this, parent_offset) == Some(ecx) &&
                                ctrl.if_mem_word_offset(arg1, target_offset) == Some(ecx);
                            if inline {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                if self.result.kill_unit.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                        if !self.increment_kill_scores_seen {
                            // Check a2 != this.parent.player_id to avoid
                            // confusing with increment_kill_scores
                            let c_a2 = ctrl.resolve(self.arg_cache.on_call(1));
                            let is_parent_player =
                                c_a2.if_mem8_offset(
                                    struct_layouts::unit_player::<E::VirtualAddress>()
                                ).is_some();
                            self.increment_kill_scores_seen = is_parent_player;
                            ctrl.clear_unchecked_branches();
                        } else {
                            let this_target =
                                ctrl.if_mem_word_offset(this, target_offset) == Some(ecx);
                            if this_target {
                                self.result.kill_unit = Some(dest);
                                self.state = MissileDamageState::UnitMaxEnergy;
                            }
                        }
                    }
                }
            }
            MissileDamageState::UnitMaxEnergy => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_gt()
                        .and_then(|(l, r)| {
                            r.if_arithmetic_add_const(0x31ff)?;
                            Some(Operand::and_masked(l).0)
                        });
                    if let Some(result) = result {
                        if let Some(custom) = result.if_custom() {
                            if let Some(func) = self.call_tracker.custom_id_to_func(custom) {
                                self.result.unit_max_energy = Some(func);
                            }
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            MissileDamageState::SplashBranch => {
                match *op {
                    Operation::Jump { condition, to } => {
                        let condition = ctrl.resolve(condition);
                        if let Some(eq) = is_lurker_weapon_cmp(condition) {
                            if let Some(to) = ctrl.resolve_va(to) {
                                ctrl.clear_unchecked_branches();
                                let next = ctrl.current_instruction_end();
                                let (eq_addr, neq_addr) = match eq {
                                    true => (to, next),
                                    false => (next, to),
                                };
                                let lurker_state = ctrl.exec_state().clone();
                                self.other_splash_branch = Some((lurker_state, eq_addr));
                                self.state = MissileDamageState::SplashPostComparison;
                                ctrl.continue_at_address(neq_addr);
                            }
                        }
                    }
                    Operation::Move(ref dest, value, Some(condition)) => {
                        let condition = ctrl.resolve(condition);
                        if let Some(eq) = is_lurker_weapon_cmp(condition) {
                            ctrl.clear_unchecked_branches();
                            let next = ctrl.current_instruction_end();
                            ctrl.skip_operation();
                            let mut lurker_state = ctrl.exec_state().clone();
                            if eq {
                                lurker_state.move_to(dest, value);
                            } else {
                                ctrl.move_unresolved(dest, value);
                            }
                            self.other_splash_branch = Some((lurker_state, next));
                            self.state = MissileDamageState::SplashPostComparison;
                        }
                    }
                    _ => (),
                }
            }
            MissileDamageState::SplashPostComparison => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if let Some(arg2) = ctrl.resolve_va(self.arg_cache.on_call(1)) {
                            if let Some((lurker_state, addr)) = self.other_splash_branch.take() {
                                self.for_each_unit_in_area_candidate = dest;
                                self.result.splash_full = Some(arg2);
                                ctrl.clear_unchecked_branches();
                                ctrl.end_branch();
                                ctrl.add_branch_with_state(addr, lurker_state, Default::default());
                            } else {
                                if self.for_each_unit_in_area_candidate == dest {
                                    self.result.splash_lurker = Some(arg2);
                                    self.result.for_each_unit_in_area = Some(dest);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

fn is_lurker_weapon_cmp<'e>(condition: Operand<'e>) -> Option<bool> {
    condition.if_arithmetic_eq_neq()
        .filter(|x| x.1.if_constant() == Some(0x6d))
        .map(|x| x.2)
}

pub(crate) fn analyze_hit_unit<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    hit_unit: E::VirtualAddress,
) -> HitUnit<E::VirtualAddress> {
    let mut result = HitUnit {
        hallucination_hit: None,
        do_weapon_damage: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = HitUnitAnalyzer::<E> {
        state: HitUnitState::FindHalluJump,
        result: &mut result,
        arg_cache: &actx.arg_cache,
        not_hallu_state: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, hit_unit);
    analysis.analyze(&mut analyzer);
    result
}

struct HitUnitAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    state: HitUnitState,
    result: &'a mut HitUnit<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    not_hallu_state: Option<(E::VirtualAddress, E)>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum HitUnitState {
    /// find jump on arg1.flags & 2 (is hallu)
    FindHalluJump,
    /// flag_2 != 0 branch, find
    /// hallucination_hit(this = this, arg1.weapon_id, arg1.facing_direction, arg1.parent)
    HallucinationHit,
    /// flag_2 == 0 branch, find
    /// do_weapon_damage(this = this, dmg, arg1.weapon_id, arg2, arg1.facing_direction,
    ///     arg1.parent, arg1.player)
    DoWeaponDamage,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for HitUnitAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            HitUnitState::FindHalluJump => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|x| {
                            x.0.if_arithmetic_and_const(0x2)?
                                .if_mem8_offset(
                                    struct_layouts::bullet_flags::<E::VirtualAddress>()
                                )?;
                            Some(x.1)
                        });
                    if let Some(jump_on_zero) = result {
                        let jump_addr = match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        };
                        let no_jump_addr = ctrl.current_instruction_end();
                        let (continue_addr, other_addr) = match jump_on_zero {
                            true => (no_jump_addr, jump_addr),
                            false => (jump_addr, no_jump_addr),
                        };
                        self.state = HitUnitState::HallucinationHit;
                        let exec = ctrl.exec_state();
                        self.not_hallu_state = Some((other_addr, exec.clone()));
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_address(continue_addr);
                    }
                }
            }
            HitUnitState::HallucinationHit | HitUnitState::DoWeaponDamage => {
                let facing_offset = struct_layouts::flingy_facing_direction::<E::VirtualAddress>();
                let parent_offset = struct_layouts::bullet_parent::<E::VirtualAddress>();
                let weapon_id_offset = struct_layouts::bullet_weapon_id::<E::VirtualAddress>();
                let call_dest = if let Operation::Call(dest) = *op {
                    Some(dest)
                } else if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() &&
                        ctrl.resolve(ctx.register(4)) == ctx.register(4)
                    {
                        // Tail call
                        Some(to)
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(dest) = call_dest {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ecx = ctx.register(1);
                        let this = ctrl.resolve(ecx);
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if this != ecx {
                            if E::VirtualAddress::SIZE == 4 &&
                                self.state == HitUnitState::DoWeaponDamage
                            {
                                if arg1 == ecx {
                                    // Probably get_weapon_damage(), on 32bit it is stdcall,
                                    // and may be mixed with do_weapon_damage args, so fix esp
                                    // manually
                                    ctrl.skip_call_preserve_esp();
                                    ctrl.move_unresolved(
                                        &DestOperand::Register64(4),
                                        ctx.add_const(ctx.register(4), 4),
                                    );
                                }
                            }
                            return;
                        }
                        let bullet = self.arg_cache.on_thiscall_entry(0);
                        let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                        let arg3 = ctrl.resolve(self.arg_cache.on_thiscall_call(2));
                        let arg4 = ctrl.resolve(self.arg_cache.on_thiscall_call(3));
                        let arg5 = ctrl.resolve(self.arg_cache.on_thiscall_call(4));
                        let ok = if self.state == HitUnitState::HallucinationHit {
                            ctx.and_const(arg1, 0xff)
                                    .if_mem8_offset(weapon_id_offset) == Some(bullet) &&
                                ctx.and_const(arg2, 0xff)
                                    .if_mem8_offset(facing_offset) == Some(bullet) &&
                                ctrl.if_mem_word_offset(arg3, parent_offset) == Some(bullet)
                        } else {
                            ctx.and_const(arg2, 0xff)
                                    .if_mem8_offset(weapon_id_offset) == Some(bullet) &&
                                ctx.and_const(arg3, 0xff) ==
                                    ctx.and_const(self.arg_cache.on_thiscall_entry(1), 0xff) &&
                                ctx.and_const(arg4, 0xff)
                                    .if_mem8_offset(facing_offset) == Some(bullet) &&
                                ctrl.if_mem_word_offset(arg5, parent_offset) == Some(bullet)
                        };

                        if ok {
                            if self.state == HitUnitState::HallucinationHit {
                                self.result.hallucination_hit = Some(dest);
                                if let Some((addr, state)) = self.not_hallu_state.take() {
                                    ctrl.clear_unchecked_branches();
                                    ctrl.add_branch_with_state(addr, state, Default::default());
                                    self.state = HitUnitState::DoWeaponDamage;
                                }
                            } else {
                                self.result.do_weapon_damage = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_do_weapon_damage<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    do_weapon_damage: E::VirtualAddress,
) -> DoWeaponDamage<E::VirtualAddress> {
    let mut result = DoWeaponDamage {
        damage_unit: None,
        show_shield_overlay_for_direction: None,
        show_shield_overlay: None,
        unit_update_strength: None,
        unit_calculate_strength: None,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = WeaponDamageAnalyzer::<E> {
        state: WeaponDamageState::DamageUnit,
        result: &mut result,
        inline_depth: 0,
        inline_limit: 0,
        arg_cache: &actx.arg_cache,
        func_entry: do_weapon_damage,
        entry_esp: ctx.register(4),
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, do_weapon_damage);
    analysis.analyze(&mut analyzer);
    result
}

struct WeaponDamageAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    state: WeaponDamageState,
    inline_depth: u8,
    inline_limit: u8,
    result: &'a mut DoWeaponDamage<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    func_entry: E::VirtualAddress,
    entry_esp: Operand<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum WeaponDamageState {
    /// find damage_unit(this = this, _, a5, a6, a2 == 0x22)
    DamageUnit,
    /// find show_shield_overlay_for_direction(this = this, a4)
    /// or assume it was inlined and find
    /// show_shield_overlay(this = this.sprite, (a4 - 0x7c / 8) & 0x1f)
    ShowShieldOverlay,
    /// find unit_update_strength(this = this) which may be inlined,
    /// and unit.ground_strength = unit_calculate_strength(this = this, 1)
    UnitUpdateStrength,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    WeaponDamageAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            WeaponDamageState::DamageUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ctx = ctrl.ctx();
                        let ok = ctrl.resolve(ctx.register(1)) == ctx.register(1) && {
                                let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                                let entry_arg5 = self.arg_cache.on_thiscall_entry(4);
                                ctx.and_const(arg2, 0xff) == ctx.and_const(entry_arg5, 0xff)
                            } && {
                                let arg3 = ctrl.resolve(self.arg_cache.on_thiscall_call(2));
                                let entry_arg6 = self.arg_cache.on_thiscall_entry(5);
                                ctx.and_const(arg3, 0xff) == ctx.and_const(entry_arg6, 0xff)
                            } && {
                                let arg4 = ctrl.resolve(self.arg_cache.on_thiscall_call(3));
                                ctx.and_const(arg4, 0xff)
                                    .if_arithmetic_eq_neq()
                                    .filter(|x| x.1.if_constant() == Some(0x22))
                                    .is_some()
                            };
                        if ok {
                            self.result.damage_unit = Some(dest);
                            self.state = WeaponDamageState::ShowShieldOverlay;
                        }
                    }
                }
            }
            WeaponDamageState::ShowShieldOverlay => {
                let ctx = ctrl.ctx();
                let dest = match *op {
                    Operation::Call(dest) => Some(dest),
                    Operation::Jump { condition, to } if self.inline_depth != 0 => {
                        let is_tail_call = condition == ctx.const_1() &&
                            ctrl.resolve(ctx.register(4)) == self.entry_esp;
                        if is_tail_call {
                            Some(to)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(dest) = dest.and_then(|x| ctrl.resolve_va(x)) {
                    let ecx = ctx.register(1);
                    let this = ctrl.resolve(ecx);
                    let arg1 = if matches!(op, Operation::Call(..)) {
                        self.arg_cache.on_thiscall_call(0)
                    } else {
                        self.arg_cache.on_thiscall_entry(0)
                    };
                    let arg1 = ctrl.resolve(arg1);
                    if this == ecx {
                        let ok = ctx.and_const(arg1, 0xff) ==
                            ctx.and_const(self.arg_cache.on_thiscall_entry(3), 0xff);
                        if ok {
                            let old_esp = self.entry_esp;
                            self.result.show_shield_overlay_for_direction = Some(dest);
                            self.inline_depth = self.inline_depth.wrapping_add(1);
                            self.entry_esp = ctrl.get_new_esp_for_call();
                            ctrl.analyze_with_current_state(self, dest);
                            self.entry_esp = old_esp;
                            self.inline_depth = self.inline_depth.wrapping_sub(1);
                        }
                    } else {
                        let sprite_offset = struct_layouts::unit_sprite::<E::VirtualAddress>();
                        let ok = ctrl.if_mem_word_offset(this, sprite_offset) == Some(ecx) &&
                            arg1.if_arithmetic_and_const(0x1f).is_some();
                        if ok {
                            self.result.show_shield_overlay = Some(dest);
                            self.state = WeaponDamageState::UnitUpdateStrength;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            WeaponDamageState::UnitUpdateStrength => {
                if self.inline_limit != 0 {
                    if matches!(op, Operation::Call(..) | Operation::Jump { .. }) {
                        self.inline_limit -= 1;
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        }
                    }
                }
                let ctx = ctrl.ctx();
                let ecx = ctx.register(1);
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.inline_depth == 0 {
                            if ctrl.resolve(ecx) == ecx {
                                let old_entry = self.func_entry;
                                self.inline_limit = 10;
                                self.inline_depth = 1;
                                self.func_entry = dest;
                                ctrl.analyze_with_current_state(self, dest);
                                if self.result.unit_update_strength.is_some() {
                                    ctrl.end_analysis();
                                    return;
                                }
                                self.func_entry = old_entry;
                                self.inline_limit = 0;
                                self.inline_depth = 0;
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    let mem = ctrl.resolve_mem(mem);
                    let strength_offset =
                        struct_layouts::unit_ground_strength::<E::VirtualAddress>();
                    if mem.address() == (ecx, strength_offset) {
                        if self.inline_depth != 0 {
                            self.result.unit_update_strength = Some(self.func_entry);
                        }
                        let value = ctrl.resolve(value);
                        if let Some(custom) = Operand::and_masked(value).0.if_custom() {
                            if let Some(func) = self.call_tracker.custom_id_to_func(custom) {
                                self.result.unit_calculate_strength = Some(func);
                            }
                        }
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}
