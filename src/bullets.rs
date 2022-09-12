use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use scarf::{MemAccess, Operand, Operation, DestOperand, MemAccessSize};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{AnalysisCtx, ArgCache};
use crate::analysis_state::{AnalysisState, StateEnum, FindCreateBulletState};
use crate::switch;
use crate::struct_layouts;
use crate::util::{bumpvec_with_capacity, ControlExt, OptionExt, OperandExt, is_global};

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
    active_list_candidate_branches: FxHashMap<E::VirtualAddress, Operand<'e>>,
    is_checking_active_list_candidate: Option<Operand<'e>>,
    active_list_candidate_head: Option<Operand<'e>>,
    active_list_candidate_tail: Option<Operand<'e>>,
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
        match *op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve(to).if_constant() {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, E::VirtualAddress::from_u64(dest));
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
                if let Some(head_candidate) = self.is_checking_active_list_candidate {
                    // Adding to active bullets is detected as
                    // if (*first_active == null) {
                    //     *first_active = *first_free;
                    //     *last_active = *first_free;
                    // }
                    if let Some(first_free) = self.first_free {
                        if value == first_free {
                            if dest_value == head_candidate {
                                self.active_list_candidate_head = Some(dest_value);
                            } else {
                                self.active_list_candidate_tail = Some(dest_value);
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                let dest_addr = match ctrl.resolve_va(to) {
                    Some(s) => s,
                    None => return,
                };
                fn if_arithmetic_eq_zero<'e>(op: Operand<'e>) -> Option<Operand<'e>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                }
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(condition) {
                    Some(other) => match if_arithmetic_eq_zero(other) {
                        Some(other) => (other, false),
                        None => (other, true),
                    }
                    None => return,
                };
                if ctrl.if_mem_word(val).is_some() {
                    let addr = match jump_if_null {
                        true => dest_addr,
                        false => ctrl.current_instruction_end(),
                    };
                    self.active_list_candidate_branches.insert(addr, val);
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let head_candidate = self.active_list_candidate_branches.get(&ctrl.address());
        self.is_checking_active_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        if let Some(_) = self.is_checking_active_list_candidate.take() {
            let head = self.active_list_candidate_head.take();
            let tail = self.active_list_candidate_tail.take();
            if let (Some(head), Some(tail)) = (head, tail) {
                self.active_bullets = Some((head, tail));
            }
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
            first_free: None,
            last_free: None,
            is_checking_active_list_candidate: None,
            active_list_candidate_head: None,
            active_list_candidate_tail: None,
            last_ptr_candidates: bumpvec_with_capacity(8, bump),
            active_list_candidate_branches: FxHashMap::default(),
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
                    if let Some(switch) = switch::CompleteSwitch::new(to, ctx, exec) {
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
                            if is_global(mem.address().0) {
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
                                if is_global(mem.address().0) {
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
                        if is_global(mem.address().0) {
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
                            if is_global(dest.address().0) {
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
