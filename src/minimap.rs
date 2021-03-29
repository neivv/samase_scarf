use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operand, Operation};

use crate::{
    AnalysisCtx, ArgCache, ControlExt, EntryOf, entry_of_until, if_arithmetic_eq_neq, OperandExt,
    OptionExt, Patch, bumpvec_with_capacity, FunctionFinder,
};

pub(crate) fn unexplored_fog_minimap_patch<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    first_fow_sprite: Operand<'e>,
    is_replay: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> (Option<Patch<E::VirtualAddress>>, Option<E::VirtualAddress>) {
    // The relevant code is something like
    //
    // for fow in fow_sprites() {
    //     if fow.id().is_installation_doodad() {
    //         continue;
    //     }
    //     if is_replay() || (!local_player_observer() && !fow.sprite().id().is_resource() {
    //         if in_fog(fow) {
    //             continue;
    //         }
    //     }
    //     -- more code to draw minimap dots --
    // }
    //
    // Going to find that replay check and just remove it, making resources appear in replay
    // minimaps. Would be nice to have other neutral buildings also appear there but this
    // will do for now.

    let first_fow_addr = first_fow_sprite
        .if_memory()
        .and_then(|x| x.address.if_constant())
        .map(|x| E::VirtualAddress::from_u64(x));
    let first_fow_addr = match first_fow_addr {
        Some(s) => s,
        None => return (None, None),
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    let mut first_fow_uses = bumpvec_with_capacity(0x10, bump);
    first_fow_uses.extend(
        functions.find_functions_using_global(analysis, first_fow_addr)
            .into_iter()
            .map(|x| x.use_address)
    );
    let mut result = None;
    let mut draw_minimap_units = None;
    let mut i = 0;
    while i < first_fow_uses.len() {
        let use_address = first_fow_uses[i];
        let entry = entry_of_until(binary, funcs, use_address, |entry| {
            let mut analyzer = ReplayFowAnalyzer::<E> {
                result: &mut result,
                entry_of: EntryOf::Retry,
                is_get_fn: false,
                use_address,
                first_fow_sprite,
                is_replay,
                inlining: false,
                fow_unit_id_checked: false,
            };
            let mut func_analysis = FuncAnalysis::new(binary, ctx, entry);
            func_analysis.analyze(&mut analyzer);
            if analyzer.is_get_fn {
                first_fow_uses.extend(functions.find_callers(analysis, entry));
            }
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);
        if result.is_some() {
            draw_minimap_units = entry;
            break;
        }
        i += 1;
    }
    (result, draw_minimap_units)
}

struct ReplayFowAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut Option<Patch<E::VirtualAddress>>,
    /// If the function was just get_first_active_fow_sprite(), analyze anything
    /// calling it.
    is_get_fn: bool,
    inlining: bool,
    fow_unit_id_checked: bool,
    entry_of: EntryOf<()>,
    use_address: E::VirtualAddress,
    first_fow_sprite: Operand<'e>,
    is_replay: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for ReplayFowAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if !self.inlining {
            if ctrl.address() <= self.use_address &&
                ctrl.current_instruction_end() > self.use_address
            {
                self.entry_of = EntryOf::Stop;
            }
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        self.inlining = true;
                        ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                        ctrl.skip_operation();
                        self.inlining = false;
                    }
                }
                Operation::Return(..) => {
                    let eax = ctrl.resolve(ctx.register(0));
                    self.is_get_fn = eax == self.first_fow_sprite;
                }
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if self.fow_unit_id_checked {
                        let result = if_arithmetic_eq_neq(condition)
                            .and_then(|x| {
                                Some((x.0, x.1))
                                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                                    .filter(|&x| x == self.is_replay)?;
                                Some(x.2)
                            });
                        if let Some(jump_if_replay_eq_zero) = result {
                            let address = ctrl.address();
                            let instruction_len = ctrl.current_instruction_end().as_u64()
                                .wrapping_sub(address.as_u64()) as usize;
                            let data = if jump_if_replay_eq_zero {
                                // Make jump unconditional
                                let binary = ctrl.binary();
                                binary.slice_from_address(address, 0x18).ok()
                                    .and_then(|x| match *x {
                                        // Short jumps
                                        [x, ..] if x >= 0x70 && x < 0x80 => {
                                            Some(vec![0xeb])
                                        }
                                        // Long jumps
                                        [0x0f, x, ..] if x >= 0x80 && x < 0x80 => {
                                            Some(vec![0x90, 0xe9])
                                        }
                                        _ => None,
                                    })
                            } else {
                                // Nop jump out
                                Some(vec![0x90; instruction_len])
                            };
                            if let Some(data) = data {
                                *self.result = Some(Patch {
                                    address,
                                    data,
                                });
                            } else {
                                warn!("Can't patch {:?}", address);
                            }
                            self.entry_of = EntryOf::Ok(());
                            ctrl.end_analysis();
                        }
                    } else {
                        let fow_unit_id_offset = (E::VirtualAddress::SIZE * 2) as u64;
                        let checks_fow_unit_id = condition.if_arithmetic_gt()
                            .and_either_other(|x| x.if_constant())
                            .and_then(|x| x.if_arithmetic_sub_const(0xcb))
                            .and_then(|x| x.if_mem16())
                            .and_then(|x| x.if_arithmetic_add_const(fow_unit_id_offset))
                            .filter(|&x| x == self.first_fow_sprite)
                            .is_some();
                        if checks_fow_unit_id {
                            self.fow_unit_id_checked = true;
                        }
                    }
                }
                _ => (),
            }
        } else {
            // Inlining, stop if it is not a trivial function.
            // This is just for if is_replay() needs to be inlined.
            match *op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }
}

pub(crate) struct ReplayVisions<'e> {
    pub replay_visions: Option<Operand<'e>>,
    pub replay_show_entire_map: Option<Operand<'e>>,
    pub first_player_unit: Option<Operand<'e>>,
}

pub(crate) fn replay_visions<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    draw_minimap_units: E::VirtualAddress,
    is_replay: Operand<'e>,
) -> ReplayVisions<'e> {
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut exec = E::initial_state(ctx, binary);
    if let Some(mem) = is_replay.if_memory() {
        exec.move_to(&DestOperand::Memory(*mem), ctx.constant(1));
    }
    let state = ReplayVisionsState {
        visibility_mask_comparision: 0,
    };
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, draw_minimap_units, exec, state);
    let mut result = ReplayVisions {
        replay_visions: None,
        replay_show_entire_map: None,
        first_player_unit: None,
    };
    let mut analyzer = ReplayVisionsAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        inlining_draw_active_units: false,
        inlining_small_fn: 0,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone)]
struct ReplayVisionsState {
    visibility_mask_comparision: u8,
}

impl analysis::AnalysisState for ReplayVisionsState {
    fn merge(&mut self, newer: Self) {
        self.visibility_mask_comparision = newer.visibility_mask_comparision
            .min(self.visibility_mask_comparision);
    }
}

struct ReplayVisionsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ReplayVisions<'e>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining_draw_active_units: bool,
    inlining_small_fn: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for ReplayVisionsAnalyzer<'a, 'e, E> {
    type State = ReplayVisionsState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn is_unit_flags_access(val: Operand<'_>) -> bool {
            val.if_mem32()
                .and_then(|x| x.if_arithmetic_add_const(0xdc))
                .is_some()
        }

        let ctx = ctrl.ctx();
        if let Operation::Move(ref dest, val, None) = *op {
            // If reading unit flags, set cloak state to 0
            // Prevents a branch from making unit.sprite.visibility_mask undefined
            if is_unit_flags_access(val) {
                ctrl.exec_state().move_to(dest, ctx.and_const(val, !0x300));
                ctrl.skip_operation();
                return;
            }
        }
        if let Operation::SetFlags(arith) = *op {
            // Check for cmp player, 0xc.
            // make assume player < 0xc
            if arith.ty == scarf::FlagArith::Sub {
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                if left.if_constant() == Some(0xc) && right.if_custom() == Some(0) {
                    // cmp 0xc, player
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            right: ctx.const_0(),
                            ..arith
                        }));
                    ctrl.skip_operation();
                } else if left.if_custom() == Some(0) && right.if_constant() == Some(0xc) {
                    // cmp player, 0xc
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            left: ctx.const_0(),
                            ..arith
                        }));
                    ctrl.skip_operation();
                }
            } else if arith.ty == scarf::FlagArith::And {
                // Another way that cloak state may be checked
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                if is_unit_flags_access(left) {
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            left: ctx.and_const(arith.left, !0x300),
                            ..arith
                        }));
                    ctrl.skip_operation();
                } else if is_unit_flags_access(right) {
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            right: ctx.and_const(arith.right, !0x300),
                            ..arith
                        }));
                    ctrl.skip_operation();
                }
            }
        }
        if self.inlining_small_fn != 0 {
            match *op {
                Operation::Jump { .. } => {
                    self.inlining_small_fn -= 1;
                }
                Operation::Call(..) => {
                    self.inlining_small_fn = 0;
                }
                _ => (),
            }
            if self.inlining_small_fn == 0 {
                ctrl.end_analysis();
            }
            return;
        }
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                if !self.inlining_draw_active_units {
                    // Find player.
                    // 8 > x (signed)
                    // Replace it with Custom(0) if found.
                    let player_cmp = condition.if_arithmetic_gt()
                        .filter(|x| x.0.if_constant() == Some(0x8000_0008))
                        .map(|x| ctx.and_const(ctx.add_const(x.1, 0x8000_0000), 0xffff_ffff));
                    if let Some(cmp) = player_cmp {
                        let exec = ctrl.exec_state();
                        for i in 0..8 {
                            if ctx.and_const(exec.resolve(ctx.register(i)), 0xffff_ffff) == cmp {
                                let dest = DestOperand::Register64(scarf::operand::Register(i));
                                exec.move_to(&dest, ctx.custom(0));
                            }
                        }
                    }
                }
                // The main check: first_active_unit[0].sprite.visibility_mask & replay_visions
                let result = if_arithmetic_eq_neq(condition)
                    .map(|x| (x.0, x.1))
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                    .and_then(|x| x.if_arithmetic_and())
                    .and_either(|x| {
                        let sprite = x.if_mem8()?
                            .if_arithmetic_add_const(0xc)?;
                        let unit = ctrl.if_mem_word(sprite)?
                            .if_arithmetic_add_const(0xc)?;
                        ctrl.if_mem_word(unit)
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either_other(|x| {
                                x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                                    .and_then(|x| x.if_custom().filter(|&c| c == 0))
                            })
                    });
                if let Some((first_player_unit, replay_visions)) = result {
                    self.result.first_player_unit = Some(first_player_unit);
                    self.result.replay_visions = Some(replay_visions);
                    ctrl.user_state().visibility_mask_comparision = 2;
                    return;
                }
                // Assume that u32 global cmp vs 0 vision mask that is
                // replay_show_entire_map check
                let user_state = ctrl.user_state();
                if user_state.visibility_mask_comparision != 0 {
                    user_state.visibility_mask_comparision -= 1;
                    let result = if_arithmetic_eq_neq(condition)
                        .map(|x| (x.0, x.1))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                        .filter(|x| x.if_memory().is_some());
                    if let Some(replay_show_entire_map) = result  {
                        self.result.replay_show_entire_map = Some(replay_show_entire_map);
                        ctrl.end_analysis();
                        return;
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    // Check for draw_active_units call
                    if !self.inlining_draw_active_units {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1.if_custom() == Some(0) {
                            self.inlining_draw_active_units = true;
                            ctrl.inline(self, dest);
                            self.inlining_draw_active_units = false;
                            if self.result.replay_visions.is_some() {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                    }
                    // Else try inlining small fn
                    self.inlining_small_fn = 3;
                    ctrl.inline(self, dest);
                    // If inlining_small_fn gets set to 0 during inlining, inlining was stopped
                    // due to the function not being small enough.
                    if self.inlining_small_fn != 0 {
                        self.inlining_small_fn = 0;
                        ctrl.skip_operation();
                    }

                }
            }
            _ => (),
        }
    }
}

