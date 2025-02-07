use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation};

use crate::analysis::{AnalysisCtx, Patch};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::analysis_state::{AnalysisState, StateEnum, ReplayVisionsState};
use crate::util::{ControlExt, ExecStateExt, OperandExt, OptionExt, bumpvec_with_capacity};
use crate::struct_layouts::StructLayouts;

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
        .and_then(|x| x.if_constant_address())
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
    let global_uses = functions.find_functions_using_global(analysis, first_fow_addr);
    for x in &global_uses {
        first_fow_uses.push(x.use_address);
    }
    let mut result = None;
    let mut draw_minimap_units = None;
    let mut i = 0;
    while i < first_fow_uses.len() {
        let use_address = first_fow_uses[i];
        let entry = entry_of_until(binary, &funcs, use_address, |entry| {
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
                let callers = functions.find_callers(analysis, entry);
                first_fow_uses.extend_from_slice_copy(&callers);
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
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inlining = false;
                    }
                }
                Operation::Return(..) => {
                    let eax = ctrl.resolve_register(0);
                    self.is_get_fn = eax == self.first_fow_sprite;
                }
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if self.fow_unit_id_checked {
                        let result = condition.if_arithmetic_eq_neq_zero(ctx)
                            .filter(|x| x.0 == self.is_replay)
                            .map(|x| x.1);
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
                            .and_then(|x| x.if_mem16_offset(fow_unit_id_offset))
                            .is_some_and(|x| x == self.first_fow_sprite);
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
    let bump = &actx.bump;
    let mut exec = E::initial_state(ctx, binary);
    if let Some(mem) = is_replay.if_memory() {
        exec.write_memory(mem, ctx.constant(1));
    }
    let state = ReplayVisionsState {
        visibility_mask_comparision: 0,
    };
    let state = AnalysisState::new(bump, StateEnum::ReplayVisions(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, draw_minimap_units, exec, state);
    let mut result = ReplayVisions {
        replay_visions: None,
        replay_show_entire_map: None,
        first_player_unit: None,
    };
    let mut analyzer = ReplayVisionsAnalyzer::<E> {
        result: &mut result,
        inlining_draw_active_units: false,
        inlining_small_fn: 0,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct ReplayVisionsAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut ReplayVisions<'e>,
    inlining_draw_active_units: bool,
    inlining_small_fn: u8,
    phantom: std::marker::PhantomData<(*const E, &'acx &'e ())>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    ReplayVisionsAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn is_unit_flags_access(struct_layouts: StructLayouts, val: Operand<'_>) -> bool {
            val.if_mem32_offset(struct_layouts.unit_flags())
                .is_some()
        }

        let ctx = ctrl.ctx();
        if let Operation::Move(ref dest, val) = *op {
            // If reading unit flags, set cloak state to 0
            // Prevents a branch from making unit.sprite.visibility_mask undefined
            if is_unit_flags_access(E::struct_layouts(), val) {
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
                if is_unit_flags_access(E::struct_layouts(), left) {
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            left: ctx.and_const(arith.left, !0x300),
                            ..arith
                        }));
                    ctrl.skip_operation();
                } else if is_unit_flags_access(E::struct_layouts(), right) {
                    ctrl.exec_state()
                        .update(&Operation::SetFlags(scarf::FlagUpdate {
                            right: ctx.and_const(arith.right, !0x300),
                            ..arith
                        }));
                    ctrl.skip_operation();
                }
            }
        }
        if let Operation::Jump { condition, to } = *op {
            // Always assume that Custom(0) (player id) < c
            // For first_player_unit bounds check
            let condition = ctrl.resolve(condition);
            let make_uncond = condition.if_arithmetic_gt()
                .is_some_and(|x| {
                    x.0.if_constant() == Some(0xc) && x.1.unwrap_and_mask().if_custom() == Some(0)
                });
            if make_uncond {
                ctrl.end_branch();
                if let Some(to) = ctrl.resolve_va(to) {
                    ctrl.add_branch_with_current_state(to);
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
                        let register_count = if E::VirtualAddress::SIZE == 4 { 8 } else { 16 };
                        for i in 0..register_count {
                            if ctx.and_const(exec.resolve_register(i), 0xffff_ffff) == cmp {
                                exec.set_register(i, ctx.custom(0));
                            }
                        }
                    }
                }
                // The main check: first_player_unit[0].sprite.visibility_mask & replay_visions
                let result = condition.if_arithmetic_eq_neq_zero(ctx)
                    .and_then(|x| x.0.if_arithmetic_and())
                    .and_either(|x| {
                        let sprite_visibility_mask = E::struct_layouts().sprite_visibility_mask();
                        let unit_sprite = E::struct_layouts().unit_sprite();
                        let sprite = x.if_mem8_offset(sprite_visibility_mask)?;
                        let unit = ctrl.if_mem_word_offset(sprite, unit_sprite)?;
                        ctrl.if_mem_word(unit)
                            .and_then(|x| {
                                x.if_add_either_other(ctx, |x| {
                                    x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                                        .filter(|&x| x.unwrap_and_mask().if_custom() == Some(0))
                                })
                            })
                    });
                let user_state = ctrl.user_state().get::<ReplayVisionsState>();
                if let Some((first_player_unit, replay_visions)) = result {
                    self.result.first_player_unit = Some(first_player_unit);
                    self.result.replay_visions = Some(replay_visions);
                    user_state.visibility_mask_comparision = 2;
                    return;
                }
                // Assume that u32 global cmp vs 0 vision mask that is
                // replay_show_entire_map check
                if user_state.visibility_mask_comparision != 0 {
                    user_state.visibility_mask_comparision -= 1;
                    let result = condition.if_arithmetic_eq_neq_zero(ctx)
                        .map(|x| x.0)
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
                        let arg1 = ctrl.resolve_arg(0);
                        if Operand::and_masked(arg1).0.if_custom() == Some(0) {
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

