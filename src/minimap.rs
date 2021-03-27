use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation};

use crate::{
    AnalysisCtx, EntryOf, entry_of_until, if_arithmetic_eq_neq, OperandExt,
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
