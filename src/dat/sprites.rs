use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operation};

use crate::analysis_find::{entry_of_until, EntryOf};
use crate::util::{ControlExt};

use super::{DatType, DatPatch, DatEntryCountPatch, DatPatchContext};

/// init_hp_bar_texture() has hardcoded constant of 183 which should be replaced
/// with sprite entry count. Find by the function also referring to sprites_dat_hp_bar (Arr 1)
pub(crate) fn patch_hp_bar_init<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, '_, 'e, E>,
) -> Option<()> {
    let sprites_dat = &dat_ctx.sprites;
    let actx = dat_ctx.analysis;
    let binary = actx.binary;
    let ctx = actx.ctx;
    let sprites_dat_hp_bar = binary.read_address(
        sprites_dat.table_address + sprites_dat.entry_size * 1
    ).ok()?;
    let functions = dat_ctx.cache.function_finder();
    let global_refs = functions.find_functions_using_global(actx, sprites_dat_hp_bar);
    let funcs = dat_ctx.cache.functions();
    for global in &global_refs {
        let ok = entry_of_until(binary, &funcs, global.use_address, |entry| {
            let mut analyzer = HpBarInitAnalyzer::<E> {
                dat_ctx,
                result: EntryOf::Retry,
                use_address: global.use_address,
                jump_limit: 15,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option().is_some();
        if ok {
            return Some(());
        }
    }
    dat_warn!(self, "Could not find sprites.dat HP bar constant patch");
    Some(())
}

pub struct HpBarInitAnalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    jump_limit: u8,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    HpBarInitAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.instruction_contains_address(self.use_address) {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Jump { .. } | Operation::Call(..) => {
                if self.jump_limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
                self.jump_limit -= 1;
            }
            Operation::Move(ref dest, value, None) => {
                if ctrl.resolve(value).if_constant() == Some(0x183) {
                    let address = ctrl.address();
                    let mut patched = false;
                    match *dest {
                        DestOperand::Register64(reg) | DestOperand::Register32(reg) => {
                            let patch_len = if reg < 8 { 5 } else { 6 };
                            let instruction_len = ctrl.current_instruction_end().as_u64()
                                .wrapping_sub(address.as_u64()) as usize;
                            if instruction_len >= patch_len {
                                // Replace instruction with `mov reg, const32`
                                // and add patch in two parts: instruction start
                                // and sprites.dat entry count patch
                                let nop_count = instruction_len - patch_len;
                                if nop_count < 4 {
                                    let mut buffer = [0u8; 8];
                                    for i in 0..nop_count {
                                        buffer[i] = 0x90;
                                    }
                                    let mut i = nop_count;
                                    if reg >= 8 {
                                        buffer[i] = 0x41;
                                        i += 1;
                                    }
                                    buffer[i] = 0xb8 | (reg & 7);
                                    i += 1;
                                    let patch = &buffer[..i];
                                    let dat_ctx = &mut self.dat_ctx;
                                    let binary = ctrl.binary();
                                    // Sometimes this is just a `mov reg, const32`
                                    // instruction already, sometimes it is result
                                    // of a more complex instruction chain that
                                    // scarf can fold to constant.
                                    // If it is just a move, don't add patch for it.
                                    let already_same = binary
                                        .slice_from_address_to_end(address)
                                        .map(|slice| slice.starts_with(patch))
                                        .unwrap_or(false);
                                    if !already_same {
                                        dat_ctx.add_replace_patch(address, patch);
                                    }
                                    dat_ctx.result.patches.push(
                                        DatPatch::EntryCount(DatEntryCountPatch {
                                            dat: DatType::Sprites,
                                            size_bytes: 4,
                                            multiply: 1,
                                            address: address + i as u32,
                                        })
                                    );
                                    patched = true;
                                }
                            }
                        }
                        _ => (),
                    }
                    if !patched {
                        dat_warn!(self, "Unable to patch sprite hpbar move @ {:?}", address);
                    }
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}
