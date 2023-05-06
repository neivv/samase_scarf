use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operation, Operand};

use crate::analysis_find::{entry_of_until, EntryOf};
use crate::util::{ControlExt, MemAccessExt};

use super::{DatPatchContext};

/// Searches for the mapdata names init code
///
/// campaign_map_names.resize(0x41);
/// followed by a loop initializing the 0x41 entries
///
/// Sets a hook point after the loop for patcher to init remaining entries.
pub(crate) fn patch_mapdata_names<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, '_, 'e, E>,
) -> Option<()> {
    let mapdata_dat = &dat_ctx.mapdata;
    let actx = dat_ctx.analysis;
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mapdata_dat_tbl = binary.read_address(mapdata_dat.table_address).ok()?;

    let functions = dat_ctx.cache.function_finder();
    let global_refs = functions.find_functions_using_global(actx, mapdata_dat_tbl);
    let funcs = dat_ctx.cache.functions();
    for global in &global_refs {
        let ok = entry_of_until(binary, &funcs, global.use_address, |entry| {
            let mut analyzer = MapDataNamesanalyzer::<E> {
                dat_ctx,
                result: EntryOf::Retry,
                use_address: global.use_address,
                map_filenames: None,
                string_size_add_seen: false,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option().is_some();
        if ok {
            return Some(());
        }
    }
    dat_warn!(self, "Could not find campaign map name patch");
    Some(())
}

pub struct MapDataNamesanalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    map_filenames: Option<Operand<'e>>,
    /// Assume that after the code does x += C, followed by jump backwards
    /// to be the looping instruction.
    string_size_add_seen: bool,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    MapDataNamesanalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.instruction_contains_address(self.use_address) {
            self.result = EntryOf::Stop;
        }
        if let Some(map_filenames) = self.map_filenames {
            if let Operation::Jump { condition, to } = *op {
                let ctx = ctrl.ctx();
                if self.string_size_add_seen && condition != ctx.const_1() {
                    if let Some(to) = ctrl.resolve_va(to) {
                        if to < ctrl.address() {
                            self.dat_ctx.result.campaign_map_names =
                                Some((map_filenames, ctrl.current_instruction_end()));
                            self.result = EntryOf::Ok(());
                            ctrl.end_analysis();
                        }
                    }
                }
                self.string_size_add_seen = false;
            } else if let Operation::Move(dest, value, None) = *op {
                // Not counting additions to stack
                if dest != DestOperand::Register64(4) {
                    // Assume string to be at least 3 words large.
                    // Likely has inline buffer adding more size but staying
                    // flexible wrt that
                    let min_size = 0x3 * E::VirtualAddress::SIZE;
                    let ok = Operand::and_masked(value).0.if_arithmetic_add()
                        .and_then(|(l, r)| {
                            [l, r].into_iter().find_map(|x| {
                                if ctrl.resolve(x).if_constant()? >= min_size as u64 {
                                    Some(())
                                } else {
                                    None
                                }
                            })
                        })
                        .is_some();
                    if ok {
                        self.string_size_add_seen = true;
                    }
                }
            }
        } else {
            if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                // Assuming this be store of vector.length
                if ctrl.resolve(value).if_constant() == Some(0x41) {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.is_global() {
                        let ctx = ctrl.ctx();
                        let vector = mem
                            .with_offset(0u64.wrapping_sub(E::VirtualAddress::SIZE as u64))
                            .address_op(ctx);
                        self.map_filenames = Some(vector);
                        ctrl.clear_all_branches();
                    }
                }
            }
        }
    }
}
