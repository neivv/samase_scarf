use fxhash::FxHashSet;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Operation};

use crate::util::{ControlExt, OperandExt};
use super::{DatPatchContext};

/// Patches unit id checks in conditions / actions. They differ
/// from other checks in that they check for `unit_id < 0xe9` since
/// there are supported group ids.
pub(crate) fn trigger_analysis<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, '_, 'e, E>,
) -> Option<()> {
    let analysis = &dat_ctx.analysis;
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let conditions = dat_ctx.cache.trigger_conditions(analysis)?;
    let actions = dat_ctx.cache.trigger_actions(analysis)?;

    // Most of these aren't necessary unless there's aggressive inlining,
    // only command + kills + deaths would suffice.
    static CONDITIONS_TO_CHECK: &[u8] = &[
        0x02, // Command
        0x03, // Bring
        0x05, // Kill
        0x06, // Command the Most
        0x07, // Command the Most At
        0x08, // Most Kills
        0x0f, // Deaths
        0x10, // Command the Least
        0x11, // Command the Least At
        0x12, // Least Kills
    ];
    let mut checked_functions = FxHashSet::with_capacity_and_hasher(0x40, Default::default());
    for &condition_id in CONDITIONS_TO_CHECK {
        let addr = conditions + condition_id as u32 * E::VirtualAddress::SIZE;
        let func = binary.read_address(addr).ok()?;
        let mut analyzer = TriggerPatchAnalyzer {
            checked_functions: &mut checked_functions,
            dat_ctx,
            is_action: false,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
    }
    // Also patch set deaths action
    let addr = actions + 0x2d * E::VirtualAddress::SIZE;
    let func = binary.read_address(addr).ok()?;
    let mut analyzer = TriggerPatchAnalyzer {
        checked_functions: &mut checked_functions,
        dat_ctx,
        is_action: true,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    Some(())
}

pub struct TriggerPatchAnalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    checked_functions: &'a mut FxHashSet<E::VirtualAddress>,
    is_action: bool,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    TriggerPatchAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let arg_cache = &self.dat_ctx.analysis.arg_cache;
                let compare = match self.is_action {
                    true => 0xe3,
                    false => 0xe8,
                };
                let offset = match self.is_action {
                    true => 0x18,
                    false => 0xc,
                };
                let ok = condition.if_arithmetic_gt_const(compare)
                    .and_then(|x| x.if_mem16_offset(offset))
                    .filter(|&x| x == arg_cache.on_entry(0))
                    .is_some();
                if ok {
                    self.convert_jae_to_je(ctrl.binary(), ctrl.address());
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.checked_functions.insert(dest) {
                        // Check for [arg1 + c] for unit_id
                        // (arg1 + 18 for action)
                        let offset = match self.is_action {
                            true => 0x18,
                            false => 0xc,
                        };
                        let arg_cache = &self.dat_ctx.analysis.arg_cache;
                        let ok = Some(ctrl.resolve_arg(1))
                            .and_then(|x| x.if_mem16_offset(offset))
                            .filter(|&x| x == arg_cache.on_entry(0))
                            .is_some();
                        if ok {
                            ctrl.analyze_with_current_state(self, dest);
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> TriggerPatchAnalyzer<'a, 'b, 'acx, 'e, E> {
    fn convert_jae_to_je(
        &mut self,
        binary: &'e BinaryFile<E::VirtualAddress>,
        address: E::VirtualAddress,
    ) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self.dat_ctx, "Can't convert jump @ {:?}", address);
                return;
            }
        };
        match *bytes {
            [0x0f, 0x83, ..] => {
                self.dat_ctx.add_replace_patch(address + 1, &[0x84]);
            }
            [0x73, ..] => {
                self.dat_ctx.add_replace_patch(address, &[0x74]);
            }
            _ => dat_warn!(self.dat_ctx, "Can't convert jump @ {:?}", address),
        }
    }
}
