use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operation};

use crate::struct_layouts;

use super::{DatPatchContext};

/// Patches change button set action, which has `button_set < 0xfa` conditional move.
pub(crate) fn cmdbtn_analysis<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, '_, 'e, E>,
) -> Option<()> {
    let actx = &dat_ctx.analysis;
    let binary = actx.binary;
    let ctx = actx.ctx;
    let &buttonsets = dat_ctx.cache.firegraft_addresses(actx).buttonsets.get(0)?;

    let scv_basic_buildings =
        struct_layouts::button_set_index_to_action(binary, buttonsets, 7, 6)?;
    let mut analyzer = SetButtonsAnalyzer {
        dat_ctx,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, scv_basic_buildings);
    analysis.analyze(&mut analyzer);
    Some(())
}

pub struct SetButtonsAnalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SetButtonsAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                if condition != ctrl.ctx().const_1() {
                    dat_warn!(self.dat_ctx, "Reached jump @ set_buttons {:?}", ctrl.address());
                    ctrl.end_analysis();
                }
            }
            Operation::Call(..) => {
                dat_warn!(self.dat_ctx, "Reached jump @ set_buttons {:?}", ctrl.address());
                ctrl.end_analysis();
            }
            Operation::ConditionalMove(_, _, condition) => {
                let condition = ctrl.resolve(condition);
                let ok = condition.if_arithmetic_gt()
                    .filter(|x| x.0.if_constant() == Some(0xfa))
                    .is_some();
                if ok {
                    // Patch cmovb (0f 42 xx) to unconditional mov (8b xx)
                    // Account for prefix 66 (and others) too by looking at
                    // just the last bytes.
                    let binary = ctrl.binary();
                    let instruction_start = ctrl.address();
                    let instruction_end = ctrl.current_instruction_end();
                    let len = instruction_end.as_u64() - instruction_start.as_u64();
                    let ok = binary.slice_from_address(instruction_start, len as u32).ok()
                        .and_then(|bytes| {
                            let (&last, rest) = bytes.split_last()?;
                            if !rest.ends_with(&[0x0f, 0x42]) {
                                return None;
                            }
                            self.dat_ctx.add_replace_patch(
                                instruction_end - 3,
                                &[0x8b, last, 0x90],
                            );
                            Some(())
                        })
                        .is_some();
                    if ok {
                        ctrl.end_analysis();
                    } else {
                        dat_warn!(
                            self.dat_ctx, "Coudln't find cmovb to patch @ {:?}",
                            instruction_start,
                        );
                    }
                }
            }
            _ => (),
        }
    }
}
