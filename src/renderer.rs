use scarf::{OperandContext, Operation, VirtualAddress, ExecutionStateX86};
use scarf::exec_state::{ExecutionState};
use scarf::analysis::{self, Control, FuncAnalysis};

use crate::{Analysis, EntryOf, OptionExt, entry_of_until, single_result_assign};

struct DrawImageEntryCheck {
    result: bool,
}

// First check in DrawImage is `if (image->flags & hidden) { return; }`
impl<'exec> scarf::Analyzer<'exec> for DrawImageEntryCheck {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'exec>;
    fn operation(&mut self, ctrl: &mut Control<Self>, op: &Operation) {
        match *op {
            Operation::Call(..) => {
                ctrl.end_analysis();
            }
            Operation::Jump { ref condition, .. } => {
                let condition = ctrl.resolve(&condition);
                self.result = condition.iter_no_mem_addr().any(|x| {
                    x.if_arithmetic_and()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0x40))
                        .and_then(|x| x.if_memory().map(|x| &x.address))
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either(|x| x.if_register().filter(|&r| r.0 == 1))
                        .is_some()
                });
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

pub fn draw_image<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> Option<VirtualAddress> {
    let switch_tables = analysis.switch_tables();
    // Switch table for drawfunc-specific code.
    // Hopefully not going to be changed. Starts from func #2 (Cloaking start)
    let switches = switch_tables.iter().filter(|switch| {
        let cases = &switch.cases;
        cases.len() == 0x10 &&
            cases[0x0] == cases[0x2] && // Cloak start == cloak end == detected start/end
            cases [0x0] == cases[0x3] &&
            cases[0x0] == cases[0x5] &&
            cases[0x1] == cases[0x6] && // Cloak == emp == remap == flag (?)
            cases[0x1] == cases[0x7] &&
            cases[0x1] == cases[0xc]
    });
    let funcs = analysis.functions();
    let binary = analysis.binary;
    let mut result = None;
    for table in switches {
        let value = entry_of_until(
            binary,
            &funcs,
            table.cases[0],
            |addr| {
                let mut analyzer = DrawImageEntryCheck {
                    result: false,
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, addr);
                analysis.analyze(&mut analyzer);
                if analyzer.result {
                    EntryOf::Ok(())
                } else {
                    EntryOf::Retry
                }
            }
        );
        if single_result_assign(value.into_option_with_entry().map(|x| x.0), &mut result) {
            break;
        }
    }

    result
}

pub fn renderer_vtables<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Vec<E::VirtualAddress> {
    crate::vtables::vtables(analysis, b".?AVRenderer@@\0")
}
