use scarf::analysis::{self, Analyzer, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operation, OperandCtx};

/// A struct to be used as component in analyzer.
///
/// Analyzer should call `DetectTailCall::operation` for each operation received
/// to update state before other handling; the return value will be true if
/// the operation appears to be a tail call.
///
/// `DetectTailCall::operation` strives to not return `true` incorrectly, but may return
/// `false` even if human would be able to tell a jump as a tail call.
/// Especially since scarf only assumes esp/rsp stay unchanged on 64bit calls by default,
/// the results of this are currently not too good on 32bit -- But this
pub struct DetectTailCall<'e, E: ExecutionState<'e>> {
    esp_write_seen: bool,
    entry: E::VirtualAddress,
    highest_instruction: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> DetectTailCall<'e, E> {
    pub fn new(entry: E::VirtualAddress) -> DetectTailCall<'e, E> {
        DetectTailCall {
            esp_write_seen: false,
            entry,
            highest_instruction: entry,
        }
    }

    #[inline(always)]
    pub fn operation<A, S>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        op: &Operation<'e>,
    ) -> bool
    where A: Analyzer<'e, Exec = E, State = S>,
          S: analysis::AnalysisState,
    {
        let addr = ctrl.address();
        let ctx = ctrl.ctx();
        let exec_state = ctrl.exec_state();
        self.operation_impl(addr, exec_state, ctx, op)
    }

    fn operation_impl(
        &mut self,
        addr: E::VirtualAddress,
        exec_state: &mut E,
        ctx: OperandCtx<'e>,
        op: &Operation<'e>,
    ) -> bool {
        if !self.esp_write_seen {
            if let Operation::Move(DestOperand::Register64(reg), _, _) = *op {
                if reg == 4 {
                    self.esp_write_seen = true;
                }
            }
        }
        if let Operation::Jump { condition, to } = *op {
            if addr > self.highest_instruction {
                self.highest_instruction = addr;
            }
            if let Some(to) = to.if_constant() {
                let to = E::VirtualAddress::from_u64(to);
                if condition == ctx.const_1() {
                    let esp = exec_state.resolve_register(4);
                    if esp == ctx.register(4) {
                        // If esp has been written, assume any jump outside function
                        // bounds be tail call from here, otherwise allow short forward jumps.
                        let max = if self.esp_write_seen {
                            self.highest_instruction
                        } else {
                            self.highest_instruction + 0x100
                        };
                        return to < self.entry || to > max;
                    }
                }
            }
        }
        false
    }
}
