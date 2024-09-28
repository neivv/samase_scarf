use scarf::analysis::{Analyzer, Control};
use scarf::{DestOperand, ExecutionState, Operand};

use super::PARTIAL_REGISTER_CLEAR_CUSTOM;

/// Scarf analysis component:
/// Makes writes to Register16, Register8Low zero high bits
/// of the register, as long as no Register8High writes have
/// been seen.
/// Will improve state merge quality as long as the code isn't intentionally
/// depending on the value in high bytes (Which seems hard to imagine as long
/// as ah/ch/dh/bh aren't explicitly used)
///
/// Otherwise scarf allowing customization of state merge, so that analysis
/// could spend time keeping low8 value without making it undefined could be fine too,
/// and not cause as inaccurate analysis as this solution does.
pub struct PartialRegisterMoves {
    // This could be AnalysisState that is merged / cleared too,
    // but probably just having it be function-wide will be enough.
    high_seen: u8,
}

impl PartialRegisterMoves {
    pub fn new() -> PartialRegisterMoves {
        PartialRegisterMoves {
            high_seen: 0,
        }
    }

    /// Zeroes the high bytes destination if this is low register move.
    /// (Because of that, it probably should be done at end of operation() handling)
    pub fn operation_move<'e, A>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        dest: &DestOperand<'e>,
        value: Operand<'e>,
        did_skip_operation: bool,
    )
    where A: Analyzer<'e>
    {
        match *dest {
            DestOperand::Arch(arch) => {
                if let Some(reg) = arch.if_x86_register_16()
                    .or_else(|| arch.if_x86_register_8_low())
                {
                    let is_16_bit = arch.if_x86_register_16().is_some();
                    let zero = if reg >= 4 || is_16_bit {
                        true
                    } else {
                        let bit = 1u8 << reg;
                        self.high_seen & bit == 0
                    };
                    if zero {
                        let ctx = ctrl.ctx();
                        let state = ctrl.exec_state();
                        let old = state.resolve_register(reg);
                        let keep_bits = match is_16_bit {
                            false => 8,
                            true => 16,
                        };
                        let mask = (1u32 << keep_bits).wrapping_sub(1) as u64;
                        let value = if did_skip_operation {
                            old
                        } else {
                            // Can't just clear high bits since the operation may be
                            // mov `al, byte [ecx + eax]` or such.
                            // Instead skip operation and do sign extended move here.
                            ctrl.skip_operation();
                            ctrl.resolve(value)
                        };
                        let custom = ctx.custom(PARTIAL_REGISTER_CLEAR_CUSTOM + reg as u32);
                        let cleared = ctx.or(
                            ctx.and_const(value, mask),
                            ctx.and_const(custom, !mask),
                        );
                        ctrl.exec_state().set_register(reg, cleared);
                    }
                } else if let Some(reg) = arch.if_x86_register_8_high() {
                    if reg < 4 {
                        let bit = 1u8 << reg;
                        self.high_seen |= bit;
                    }
                }
            }
            _ => (),
        }
    }
}
