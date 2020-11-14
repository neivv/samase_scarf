use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation};

use crate::{AnalysisCtx, ArgCache};

pub(crate) fn play_sound<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // Search for iscript opcode 0x18, calling into
    // play_sound_outermost(sound, xy, 1, 0)
    // which calls play_sound_outer(sound, unused?, 0, x, y)
    // which calls play_sound(sound, unused, 0, x, y)
    let iscript_switch = match analysis.step_iscript().switch_table {
        Some(s) => s,
        None => return None,
    };
    let word_size = E::VirtualAddress::SIZE;
    let playsound = match binary.read_address(iscript_switch + 0x18 * word_size) {
        Ok(o) => o,
        Err(_) => return None,
    };
    let arg_cache = analysis.arg_cache;
    let mut analyzer = PlaySoundAnalyzer::<E> {
        result: None,
        inline_depth: 0,
        sound_id: None,
        arg_cache,
        arg3_zero_seen: false,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, playsound);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct PlaySoundAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    inline_depth: u8,
    sound_id: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    arg3_zero_seen: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlaySoundAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    if self.inline_depth == 0 {
                        if arg1.if_mem16().is_some() {
                            self.sound_id = Some(arg1);
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            self.sound_id = None;
                        }
                    } else {
                        if Some(arg1) == self.sound_id {
                            let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                            let arg3_zero = arg3.if_constant() == Some(0);
                            if arg3_zero {
                                self.arg3_zero_seen = true;
                            }
                            if !self.arg3_zero_seen || arg3_zero {
                                let was_arg3_zero_seen = self.arg3_zero_seen;
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                self.arg3_zero_seen = was_arg3_zero_seen;
                                if self.result.is_none() {
                                    self.result = Some(dest);
                                }
                            }
                        }
                    }
                    if self.result.is_some() {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { to, .. } => {
                if self.inline_depth == 0 && to.if_memory().is_some() {
                    // Reached back to the switch
                    ctrl.end_branch();
                }
            }
            _ => (),
        }
    }
}
