use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState};
use scarf::{DestOperand, MemAccessSize, Operand, Operation};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::switch;
use crate::util::{ControlExt, OptionExt};

pub(crate) struct PlaySound<'e> {
    pub sfx_data: Option<Operand<'e>>,
    pub sound_channels: Option<Operand<'e>>,
}

pub(crate) fn play_sound<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    iscript_switch: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // Search for iscript opcode 0x18, calling into
    // play_sound_outermost(sound, xy, 1, 0)
    // which calls play_sound_outer(sound, unused?, 0, x, y)
    // which calls play_sound(sound, unused, 0, x, y)
    let playsound = switch::simple_switch_branch(binary, iscript_switch, 0x18)?;
    let arg_cache = &analysis.arg_cache;
    let mut analyzer = PlaySoundAnalyzer::<E> {
        result: None,
        inline_depth: 0,
        sound_id: None,
        arg_cache,
        arg3_zero_seen: false,
        inner_arg4: None,
        inner_arg5: None,
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
    inner_arg4: Option<Operand<'e>>,
    inner_arg5: Option<Operand<'e>>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlaySoundAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ctx = ctrl.ctx();
                    if self.inline_depth == 0 {
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if arg1.if_mem16().is_some() {
                            self.sound_id = Some(arg1);
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            self.sound_id = None;
                        }
                    } else {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if Some(arg1) == self.sound_id {
                            let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                            let arg3_zero = arg3 == ctx.const_0();
                            if arg3_zero {
                                if self.arg3_zero_seen {
                                    let ok = Some(ctrl.resolve(self.arg_cache.on_call(3))) ==
                                            self.inner_arg4 &&
                                        Some(ctrl.resolve(self.arg_cache.on_call(4))) ==
                                            self.inner_arg5;
                                    if !ok {
                                        return;
                                    }
                                } else {
                                    self.inner_arg4 =
                                        Some(ctrl.resolve(self.arg_cache.on_call(3)));
                                    self.inner_arg5 =
                                        Some(ctrl.resolve(self.arg_cache.on_call(4)));
                                    self.arg3_zero_seen = true;
                                }
                            }
                            if !self.arg3_zero_seen || arg3_zero {
                                let was_arg3_zero_seen = self.arg3_zero_seen;
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                self.arg3_zero_seen = was_arg3_zero_seen;
                                if self.result.is_none() && arg3_zero {
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
                if self.inline_depth == 0 && to.if_constant().is_none() {
                    // Reached back to the switch
                    ctrl.end_branch();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_play_sound<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    play_sound: E::VirtualAddress,
) -> PlaySound<'e> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let arg_cache = &analysis.arg_cache;
    let mut result = PlaySound {
        sfx_data: None,
        sound_channels: None,
    };
    let mut analyzer = PlaySoundFnAnalyzer::<E> {
        result: &mut result,
        arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, play_sound);
    analysis.analyze(&mut analyzer);
    result
}

struct PlaySoundFnAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut PlaySound<'e>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlaySoundFnAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // Just search for sound_channel.x6 = sfx_data[sound].x5b / x7f
        // Both sound channel and sfxdata struct sizes/layouts have changed across patches.
        if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
            let ctx = ctrl.ctx();
            // Skip stack writes early
            if mem.size != MemAccessSize::Mem8 || mem.address().0 == ctx.register(4) {
                return;
            }
            let value = ctrl.resolve(value);
            let sfx_data = value
                .if_mem8()
                .and_then(|x| {
                    let (base, offset) = x.address();
                    (0x30..0x100).contains(&offset)
                        .then_some(base)?
                        .if_arithmetic_add()
                })
                .and_either_other(|x| {
                    let (l, c) = x.if_mul_with_const()?;
                    (c >= 0x80 && c < 0x150 &&
                        ctx.and_const(l, 0xffff_ffff) ==
                        ctx.and_const(self.arg_cache.on_entry(0), 0xffff_ffff)
                    ).then_some(())
                });
            if let Some(sfx) = sfx_data {
                let mem = ctrl.resolve_mem(mem);
                let channels = mem
                    .if_add_either_other(ctx, |x| {
                        x.if_mul_with_const().filter(|x| (0x18..0x30).contains(&x.1))
                    })
                    .map(|x| ctx.sub_const(x, 0x6));
                if let Some(channels) = channels {
                    self.result.sfx_data = Some(sfx);
                    self.result.sound_channels = Some(channels);
                    ctrl.end_analysis();
                }
            }
        }
    }
}
