use scarf::{Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{OperandHashByAddress};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::hash_map::HashSet;
use crate::util::{ControlExt, OperandExt, is_global};

pub(crate) struct ReadWholeMpqFile<'e, Va: VirtualAddress> {
    pub mpq_locale: Option<Operand<'e>>,
    // Decided to add this since it is pretty much free,
    // but also pretty useless so it is not in the public api.
    pub mpq_platform: Option<Operand<'e>>,
    pub sfile_open_file_ex: Option<Va>,
    pub sfile_read_file_ex: Option<Va>,
    pub sfile_close_file: Option<Va>,
}

pub(crate) fn analyze_read_whole_mpq_file<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    read_whole_mpq_file: E::VirtualAddress,
) -> ReadWholeMpqFile<'e, E::VirtualAddress> {
    let mut result = ReadWholeMpqFile {
        mpq_locale: None,
        mpq_platform: None,
        sfile_open_file_ex: None,
        sfile_read_file_ex: None,
        sfile_close_file: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;

    let mut analysis = FuncAnalysis::new(binary, ctx, read_whole_mpq_file);
    let mut analyzer = AnalyzeReadWholeMpqFile::<E> {
        result: &mut result,
        state: MpqFileState::OpenArchive,
        inline_depth: 0,
        checked_functions: HashSet::with_capacity_and_hasher(0x20, Default::default()),
        arg_cache,
        entry_esp_base: ctx.register(4),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum MpqFileState {
    // Find result by finding mpq hash table lookup func
    // read_whole_mpq_file(a1 (mpq), a2 (path), a3, a4, a5, a6 (flags), ...)
    //   calls SFileOpenFileEx(a1, a2, a6, out)
    //     calls child2(a1, a2, a6, out, 0, out, ...)
    //       calls mpq_lookup_file(_, _, a6, locale_global, platform_global, out)
    OpenArchive,
    // SFileReadFileEx should be (file, _, _, 0, a7, a8, 0)
    ReadFile,
    // Only function with file in arg1 after read
    CloseFile,
}

struct AnalyzeReadWholeMpqFile<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ReadWholeMpqFile<'e, E::VirtualAddress>,
    state: MpqFileState,
    inline_depth: u8,
    checked_functions: HashSet<OperandHashByAddress<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    entry_esp_base: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeReadWholeMpqFile<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            MpqFileState::OpenArchive => {
                if let Operation::Call(dest) = *op {
                    if !self.checked_functions.insert(dest.hash_by_address()) {
                        return;
                    }
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ctx = ctrl.ctx();
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
                        let arg3 = ctrl.resolve_arg(2);
                        let arg4 = ctrl.resolve_arg(3);
                        let arg5 = ctrl.resolve_arg(4);
                        let ok = match self.inline_depth {
                            0 => {
                                arg1 == self.arg_cache.on_entry(0) &&
                                    arg2 == self.arg_cache.on_entry(1) &&
                                    ctx.and_const(arg3, 0xffff_ffff) ==
                                        ctx.and_const(self.arg_cache.on_entry(5), 0xffff_ffff) &&
                                    self.is_stack_ref(ctrl, arg4)
                            }
                            1 => {
                                arg1 == self.arg_cache.on_entry(0) &&
                                    arg2 == self.arg_cache.on_entry(1) &&
                                    ctx.and_const(arg3, 0xffff_ffff) ==
                                        ctx.and_const(self.arg_cache.on_entry(5), 0xffff_ffff) &&
                                    self.is_stack_ref(ctrl, arg4) &&
                                    arg5 == ctx.const_0()
                            }
                            2 | _ => {
                                let arg6 = ctrl.resolve_arg(5);
                                // Checking that locale_global must be global, but
                                // not platform_global, as it is semi-unused and smart
                                // compiler could just compile it to 0.
                                ctx.and_const(arg3, 0xffff_ffff) ==
                                        ctx.and_const(self.arg_cache.on_entry(5), 0xffff_ffff) &&
                                    is_global(arg4) &&
                                    arg4.relevant_bits().end >= 16 &&
                                    self.is_stack_ref(ctrl, arg6)
                            }
                        };
                        if ok {
                            if self.inline_depth >= 2 {
                                self.result.mpq_locale = Some(arg4);
                                if is_global(arg5) {
                                    self.result.mpq_platform = Some(arg5);
                                }
                            } else {
                                self.inline_depth += 1;
                                let old_esp_base = self.entry_esp_base;
                                self.entry_esp_base = ctrl.resolve_register(4).add_sub_offset().0;
                                ctrl.analyze_with_current_state(self, dest);
                                self.entry_esp_base = old_esp_base;
                                self.inline_depth -= 1;
                            }
                            if self.result.mpq_locale.is_some() {
                                if self.inline_depth == 0 {
                                    self.result.sfile_open_file_ex = Some(dest);
                                    let arg4_mem = ctx.mem_access(arg4, 0, E::WORD_SIZE);
                                    ctrl.write_memory(&arg4_mem, ctx.custom(0));
                                    ctrl.do_call_with_result(ctx.const_1());
                                    ctrl.clear_unchecked_branches();
                                    self.state = MpqFileState::ReadFile;
                                } else {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            MpqFileState::ReadFile => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ctx = ctrl.ctx();
                        let zero = ctx.const_0();
                        let ok = ctrl.resolve_arg(0).if_custom() == Some(0) &&
                            ctrl.resolve_arg(3) == zero &&
                            ctrl.resolve_arg(4) == self.arg_cache.on_entry(6) &&
                            ctrl.resolve_arg_u32(5) ==
                                ctx.and_const(self.arg_cache.on_entry(7), 0xffff_ffff) &&
                            ctrl.resolve_arg(6) == zero;
                        if ok {
                            self.result.sfile_read_file_ex = Some(dest);
                            ctrl.clear_unchecked_branches();
                            ctrl.do_call_with_result(ctx.const_0());
                            self.state = MpqFileState::CloseFile;
                        }
                    }
                }
            }
            MpqFileState::CloseFile => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        if arg1.if_custom() == Some(0) {
                            self.result.sfile_close_file = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> AnalyzeReadWholeMpqFile<'a, 'e, E> {
    fn is_stack_ref(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, value: Operand<'e>) -> bool {
        let value_base = value.add_sub_offset().0;
        value_base == self.entry_esp_base ||
            value_base == ctrl.resolve_register(4).add_sub_offset().0
    }
}
