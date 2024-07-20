use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{Operand};
use scarf::{BinaryFile, BinarySection, MemAccessSize, Operation};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{FunctionFinder};
use crate::util::{single_result_assign, is_global, ControlExt, OperandExt};

pub(crate) struct OpenFile<Va: VirtualAddress> {
    pub file_exists: Option<Va>,
}

struct FindLoadDat<'acx, 'e, E: ExecutionState<'e>> {
    result: BumpVec<'acx, E::VirtualAddress>,
    string_address: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindLoadDat<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let arg1 = ctrl.resolve_arg(0).if_constant();
                let arg2 = ctrl.resolve_arg(1).if_constant();
                if let (Some(arg1), Some(_)) = (arg1, arg2) {
                    if arg1 == self.string_address.as_u64() {
                        self.result.push(dest);
                    }
                }
            }
        }
    }
}

/// Return Vec<call_dest>
pub(crate) fn find_load_dat_fn<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    parent: E::VirtualAddress,
    string_address: E::VirtualAddress,
) -> BumpVec<'acx, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let mut analysis: FuncAnalysis<'_, E, _> = FuncAnalysis::new(binary, ctx, parent);
    let mut analyzer = FindLoadDat {
        result: BumpVec::new_in(bump),
        string_address,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Arg {
    Stack(u8),
    // TODO: Register
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct OpenFileFnIntermediate<Va: VirtualAddress> {
    address: Va,
    filename_arg: Arg,
}

fn find_open_file_fn<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    load_dat_fn: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let arg_cache = &analysis.arg_cache;
    let rdata = analysis.binary_sections.rdata;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let mut functions = bumpalo::vec![in bump; OpenFileFnIntermediate {
        address: load_dat_fn,
        filename_arg: Arg::Stack(0),
    }];
    let mut checked_functions = BumpVec::new_in(bump);
    let mut result = None;

    while let Some(func) = functions.pop() {
        if checked_functions.iter().any(|&x| x == func.address) {
            continue;
        }
        checked_functions.push(func.address);

        let mut state = E::initial_state(ctx, binary);
        let arg1_store_addr = ctx.mem_access64(ctx.custom(0), 0);
        let arg1_store = ctx.memory(&arg1_store_addr);
        let arg1_addr = arg_cache.on_entry(0);
        let arg1 = state.resolve(arg1_addr);
        state.write_memory(&arg1_store_addr, arg1);
        let mut analysis = FuncAnalysis::with_state(
            binary,
            ctx,
            func.address,
            state,
        );
        let mut analyzer = Analyzer {
            functions: &mut functions,
            filename_arg: func.filename_arg,
            ok: false,
            arg1_store,
            rdata,
            arg_cache,
            inlining: false,
        };
        analysis.analyze(&mut analyzer);

        struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
            functions: &'a mut BumpVec<'acx, OpenFileFnIntermediate<E::VirtualAddress>>,
            filename_arg: Arg,
            ok: bool,
            arg1_store: Operand<'e>,
            rdata: &'e BinarySection<E::VirtualAddress>,
            arg_cache: &'acx ArgCache<'e, E>,
            inlining: bool,
        }
        impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
            Analyzer<'a, 'acx, 'e, E>
        {
            type State = analysis::DefaultState;
            type Exec = E;
            fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let new_arg_pos = find_name_arg(self.arg_cache, self.filename_arg, ctrl);
                        if let Some(new_arg) = new_arg_pos {
                            self.functions.push(OpenFileFnIntermediate {
                                address: dest,
                                filename_arg: new_arg,
                            });
                        } else if self.filename_arg == Arg::Stack(1) && !self.ok {
                            // Inline if arg1 is currently being passed as ecx
                            if !self.inlining {
                                let ecx = ctrl.resolve_register(1);
                                if ecx == self.arg_cache.on_entry(0) {
                                    self.inlining = true;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inlining = false;
                                }
                            }
                        }
                    }
                }
            }

            fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
                if self.filename_arg == Arg::Stack(1) && !self.ok {
                    // Don't immediately end analysis even if ok, can still find other functions.
                    self.ok |= (0..3).all(|i| {
                        let arg1_out = ctrl.mem_word(
                            self.arg1_store,
                            i * E::VirtualAddress::SIZE as u64,
                        );
                        let resolved = ctrl.resolve(arg1_out);
                        let rdata = self.rdata;
                        match resolved.if_constant() {
                            Some(c) => {
                                let rdata_end = rdata.virtual_address + rdata.data.len() as u32;
                                c >= rdata.virtual_address.as_u64() && c < rdata_end.as_u64()
                            }
                            None => false,
                        }
                    });
                }
            }
        }
        if analyzer.ok {
            if single_result_assign(Some(func.address), &mut result) {
                break;
            }
        }
    }
    result
}

/// State has to be right before call ins
fn find_name_arg<'e, A: analysis::Analyzer<'e>>(
    arg_cache: &ArgCache<'e, A::Exec>,
    arg: Arg,
    ctrl: &mut Control<'e, '_, '_, A>
) -> Option<Arg> {
    (0..10).filter_map(|i| {
        let resolved = ctrl.resolve_arg(i);
        match arg {
            Arg::Stack(s) => {
                let equiv = arg_cache.on_entry(s);
                if resolved == equiv {
                    Some(Arg::Stack(i))
                } else {
                    None
                }
            }
        }
    }).next()
}

pub(crate) fn open_file<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let str_refs = functions.string_refs(analysis, b"arr\\units.");

    let mut load_dat_fns = BumpVec::new_in(bump);
    for str_ref in &str_refs {
        let func = str_ref.func_entry;
        let result = find_load_dat_fn(analysis, func, str_ref.string_address);
        load_dat_fns.extend_from_slice_copy(&result);
    }
    if load_dat_fns.is_empty() {
        return None;
    }
    load_dat_fns.sort_unstable();
    load_dat_fns.dedup();
    let mut result = None;
    for &addr in &load_dat_fns {
        let new = find_open_file_fn(analysis, binary, addr);
        if single_result_assign(new, &mut result) {
            break;
        }
    }
    result
}

pub(crate) fn open_file_analysis<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    open_file: E::VirtualAddress,
) -> OpenFile<E::VirtualAddress> {
    let mut result = OpenFile {
        file_exists: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analysis = FuncAnalysis::new(binary, ctx, open_file);
    let mut analyzer = AnalyzeOpenFile {
        result: &mut result,
        arg_cache: &actx.arg_cache,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeOpenFile<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OpenFile<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeOpenFile<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                // file_exists(&local_buffer, 104, path(arg2), open_params(arg3))
                let arg_cache = self.arg_cache;
                let ok = ctrl.resolve_arg(1).if_constant() == Some(0x104) &&
                    ctrl.resolve_arg(2) == arg_cache.on_entry(1) &&
                    ctrl.resolve_arg(3) == arg_cache.on_entry(2) &&
                    !is_global(ctrl.resolve_arg(0));
                if ok {
                    self.result.file_exists = Some(dest);
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) fn read_fatal_error<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    load_dat: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analysis = FuncAnalysis::new(binary, ctx, load_dat);
    let mut analyzer = AnalyzeLoadDat {
        result: None,
        arg_cache: &actx.arg_cache,
        custom_jump_seen: false,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AnalyzeLoadDat<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    custom_jump_seen: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeLoadDat<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // Assume that arg2 == 0 on jumps,
        // when calling read_file_x(arg1, 0, &mut out_size, ...) set out_size to custom
        // Find jump with custom != 0
        if let Operation::Jump { condition, to } = *op {
            let ctx = ctrl.ctx();
            let condition = ctrl.resolve(condition);
            if let Some((var, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                if ctrl.if_mem_word(var).map(|x| x.address()) ==
                    Some((self.arg_cache.on_entry(1), 0))
                {
                    ctrl.continue_at_eq_address(eq, to);
                } else if Operand::and_masked(var).0.if_custom().is_some() {
                    ctrl.clear_unchecked_branches();
                    ctrl.continue_at_neq_address(eq, to);
                    self.custom_jump_seen = true;
                }
            }
        } else if let Operation::Call(dest) = *op {
            let ctx = ctrl.ctx();
            let arg1 = ctrl.resolve_arg(0);
            if arg1 == self.arg_cache.on_entry(0) {
                if self.custom_jump_seen {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.result = Some(dest);
                        ctrl.end_analysis();
                        return;
                    }
                } else {
                    let arg3 = ctrl.resolve_arg(2);
                    ctrl.write_memory(
                        &ctx.mem_access(arg3, 0, MemAccessSize::Mem32),
                        ctx.custom(0),
                    );
                }
            }
            if dest.if_constant().is_none() {
                // May have inlined that read_file_x, detect
                // file.vtbl.get_file_size(file) call too and assign custom.
                let dest = ctrl.resolve(dest);
                let ecx = ctrl.resolve_register(1);
                let is_vtable_call = ctrl.if_mem_word(dest)
                    .and_then(|x| ctrl.if_mem_word(x.address().0)) ==
                    Some(&ctx.mem_access(ecx, 0, E::WORD_SIZE));
                if is_vtable_call {
                    ctrl.do_call_with_result(ctx.custom(0));
                }
            }
            if self.custom_jump_seen {
                self.custom_jump_seen = false;
            }
        }
    }
}
