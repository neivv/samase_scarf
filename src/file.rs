use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};
use scarf::operand::{Operand};
use scarf::{BinaryFile, BinarySection, DestOperand, Operation};

use crate::{AnalysisCtx, ArgCache, if_callable_const, FunctionFinder, single_result_assign};

struct FindLoadDat<'acx, 'e, E: ExecutionState<'e>> {
    result: BumpVec<'acx, (E::VirtualAddress, E::VirtualAddress)>,
    string_address: E::VirtualAddress,
    arg_cache: &'acx ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindLoadDat<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            let dest = if_callable_const(self.binary, dest, ctrl);
            let arg1 = ctrl.resolve(self.arg_cache.on_call(0)).if_constant();
            let arg2 = ctrl.resolve(self.arg_cache.on_call(1)).if_constant();
            if let (Some(dest), Some(arg1), Some(_)) = (dest, arg1, arg2) {
                if arg1 == self.string_address.as_u64() {
                    self.result.push((ctrl.address(), dest));
                }
            }
        }
    }
}

/// Return (Vec<(call_ins_address, call_dest)>, errors)
pub(crate) fn find_load_dat_fn<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    parent: E::VirtualAddress,
    string_address: E::VirtualAddress,
) -> BumpVec<'acx, (E::VirtualAddress, E::VirtualAddress)> {
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let mut analysis: FuncAnalysis<'_, E, _> = FuncAnalysis::new(binary, ctx, parent);
    let mut analyzer = FindLoadDat {
        result: BumpVec::new_in(bump),
        string_address,
        arg_cache,
        binary,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result.sort_unstable();
    analyzer.result.dedup();
    analyzer.result
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Arg {
    Stack(u8),
    // TODO: Register
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct OpenFileFnIntermediate<Va: VirtualAddressTrait> {
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
        let arg1_store = ctx.mem64(ctx.custom(0));
        let arg1_addr = arg_cache.on_entry(0);
        let arg1 = state.resolve(arg1_addr);
        state.move_to(&DestOperand::from_oper(arg1_store), arg1);
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
            binary,
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
            binary: &'e BinaryFile<E::VirtualAddress>,
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
                    let dest = if_callable_const(self.binary, dest, ctrl);
                    let new_arg_pos = find_name_arg(self.arg_cache, self.filename_arg, ctrl);
                    if let (Some(dest), Some(new_arg)) = (dest, new_arg_pos) {
                        self.functions.push(OpenFileFnIntermediate {
                            address: dest,
                            filename_arg: new_arg,
                        });
                    } else if self.filename_arg == Arg::Stack(1) && !self.ok {
                        // Inline if arg1 is currently being passed as ecx
                        if let Some(dest) = dest {
                            let ctx = ctrl.ctx();
                            if !self.inlining {
                                let ecx = ctrl.resolve(ctx.register_ref(1));
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
                        let arg1_out = ctrl.mem_word(ctrl.const_word_offset(self.arg1_store, i));
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
        let resolved = ctrl.resolve(arg_cache.on_call(i));
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
    load_dat_fns.extend(
        str_refs.iter().flat_map(|str_ref| {
            let func = str_ref.func_entry;
            let result = find_load_dat_fn(analysis, func, str_ref.string_address);
            result.into_iter().map(|x| x.1)
        })
    );
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
