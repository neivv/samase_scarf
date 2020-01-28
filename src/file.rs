use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, InternMap, VirtualAddress as VirtualAddressTrait};
use scarf::operand::{Operand};
use scarf::{BinaryFile, BinarySection, DestOperand, Operation};

use crate::{Analysis, ArgCache, if_callable_const};

struct FindLoadDat<'a, 'e, E: ExecutionState<'e>> {
    result: Vec<(E::VirtualAddress, E::VirtualAddress)>,
    string_address: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindLoadDat<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        if let Operation::Call(ref dest) = *op {
            let (state, interner) = ctrl.exec_state();
            let dest = if_callable_const(self.binary, state, dest, interner);
            let arg1 = ctrl.resolve(&self.arg_cache.on_call(0)).if_constant();
            let arg2 = ctrl.resolve(&self.arg_cache.on_call(1)).if_constant();
            if let (Some(dest), Some(arg1), Some(_)) = (dest, arg1, arg2) {
                if arg1 == self.string_address.as_u64() {
                    self.result.push((ctrl.address(), dest));
                }
            }
        }
    }
}

/// Return (Vec<(call_ins_address, call_dest)>, errors)
pub fn find_load_dat_fn<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    parent: E::VirtualAddress,
    string_address: E::VirtualAddress,
) -> Vec<(E::VirtualAddress, E::VirtualAddress)> {
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut analysis: FuncAnalysis<'_, E, _> = FuncAnalysis::new(binary, ctx, parent);
    let mut analyzer = FindLoadDat {
        result: Vec::new(),
        string_address,
        arg_cache,
        binary,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result.sort();
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

fn find_open_file_fn<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    load_dat_fn: E::VirtualAddress,
) -> Vec<E::VirtualAddress> {
    let arg_cache = &analysis.arg_cache;
    let rdata = binary.section(b".rdata\0\0").unwrap();
    let ctx = analysis.ctx;
    let mut functions = vec![OpenFileFnIntermediate {
        address: load_dat_fn,
        filename_arg: Arg::Stack(0),
    }];
    let mut checked_functions = Vec::new();
    let mut result = Vec::new();

    while let Some(func) = functions.pop() {
        if checked_functions.iter().any(|&x| x == func.address) {
            continue;
        }
        checked_functions.push(func.address);

        let mut interner = InternMap::new();
        let mut state = E::initial_state(ctx, binary, &mut interner);
        let arg1_store = ctx.mem64(&ctx.custom(0));
        let arg1_addr = arg_cache.on_entry(0);
        let arg1 = state.resolve(&arg1_addr, &mut interner);
        state.move_to(&DestOperand::from_oper(&arg1_store), arg1, &mut interner);
        let mut analysis = FuncAnalysis::with_state(
            binary,
            ctx,
            func.address,
            state,
            interner,
        );
        let mut analyzer = Analyzer {
            functions: &mut functions,
            filename_arg: func.filename_arg,
            ok: false,
            arg1_store,
            binary,
            rdata,
            arg_cache,
        };
        analysis.analyze(&mut analyzer);

        struct Analyzer<'a, 'e, E: ExecutionState<'e>> {
            functions: &'a mut Vec<OpenFileFnIntermediate<E::VirtualAddress>>,
            filename_arg: Arg,
            ok: bool,
            arg1_store: Rc<Operand>,
            binary: &'e BinaryFile<E::VirtualAddress>,
            rdata: &'e BinarySection<E::VirtualAddress>,
            arg_cache: &'a ArgCache<'e, E>,
        };
        impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'a, 'e, E> {
            type State = analysis::DefaultState;
            type Exec = E;
            fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
                if let Operation::Call(ref dest) = op {
                    let (state, i) = ctrl.exec_state();
                    let dest = if_callable_const(self.binary, state, dest, i);
                    let new_arg_pos = find_name_arg(self.arg_cache, state, self.filename_arg, i);
                    if let (Some(dest), Some(new_arg)) = (dest, new_arg_pos) {
                        self.functions.push(OpenFileFnIntermediate {
                            address: dest,
                            filename_arg: new_arg,
                        });
                    }
                }
            }

            fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
                if self.filename_arg == Arg::Stack(1) && !self.ok {
                    // Don't immediately end analysis even if ok, can still find other functions.
                    self.ok |= (0..3).all(|i| {
                        let arg1_out = Operand::simplified(
                            ctrl.mem_word(ctrl.const_word_offset(self.arg1_store.clone(), i)),
                        );
                        let resolved = ctrl.resolve(&arg1_out);
                        let rdata = self.rdata;
                        match resolved.ty {
                            scarf::OperandType::Constant(c) => {
                                let rdata_end = rdata.virtual_address + rdata.data.len() as u32;
                                c >= rdata.virtual_address.as_u64() && c < rdata_end.as_u64()
                            }
                            _ => false,
                        }
                    });
                }
            }
        }
        if analyzer.ok {
            result.push(func.address);
        }
    }
    result
}

/// State has to be right before call ins
fn find_name_arg<'e, E: ExecutionState<'e>>(
    arg_cache: &ArgCache<'e, E>,
    state: &mut E,
    arg: Arg,
    interner: &mut InternMap,
) -> Option<Arg> {
    (0..10).filter_map(|i| {
        let resolved = state.resolve(&arg_cache.on_call(i), interner);
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

pub fn open_file<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Vec<E::VirtualAddress> {
    let binary = analysis.binary;
    let str_refs = crate::string_refs(binary, analysis, b"arr\\units.");

    let mut load_dat_fns = str_refs.iter().flat_map(|str_ref| {
        let func = str_ref.func_entry;
        let result = find_load_dat_fn(analysis, func, str_ref.string_address);
        result.into_iter().map(|x| x.1)
    }).collect::<Vec<_>>();
    if load_dat_fns.is_empty() {
        return Vec::new();
    }
    load_dat_fns.sort();
    load_dat_fns.dedup();
    let open_file_fns = load_dat_fns.iter().flat_map(|&addr| {
        find_open_file_fn(analysis, binary, addr)
    }).collect::<Vec<_>>();
    open_file_fns
}
