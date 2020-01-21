use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Operand, Operation};

use crate::{
    ArgCache, Analysis, EntryOf, StringRefs, entry_of_until, single_result_assign, string_refs,
    if_callable_const,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DatTablePtr {
    pub address: Rc<Operand>,
    pub entry_size: u32,
}

pub fn dat_table<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    filename: &'static str,
) -> Option<DatTablePtr> {
    let binary = analysis.binary;
    let functions = analysis.functions();
    let str_refs = string_refs(binary, analysis, filename.as_bytes());

    let mut result = None;
    'outer: for str_ref in &str_refs {
        let addr = entry_of_until(binary, &functions, str_ref.use_address, |entry| {
            find_dat_root(analysis, entry, str_ref)
        }).into_option();
        if let Some(addr) = addr {
            // Check distance between 2 pointers.
            // TODO Could check that they must be relocs?
            if let Ok(first) = binary.read_address(addr) {
                if first.as_u64() > 0x10000 {
                    let size = (1..10).filter_map(|offset| {
                        match binary.read_address(addr + offset * 4) {
                            Ok(x) if x.as_u64() > 0x10000 => Some(offset * 4),
                            _ => None,
                        }
                    }).next();
                    if let Some(size) = size {
                        let val = DatTablePtr {
                            address: analysis.ctx.constant(addr.as_u64()),
                            entry_size: size,
                        };
                        if single_result_assign(Some(val), &mut result) {
                            break 'outer;
                        }
                    }
                }
            }
        }
    }
    result
}

fn find_dat_root<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    parent: E::VirtualAddress,
    str_ref: &StringRefs<E::VirtualAddress>,
) -> EntryOf<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, parent);
    let mut analyzer = FindDatRoot {
        str_ref,
        addr_found: false,
        result: None,
        arg_cache,
        binary,
    };
    analysis.analyze(&mut analyzer);
    if let Some(result) = analyzer.result {
        EntryOf::Ok(result)
    } else if analyzer.addr_found {
        EntryOf::Stop
    } else {
        EntryOf::Retry
    }
}

struct FindDatRoot<'a, 'e, E: ExecutionState<'e>> {
    str_ref: &'a StringRefs<E::VirtualAddress>,
    addr_found: bool,
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindDatRoot<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        if ctrl.address() == self.str_ref.use_address {
            self.addr_found = true;
        }
        if let Operation::Call(dest) = op {
            let (state, interner) = ctrl.exec_state();
            let dest = if_callable_const(self.binary, state, dest, interner);
            let arg1 = ctrl.resolve(&self.arg_cache.on_call(0)).if_constant();
            let arg2 = ctrl.resolve(&self.arg_cache.on_call(1)).if_constant();
            if let (Some(_dest), Some(arg1), Some(arg2)) = (dest, arg1, arg2) {
                if arg1 == self.str_ref.string_address.as_u64() {
                    self.result = Some(E::VirtualAddress::from_u64(arg2));
                    ctrl.end_analysis();
                }
            }
        }
    }
}
