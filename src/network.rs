use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand, Operation, BinarySection, BinaryFile};

use crate::{Analysis, ArgCache, single_result_assign, find_bytes};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnpDefinitions {
    pub snp_definitions: Rc<Operand>,
    pub entry_size: u32,
}

pub fn snp_definitions<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<SnpDefinitions> {
    // Search for BNAU code.
    // The data is expected to be
    // SnpDefinition { u32 code, char *string_key, char *string_key, Caps *caps, Functions funcs }
    // Functions { u32 size_bytes, func *funcs[..] } (Functions are global constructor inited
    // though, so they're not in static data)
    // BNAU should be followed by UDPA
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let data = binary.section(b".data\0\0\0").unwrap();
    let results = find_bytes(&data.data, &[0x55, 0x41, 0x4e, 0x42]);
    let mut result = None;
    for rva in results {
        let address = data.virtual_address + rva.0;
        let entry_size = (0x10..0x100).find(|i| {
            match binary.read_u32(address + i * 4) {
                Ok(o) => o == 0x55445041,
                Err(_) => false,
            }
        }).map(|x| x * 4);
        if let Some(entry_size) = entry_size {
            let new = SnpDefinitions {
                snp_definitions: ctx.constant(address.as_u64()),
                entry_size,
            };
            if single_result_assign(Some(new), &mut result) {
                break;
            }
        }
    }
    result
}

pub fn init_storm_networking<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    // Init function of AVSelectConnectionScreen calls init_storm_networking,
    // init_storm_networking calls load_snp_list(&[fnptr, fnptr], 1)
    let vtables = crate::vtables::vtables(analysis, b".?AVSelectConnectionScreen@glues@@\0");
    let binary = analysis.binary;
    let text = binary.section(b".text\0\0\0").unwrap();
    let ctx = analysis.ctx;
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    for vtable in vtables {
        let func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let mut analyzer = FindInitStormNetworking::<E> {
            result: None,
            inlining: false,
            text,
            binary,
            arg_cache,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    result
}

struct FindInitStormNetworking<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    inlining: bool,
    text: &'a BinarySection<E::VirtualAddress>,
    binary: &'a BinaryFile<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindInitStormNetworking<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.is_some() {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                        }
                        self.inlining = false;
                    }
                } else {
                    let arg1 = &self.arg_cache.on_call(0);
                    let arg2 = ctrl.resolve(&self.arg_cache.on_call(1)).if_constant();
                    let text_start = self.text.virtual_address;
                    let text_end = self.text.virtual_address + self.text.virtual_size;
                    let binary = self.binary;
                    let arg1_1;
                    let arg1_2;
                    if arg2 == Some(1) {
                        arg1_1 = ctrl.resolve(&ctrl.mem_word(arg1.clone()));
                        arg1_2 = ctrl.resolve(
                            &ctrl.mem_word(ctrl.const_word_offset(arg1.clone(), 1))
                        );
                    } else if arg2 == Some(2) {
                        // Older versions have array size 2 and a second fnptr pair
                        arg1_1 = ctrl.resolve(
                            &ctrl.mem_word(ctrl.const_word_offset(arg1.clone(), 2))
                        );
                        arg1_2 = ctrl.resolve(
                            &ctrl.mem_word(ctrl.const_word_offset(arg1.clone(), 3))
                        );
                    } else {
                        return;
                    }
                    let ok = Some(())
                        .and_then(|_| arg1_1.if_mem32()?.if_constant())
                        .and_then(|a| binary.read_address(E::VirtualAddress::from_u64(a)).ok())
                        .filter(|&c| c >= text_start && c < text_end)
                        .and_then(|_| arg1_2.if_mem32()?.if_constant())
                        .and_then(|a| binary.read_address(E::VirtualAddress::from_u64(a)).ok())
                        .filter(|&c| c >= text_start && c < text_end)
                        .is_some();
                    if ok {
                        self.result = Some(E::VirtualAddress::from_u64(0));
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
