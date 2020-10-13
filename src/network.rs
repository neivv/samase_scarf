use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{MemAccessSize, Operand, Operation, BinarySection, BinaryFile};

use crate::{AnalysisCtx, ArgCache, single_result_assign, find_bytes};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnpDefinitions<'e> {
    pub snp_definitions: Operand<'e>,
    pub entry_size: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InitStormNetworking<Va: VirtualAddress> {
    pub init_storm_networking: Option<Va>,
    pub load_snp_list: Option<Va>,
}

#[derive(Copy, Clone, Debug)]
pub struct SnetHandlePackets<Va: VirtualAddress> {
    pub send_packets: Option<Va>,
    pub recv_packets: Option<Va>,
}

pub(crate) fn snp_definitions<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<SnpDefinitions<'e>> {
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

pub(crate) fn init_storm_networking<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> InitStormNetworking<E::VirtualAddress> {
    let mut result = InitStormNetworking {
        init_storm_networking: None,
        load_snp_list: None,
    };

    // Init function of AVSelectConnectionScreen calls init_storm_networking,
    // init_storm_networking calls load_snp_list(&[fnptr, fnptr], 1)
    let vtables = crate::vtables::vtables(analysis, b".?AVSelectConnectionScreen@glues@@\0");
    let binary = analysis.binary;
    let text = binary.section(b".text\0\0\0").unwrap();
    let ctx = analysis.ctx;
    let arg_cache = analysis.arg_cache;
    for vtable in vtables {
        let func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let mut analyzer = FindInitStormNetworking::<E> {
            result: &mut result,
            inlining: false,
            text,
            binary,
            arg_cache,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if result.init_storm_networking.is_some() {
            break;
        }
    }
    result
}

struct FindInitStormNetworking<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitStormNetworking<E::VirtualAddress>,
    inlining: bool,
    text: &'a BinarySection<E::VirtualAddress>,
    binary: &'a BinaryFile<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindInitStormNetworking<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.init_storm_networking.is_some() {
                            self.result.init_storm_networking = Some(dest);
                            ctrl.end_analysis();
                        }
                        self.inlining = false;
                    }
                } else {
                    let arg1 = self.arg_cache.on_call(0);
                    let arg2 = ctrl.resolve(self.arg_cache.on_call(1)).if_constant();
                    let text_start = self.text.virtual_address;
                    let text_end = self.text.virtual_address + self.text.virtual_size;
                    let binary = self.binary;
                    let arg1_1;
                    let arg1_2;
                    if arg2 == Some(1) {
                        arg1_1 = ctrl.resolve(ctrl.mem_word(arg1));
                        arg1_2 = ctrl.resolve(
                            ctrl.mem_word(ctrl.const_word_offset(arg1, 1))
                        );
                    } else if arg2 == Some(2) {
                        // Older versions have array size 2 and a second fnptr pair
                        arg1_1 = ctrl.resolve(
                            ctrl.mem_word(ctrl.const_word_offset(arg1, 2))
                        );
                        arg1_2 = ctrl.resolve(
                            ctrl.mem_word(ctrl.const_word_offset(arg1, 3))
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
                        self.result.init_storm_networking = Some(E::VirtualAddress::from_u64(0));
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            self.result.load_snp_list = Some(E::VirtualAddress::from_u64(dest));
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn snet_handle_packets<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> SnetHandlePackets<E::VirtualAddress> {
    let mut result = SnetHandlePackets {
        send_packets: None,
        recv_packets: None,
    };
    // Look for snet functions in packet received handler of UdpServer (vtable fn #3)
    // First one - receive - immediately calls a function pointer to receive the packets,
    // send calls a send_packet function for a ping (?) - send_packet(_, 0, 4, _, 4)
    let vtables = crate::vtables::vtables(analysis, b".?AVUdpServer@");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = analysis.arg_cache;
    for root_inline_limit in 0..2 {
        for &vtable in &vtables {
            let func = match binary.read_address(vtable + 0x3 * E::VirtualAddress::SIZE) {
                Ok(o) => o,
                Err(_) => continue,
            };
            let mut analyzer = SnetHandlePacketsAnalyzer::<E> {
                result: &mut result,
                root_inline_limit,
                checking_candidate: false,
                inlining_entry: E::VirtualAddress::from_u64(0),
                arg_cache,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, func);
            analysis.analyze(&mut analyzer);
            if result.recv_packets.is_some() {
                break;
            }
        }
    }
    result
}

struct SnetHandlePacketsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SnetHandlePackets<E::VirtualAddress>,
    checking_candidate: bool,
    // How much should try inilining before checking for candidate.
    // Do first with no inlining, then with one level of inlining.
    root_inline_limit: u8,
    inlining_entry: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SnetHandlePacketsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let searching_for_recv = self.result.recv_packets.is_none();
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if !self.checking_candidate {
                    if let Some(dest) = dest.if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining_entry = dest;
                        if self.root_inline_limit == 0 {
                            self.checking_candidate = true;
                        } else {
                            self.root_inline_limit -= 1;
                        }
                        ctrl.analyze_with_current_state(self, dest);
                        if self.checking_candidate {
                            self.checking_candidate = false;
                        } else {
                            self.root_inline_limit += 1;
                        }
                        if self.result.send_packets.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    let arg_cache = self.arg_cache;
                    if searching_for_recv {
                        let ok = Some(())
                            .filter(|_| dest.if_memory().is_some())
                            .filter(|_| {
                                // All arguments are out arguments initialized to 0
                                (0..3).all(|i| {
                                    Some(())
                                        .map(|_| ctrl.resolve(arg_cache.on_call(i)))
                                        .map(|x| ctrl.read_memory(x, MemAccessSize::Mem32))
                                        .filter(|x| x.if_constant() == Some(0))
                                        .is_some()
                                })
                            })
                            .is_some();
                        if ok {
                            self.result.recv_packets = Some(self.inlining_entry);
                        }
                        // End even if it isn't recv_packets, the [snp_functions + x] call
                        // should be first.
                        ctrl.end_analysis();
                    } else {
                        let mut ok = Some(())
                            .map(|_| ctrl.resolve(arg_cache.on_call(1)))
                            .filter(|x| x.if_constant() == Some(0))
                            .map(|_| ctrl.resolve(arg_cache.on_call(2)))
                            .filter(|x| x.if_constant() == Some(4))
                            .map(|_| ctrl.resolve(arg_cache.on_call(4)))
                            .filter(|x| x.if_constant() == Some(4))
                            .is_some();
                        if !ok {
                            // Alt: data and length are 0
                            ok = (1..5)
                                .all(|i| {
                                    let expected = if i == 2 { 4 } else { 0 };
                                    Some(())
                                        .map(|_| ctrl.resolve(arg_cache.on_call(i)))
                                        .filter(|x| x.if_constant() == Some(expected))
                                        .is_some()
                                });
                        }
                        if ok {
                            self.result.send_packets = Some(self.inlining_entry);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}
