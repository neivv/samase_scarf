use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{MemAccessSize, Operand, OperandCtx, Operation, BinarySection, BinaryFile};

use crate::{AnalysisCtx, ArgCache, single_result_assign, find_bytes, FunctionFinder, EntryOf, OptionExt, OperandExt, entry_of_until, if_arithmetic_eq_neq, VirtualAddressTrait};
use crate::add_terms::collect_arith_add_terms;
use crate::vtables::Vtables;

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
    analysis: &AnalysisCtx<'e, E>,
) -> Option<SnpDefinitions<'e>> {
    // Search for BNAU code.
    // The data is expected to be
    // SnpDefinition { u32 code, char *string_key, char *string_key, Caps *caps, Functions funcs }
    // Functions { u32 size_bytes, func *funcs[..] } (Functions are global constructor inited
    // though, so they're not in static data)
    // BNAU should be followed by UDPA
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let data = analysis.binary_sections.data;
    let results = find_bytes(bump, &data.data, &[0x55, 0x41, 0x4e, 0x42]);
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
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> InitStormNetworking<E::VirtualAddress> {
    let mut result = InitStormNetworking {
        init_storm_networking: None,
        load_snp_list: None,
    };

    // Init function of AVSelectConnectionScreen calls init_storm_networking,
    // init_storm_networking calls load_snp_list(&[fnptr, fnptr], 1)
    let vtables = vtables.vtables_starting_with(b".?AVSelectConnectionScreen@glues@@\0")
        .map(|x| x.address);
    let binary = analysis.binary;
    let text = analysis.binary_sections.text;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;
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
                    let word_size = u64::from(E::VirtualAddress::SIZE);
                    if arg2 == Some(1) {
                        arg1_1 = ctrl.resolve(ctrl.mem_word(arg1, 0));
                        arg1_2 = ctrl.resolve(ctrl.mem_word(arg1, word_size));
                    } else if arg2 == Some(2) {
                        // Older versions have array size 2 and a second fnptr pair
                        arg1_1 = ctrl.resolve(ctrl.mem_word(arg1, 2 * word_size));
                        arg1_2 = ctrl.resolve(ctrl.mem_word(arg1, 3 * word_size));
                    } else {
                        return;
                    }
                    let ok = Some(())
                        .and_then(|_| ctrl.if_mem_word(arg1_1)?.if_constant_address())
                        .and_then(|a| binary.read_address(E::VirtualAddress::from_u64(a)).ok())
                        .filter(|&c| c >= text_start && c < text_end)
                        .and_then(|_| ctrl.if_mem_word(arg1_2)?.if_constant_address())
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
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> SnetHandlePackets<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = SnetHandlePackets {
        send_packets: None,
        recv_packets: None,
    };
    // Look for snet functions in packet received handler of UdpServer (vtable fn #3)
    // First one - receive - immediately calls a function pointer to receive the packets,
    // send is verified by looking for a comparision (a - Mem32[b + C]) < 0xc350
    let vtables = BumpVec::from_iter_in(
        vtables.vtables_starting_with(b".?AVUdpServer@").map(|x| x.address),
        bump,
    );
    let arg_cache = &analysis.arg_cache;
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
        let ctx = ctrl.ctx();
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
                                        .map(|x| {
                                            let mem = ctx.mem_access(x, 0, MemAccessSize::Mem32);
                                            ctrl.read_memory(&mem)
                                        })
                                        .filter(|&x| x == ctx.const_0())
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
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if !searching_for_recv && self.checking_candidate {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_gt()
                        .filter(|x| x.0.if_constant() == Some(0xc350))
                        .and_then(|x| {
                            let mem = Operand::and_masked(x.1).0
                                .if_arithmetic_sub()?.1
                                .if_mem32()?;
                            let (base, _offset) = mem.address();
                            base.if_memory()?;
                            Some(())
                        })
                        .is_some();
                    if ok {
                        self.result.send_packets = Some(self.inlining_entry);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn start_udp_server<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // Check for a function using "Game Data Port" string,
    // immediately checking this.x18 == 0, 4, 6
    let binary = actx.binary;
    let ctx = actx.ctx;
    let str_refs = functions.string_refs(actx, b"game data port");
    let mut result = None;
    let funcs = functions.functions();
    for string in str_refs {
        let new = entry_of_until(binary, funcs, string.use_address, |entry| {
            let mut analyzer = IsStartUdpServer::<E> {
                result: EntryOf::Retry,
                use_address: string.use_address,
                found: [false; 3],
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();
        if let Some((entry, ())) = new {
            if single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsStartUdpServer<'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    found: [bool; 3],
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStartUdpServer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        /// Matches val = Mem32[ecx + C]
        fn is_this_mem32<'e>(val: Operand<'e>, ctx: OperandCtx<'e>) -> bool {
            val.if_mem32()
                .filter(|x| x.address().0 == ctx.register(1))
                .is_some()
        }

        let address = ctrl.address();
        if self.use_address >= address && self.use_address < ctrl.current_instruction_end() {
            self.result = EntryOf::Stop;
            ctrl.end_branch(); // Branch using "Game Data Port" isn't needed
        }
        if let Operation::Jump { condition, .. } = *op {
            let condition = ctrl.resolve(condition);
            let ctx = ctrl.ctx();
            let ok = if_arithmetic_eq_neq(condition)
                .map(|x| (x.0, x.1))
                .and_either(|x| match x.if_constant() {
                    Some(0) => Some(0),
                    Some(4) => Some(1),
                    Some(6) => Some(2),
                    _ => None,
                })
                .filter(|&(_, other)| is_this_mem32(other, ctx))
                .map(|x| x.0);
            if let Some(index) = ok {
                self.found[index] = true;
                if self.found == [true; 3] {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            } else {
                // Also check for val & ffff_fff9 == 0, which matches
                // 0/2/4/6 (It would then check != 2 later)
                let all_ok = if_arithmetic_eq_neq(condition)
                    .filter(|x| x.1 == ctx.const_0())
                    .and_then(|x| x.0.if_arithmetic_and_const(0xffff_fff9))
                    .filter(|&x| is_this_mem32(x, ctx))
                    .is_some();
                if all_ok {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct NetFormatTurnRate<'e, Va: VirtualAddressTrait> {
    pub net_format_turn_rate: Option<Va>,
    pub net_user_latency: Option<Operand<'e>>,
}

pub(crate) fn anaylze_net_format_turn_rate<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> NetFormatTurnRate<'e, E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let str_refs = functions.string_refs(actx, b"bnet_latency_low");
    let mut result = None;
    let funcs = functions.functions();

    for string in str_refs {
        let val = entry_of_until(binary, funcs, string.use_address, |entry| {

            let mut analyzer = IsNetUserLatency::<E> {
                result: EntryOf::Retry,
                inlining: false,
                bump: &actx.bump,
                phantom: Default::default(),
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();

        if single_result_assign(val, &mut result) {
          break;
        }
    }

    result.map_or(NetFormatTurnRate {
        net_format_turn_rate: None,
        net_user_latency: None,
    }, |r| NetFormatTurnRate {
        net_format_turn_rate: Some(r.0),
        net_user_latency: Some(r.1)
    })
}

struct IsNetUserLatency<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    inlining: bool,
    bump: &'a bumpalo::Bump,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsNetUserLatency<'a, 'e, E> {
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if !self.inlining {
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    if let Some(dest) = dest.if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        ctrl.skip_operation();
                        self.inlining = false;


                    }
                },
                Operation::Move(_, val, _) => {
                    if let Some(mem) = ctrl.if_mem_word(val) {
                        let (mem_base, _) = mem.address();
                        // Looking for e.g. mov eax, [string_table + net_user_latency*4]
                        let mut terms = collect_arith_add_terms(mem_base, self.bump);
                        let term = terms.remove_get(|x, is_sub| {
                            !is_sub &&
                                x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()).is_some()
                        });
                        if let Some(term) = term {
                            let result =
                                term.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                                    .and_then(|x| Some(ctrl.resolve(x).unwrap_sext()));

                            if let Some(result) = result {
                                self.result = EntryOf::Ok(result);
                                ctrl.end_analysis();
                            }
                    }
                }
                },
                _ => (),
            }
        } else {
            // We're only looking for a very small function, so if we find go anywhere else, end
            // analysis
            match *op {
                Operation::Call(_) | Operation::Jump { .. } => {
                    ctrl.end_analysis()
                }
                _ => {}
            }
        }
    }
}
