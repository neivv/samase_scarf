use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, MemAccessSize, Operand, OperandCtx, Operation, BinarySection, BinaryFile};

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{FunctionFinder, find_bytes, entry_of_until, EntryOf};
use crate::add_terms::collect_arith_add_terms;
use crate::call_tracker::{CallTracker};
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, OperandExt, OptionExt, single_result_assign, if_arithmetic_eq_neq,
    MemAccessExt,
};
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

#[derive(Copy, Clone, Debug)]
pub struct StepLobbyNetwork<Va: VirtualAddress> {
    pub step_lobby_network: Option<Va>,
    pub send_queued_lobby_commands: Option<Va>,
}

#[derive(Copy, Clone, Debug)]
pub struct StepLobbyState<Va: VirtualAddress> {
    pub process_async_lobby_command: Option<Va>,
    pub command_lobby_map_p2p: Option<Va>,
}

pub struct SnetRecvPackets<'e> {
    pub snet_local_player_list: Option<Operand<'e>>,
    pub snet_player_list: Option<Operand<'e>>,
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
    functions: &FunctionFinder<'_, 'e, E>,
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
    let bump = &analysis.bump;
    let funcs = functions.functions();
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
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if result.init_storm_networking.is_some() {
            break;
        }
    }
    if result.init_storm_networking.is_none() {
        // Fallback: The same function should also refer to string SetGatewayText
        let rdata = analysis.binary_sections.rdata;
        let results = find_bytes(bump, &rdata.data, b"SetGatewayText\0");
        'outer: for rva in results {
            let address = rdata.virtual_address + rva.0;
            let global_refs = functions.find_functions_using_global(analysis, address);
            for global_ref in global_refs {
                entry_of_until(binary, &funcs, global_ref.use_address, |entry| {
                    let mut analyzer = FindInitStormNetworking::<E> {
                        result: &mut result,
                        inlining: false,
                        text,
                        binary,
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    if result.init_storm_networking.is_some() {
                        EntryOf::Ok(())
                    } else {
                        EntryOf::Retry
                    }
                });
                if result.init_storm_networking.is_some() {
                    break 'outer;
                }
            }
        }
    }
    result
}

struct FindInitStormNetworking<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitStormNetworking<E::VirtualAddress>,
    inlining: bool,
    text: &'a BinarySection<E::VirtualAddress>,
    binary: &'a BinaryFile<E::VirtualAddress>,
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
                    let arg1 = ctrl.resolve_arg(0);
                    let arg2 = ctrl.resolve_arg(1).if_constant();
                    let text_start = self.text.virtual_address;
                    let text_end = self.text.virtual_address + self.text.virtual_size;
                    let binary = self.binary;

                    let word_size = u64::from(E::VirtualAddress::SIZE);
                    let ctx = ctrl.ctx();
                    let mem = if arg2 == Some(1) {
                        ctx.mem_access(arg1, 0, E::WORD_SIZE)
                    } else if arg2 == Some(2) {
                        // Older versions have array size 2 and a second fnptr pair
                        ctx.mem_access(arg1, word_size * 2, E::WORD_SIZE)
                    } else {
                        return;
                    };
                    let arg1_1 = ctrl.read_memory(&mem);
                    let arg1_2 = ctrl.read_memory(&mem.with_offset(word_size));

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
    // send is verified by looking for a comparision (a - Mem32[b + C]) < 0xc350,
    // and by then also verifying that it checks bit 4 on the packet flags
    let vtables = BumpVec::from_iter_in(
        vtables.vtables_starting_with(b".?AVUdpServer@").map(|x| x.address),
        bump,
    );
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
                verify_recv_packets: false,
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
    verify_recv_packets: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SnetHandlePacketsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let searching_for_recv = self.result.recv_packets.is_none();
        let ctx = ctrl.ctx();
        if self.verify_recv_packets {
            match *op {
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    if condition.if_and_mask_eq_neq(0x4).is_some() {
                        self.result.recv_packets = Some(self.inlining_entry);
                        ctrl.end_analysis();
                    }
                }
                _ => (),
            }
        } else {
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
                            self.verify_recv_packets = false;
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
                        if searching_for_recv {
                            let ok = Some(())
                                .filter(|_| dest.if_memory().is_some())
                                .filter(|_| {
                                    // All arguments are out arguments initialized to 0
                                    (0..3).all(|i| {
                                        Some(())
                                            .map(|_| ctrl.resolve_arg(i))
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
                                // Write results that the func won't return
                                let a1 = ctrl.resolve_arg(0);
                                let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                                ctrl.write_memory(&a1_mem, ctx.custom(0));

                                let a2 = ctrl.resolve_arg(1);
                                let a2_mem = ctx.mem_access(a2, 0, E::WORD_SIZE);
                                ctrl.write_memory(&a2_mem, ctx.custom(1));

                                ctrl.do_call_with_result(ctx.const_1());
                                self.verify_recv_packets = true;
                            } else {
                                // End even if it isn't recv_packets, the [snp_functions + x] call
                                // should be first.
                                ctrl.end_analysis();
                            }
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
        let new = entry_of_until(binary, &funcs, string.use_address, |entry| {
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
pub struct NetFormatTurnRate<'e, Va: VirtualAddress> {
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
        let val = entry_of_until(binary, &funcs, string.use_address, |entry| {

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
                Operation::Move(_, val) => {
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

// net_player_count() @ SC:R: `int __cdecl`, no args. Counts the active networked players in the
// Storm session (local player included) via storm_get_session_player_range(&min,&max,&count),
// stores the count as a byte into game+0xf1, and returns byte[game+0xf1]. A peerless session
// yields 1; BW's minimap dialog / MP-button code classifies a game as multiplayer with
// `is_multiplayer != 0 && net_player_count() > 1`. Anchored on the error string
// "strERROR_GENERAL_NETWORK" it references on the Storm failure path (a bounded candidate set).
// game+0xf1 also gets written by the (unrelated, much larger) player-leave handler as a side
// effect, so a bare write match isn't unique; discriminate on shape instead: this is the only
// candidate whose containing function writes to game+0xf1 and to *no other* global memory
// location at all. game+0xf1 is width-stable.
pub(crate) fn net_player_count<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    game: Operand<'e>,
) -> Option<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let funcs = functions.functions();
    let str_refs = functions.string_refs(actx, b"strERROR_GENERAL_NETWORK");
    let mut result = None;
    for str_ref in &str_refs {
        let val = entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = FindNetPlayerCount::<E> {
                game,
                game_field_write: false,
                other_global_write: false,
                phantom: Default::default(),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if analyzer.game_field_write {
                if analyzer.other_global_write {
                    // Reached the right function for this string ref, but it isn't the
                    // one we want (e.g. the player-leave handler) -- no need to keep
                    // walking further back for an earlier entry candidate.
                    EntryOf::Stop
                } else {
                    EntryOf::Ok(())
                }
            } else {
                EntryOf::Retry
            }
        }).into_option_with_entry().map(|x| x.0);
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

struct FindNetPlayerCount<'e, E: ExecutionState<'e>> {
    game: Operand<'e>,
    // Set once a `Mem8[game + 0xf1] = _` store is seen.
    game_field_write: bool,
    // Set if the function stores to any *other* global memory location. net_player_count's
    // real body only ever touches game+0xf1; the player-leave handler that also happens to
    // write game+0xf1 touches many other globals (storm_command_user, per-player state, ...),
    // so this tells the two apart.
    other_global_write: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindNetPlayerCount<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Move(DestOperand::Memory(ref mem), _) = *op {
            let resolved = ctrl.resolve_mem(mem);
            if resolved.is_global() {
                let (base, offset) = resolved.address();
                if offset == 0xf1 && base == self.game {
                    self.game_field_write = true;
                } else {
                    self.other_global_write = true;
                }
                // Once both are set the verdict is locked to EntryOf::Stop (game+0xf1 plus
                // another global rules out net_player_count, which writes only game+0xf1), so
                // stop walking early -- this cuts short the large player-leave handler. Non-
                // matching candidates must still return Retry (not Stop) via the full walk, so
                // entry_of_until keeps iterating toward net_player_count's own entry; only this
                // provably-terminal case may bail.
                if self.game_field_write && self.other_global_write {
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) fn step_lobby_network<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_network: E::VirtualAddress,
    send_command: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> StepLobbyNetwork<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = StepLobbyNetwork {
        step_lobby_network: None,
        send_queued_lobby_commands: None,
    };

    let callers = functions.find_callers(actx, step_network);
    let funcs = functions.functions();
    for caller in callers {
        let new = entry_of_until(binary, &funcs, caller, |entry| {
            let mut analyzer = StepLobbyNetworkAnalyzer::<E> {
                result: &mut result,
                entry_of: EntryOf::Retry,
                inline_limit: 0,
                step_network,
                send_command,
                state: StepLobbyNetworkState::StepNetwork,
                true_state: None,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);

        if single_result_assign(new, &mut result.step_lobby_network) {
            break;
        }
    }

    result
}

struct StepLobbyNetworkAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    result: &'a mut StepLobbyNetwork<E::VirtualAddress>,
    inline_limit: u8,
    step_network: E::VirtualAddress,
    send_command: E::VirtualAddress,
    state: StepLobbyNetworkState,
    true_state: Option<(E, analysis::DefaultState, E::VirtualAddress)>,
}

enum StepLobbyNetworkState {
    /// Find step_network call, and jump based on its return value
    StepNetwork,
    /// False branch should have comparison of GetTickCount() - global, 0x4e20
    StepNetworkFalse,
    /// True branch should call send_queued_lobby_commands
    StepNetworkTrue,
    /// Should have send_command(global, 1) call early in the function
    SendQueuedVerify,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepLobbyNetworkAnalyzer<'a, 'e, E>
{
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepLobbyNetworkState::StepNetwork => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.step_network {
                            self.entry_of = EntryOf::Stop;
                            ctrl.do_call_with_result(ctx.custom(0));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((other, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if other.unwrap_and_mask().if_custom() == Some(0) {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.true_state = ctrl.state_for_neq_address(eq, to);
                            self.state = StepLobbyNetworkState::StepNetworkFalse;
                        }
                    }
                }
            }
            StepLobbyNetworkState::StepNetworkFalse => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_gt()
                        .is_some_and(|x| x.0.if_constant() == Some(0x4e20));
                    if ok {
                        self.entry_of = EntryOf::Ok(());
                        if let Some(state) = self.true_state.take() {
                            ctrl.continue_with_state(state);
                            self.state = StepLobbyNetworkState::StepNetworkTrue;
                        }
                    }
                }
            }
            StepLobbyNetworkState::StepNetworkTrue => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_limit = 6;
                        self.state = StepLobbyNetworkState::SendQueuedVerify;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.send_queued_lobby_commands.is_some() {
                            self.result.send_queued_lobby_commands = Some(dest);
                            ctrl.end_analysis();
                        } else {
                            self.state = StepLobbyNetworkState::StepNetworkTrue;
                        }
                    }
                }
            }
            StepLobbyNetworkState::SendQueuedVerify => {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                    _ => (),
                }
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.send_command {
                            let arg2 = ctrl.resolve_arg_u32(1);
                            if arg2 == ctx.const_1() {
                                self.result.send_queued_lobby_commands =
                                    Some(E::VirtualAddress::from_u64(0));
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn step_lobby_state<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_lobby_network: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> StepLobbyState<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = StepLobbyState {
        process_async_lobby_command: None,
        command_lobby_map_p2p: None,
    };

    let callers = functions.find_callers(actx, step_lobby_network);
    let funcs = functions.functions();
    for caller in callers {
        // Can match two different functions that both work for async command
        entry_of_until(binary, &funcs, caller, |entry| {
            let mut analyzer = StepLobbyStateAnalyzer::<E> {
                result: &mut result,
                entry_of: EntryOf::Retry,
                inline_limit: 0,
                step_lobby_network,
                state: StepLobbyStateState::StepLobbyNetwork,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });

        if result.process_async_lobby_command.is_some() {
            break;
        }
    }

    result
}

struct StepLobbyStateAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    result: &'a mut StepLobbyState<E::VirtualAddress>,
    inline_limit: u8,
    step_lobby_network: E::VirtualAddress,
    state: StepLobbyStateState,
}

enum StepLobbyStateState {
    /// Find step_lobby_network call, and jump based on its return value
    StepLobbyNetwork,
    /// Should be next call / tail call on 0 branch
    FindAsyncCommands,
    /// Should have a switch
    VerifyAsyncCommands,
    /// On branch 0x4f, should have a call to lobby_command_map_p2p
    MapP2pPacket,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StepLobbyStateAnalyzer<'a, 'e, E> {
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepLobbyStateState::StepLobbyNetwork => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.step_lobby_network {
                            self.entry_of = EntryOf::Stop;
                            ctrl.do_call_with_result(ctx.custom(0));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((other, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if other.unwrap_and_mask().if_custom() == Some(0) {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.state = StepLobbyStateState::FindAsyncCommands;
                        }
                    }
                }
            }
            StepLobbyStateState::FindAsyncCommands => {
                let dest = match *op {
                    Operation::Call(dest) => dest,
                    Operation::Jump { condition, to } => {
                        if condition == ctx.const_1() &&
                            ctrl.resolve_register(4) == ctx.register(4)
                        {
                            to
                        } else {
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    _ => return,
                };
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.inline_limit = 8;
                    self.state = StepLobbyStateState::VerifyAsyncCommands;
                    // This doesn't do stack correctly for tail call but there are no
                    // arguments so it's fine..
                    ctrl.analyze_with_current_state(self, dest);
                    if self.result.process_async_lobby_command.is_some() {
                        self.result.process_async_lobby_command = Some(dest);
                    }
                }
                ctrl.end_analysis();
            }
            StepLobbyStateState::VerifyAsyncCommands => {
                match *op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                    _ => (),
                }
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() && to.if_constant().is_none() {
                        let to = ctrl.resolve(to);
                        let exec_state = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec_state) {
                            self.result.process_async_lobby_command =
                                Some(E::VirtualAddress::from_u64(0));
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x4f) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = StepLobbyStateState::MapP2pPacket;
                            }
                        }
                    }
                }
            }
            StepLobbyStateState::MapP2pPacket => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg(0);
                        let a2 = ctrl.resolve_arg(1);
                        let ok = a2.if_mem16().is_some_and(|mem| {
                            mem.with_offset(2) == ctx.mem_access(a1, 0, MemAccessSize::Mem16)
                        });
                        if ok {
                            self.result.command_lobby_map_p2p = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

// apply_lobby_force_cmd is the handler for async lobby command class 0x4A (the per-slot
// force/alliance/vision apply). Its only caller is the async lobby command dispatcher
// (process_async_lobby_command), which switches on (class_byte - 0x3A) through a byte lookup
// table into a dword jump table. The 0x4A case checks the record length == 0x3F (== 63, the
// serialized body size) and then directly calls apply_lobby_force_cmd(record, guard). We locate
// the dispatcher's switch the same way command_lobby_map_p2p does for class 0x4F, branch to the
// 0x4A case, steer onto the length == 0x3F branch to confirm the case, and take the following
// call. The switch-case shape and the 0x3F length check survive recompiles even though the raw
// addresses and the record layout do not.
pub(crate) fn apply_lobby_force_cmd<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    process_async_lobby_command: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = None;
    let mut analyzer = ApplyLobbyForceCmd::<E> {
        result: &mut result,
        state: ApplyLobbyForceCmdState::FindSwitch,
        limit: 0,
    };
    FuncAnalysis::new(binary, ctx, process_async_lobby_command).analyze(&mut analyzer);
    result
}

struct ApplyLobbyForceCmd<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut Option<E::VirtualAddress>,
    state: ApplyLobbyForceCmdState,
    limit: u8,
}

#[derive(Eq, PartialEq, Copy, Clone)]
enum ApplyLobbyForceCmdState {
    /// Find the dispatcher switch jump, branch to the 0x4A case.
    FindSwitch,
    /// In the 0x4A case, steer onto the record-length == 0x3F branch.
    FindLenCheck,
    /// The next resolved call is apply_lobby_force_cmd.
    FindCall,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for ApplyLobbyForceCmd<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            ApplyLobbyForceCmdState::FindSwitch => {
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() && to.if_constant().is_none() {
                        let to = ctrl.resolve(to);
                        let exec_state = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec_state) {
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x4a) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = ApplyLobbyForceCmdState::FindLenCheck;
                                self.limit = 8;
                            }
                        }
                    }
                }
            }
            ApplyLobbyForceCmdState::FindLenCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((l, r, is_eq)) = condition.if_arithmetic_eq_neq() {
                        if l.if_constant() == Some(0x3f) || r.if_constant() == Some(0x3f) {
                            // Continue on the record-length == 0x3F side; the apply call follows.
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(is_eq, to);
                            self.state = ApplyLobbyForceCmdState::FindCall;
                            self.limit = 8;
                            return;
                        }
                    }
                    if self.limit == 0 {
                        ctrl.end_analysis();
                    } else {
                        self.limit -= 1;
                    }
                }
            }
            ApplyLobbyForceCmdState::FindCall => {
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            *self.result = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                    Operation::Jump { .. } => {
                        if self.limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.limit -= 1;
                        }
                    }
                    _ => (),
                }
            }
        }
    }
}

pub(crate) fn analyze_snet_recv_packets<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    snet_recv_packets: E::VirtualAddress,
) -> SnetRecvPackets<'e> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = SnetRecvPackets {
        snet_local_player_list: None,
        snet_player_list: None,
    };

    let mut analyzer = SnetRecvAnalyzer::<E> {
        result: &mut result,
        state: SnetRecvState::Init,
        call_tracker: CallTracker::with_capacity(actx, 0x1000, 0x8),
        inline_depth: 0,
        ctx,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, snet_recv_packets);
    analysis.analyze(&mut analyzer);

    result
}

struct SnetRecvAnalyzer<'acx, 'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SnetRecvPackets<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
    state: SnetRecvState,
    inline_depth: u8,
    ctx: OperandCtx<'e>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SnetRecvState {
    /// Find call to fnptr(&mut sockaddr_in, ..), write Custom(0) to that ptr (sockaddr)
    /// and Custom(1) to arg 2 (data)
    Init,
    /// Find jump on packet.flags & 4, follow zero branch
    PacketFlags4,
    /// Inline once to find_snet_player_by_sockaddr(*a1 = Custom(0)),
    /// then find check of bit1 of list.next
    PlayerList,
    /// Find jump on a func return value from before being nonnull, then use same
    /// logic as in PlayerList. If the func was inlined then the list got already set in
    /// PacketFlags4 state.
    LocalPlayerList,
    /// Same as PlayerList
    LocalPlayerListGetFn,
}

impl<'acx, 'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SnetRecvAnalyzer<'acx, 'a, 'e, E>
{
    type Exec = E;
    type State = analysis::DefaultState;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            SnetRecvState::Init => {
                if let Operation::Call(dest) = *op {
                    let dest = ctrl.resolve(dest);
                    if ctrl.if_mem_word(dest).is_some() {
                        let a1 = ctrl.resolve_arg(0);
                        let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                        ctrl.write_memory(&a1_mem, ctx.custom(0));

                        let a2 = ctrl.resolve_arg(1);
                        let a2_mem = ctx.mem_access(a2, 0, E::WORD_SIZE);
                        ctrl.write_memory(&a2_mem, ctx.custom(1));

                        ctrl.do_call_with_result(ctx.const_1());
                        self.state = SnetRecvState::PacketFlags4;
                    }
                }
            }
            SnetRecvState::PacketFlags4 => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_and_mask_eq_neq(0x4);
                    if let Some((_, eq_zero)) = result {
                        ctrl.continue_at_eq_address(eq_zero, to);
                        self.state = SnetRecvState::PlayerList;
                    } else if let Some(cand) = self.check_player_list_head_bit1(condition) {
                        self.result.snet_local_player_list = Some(cand);
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            SnetRecvState::PlayerList | SnetRecvState::LocalPlayerListGetFn => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some(result) = self.check_player_list_head_bit1(condition) {
                        if self.state == SnetRecvState::PlayerList {
                            self.result.snet_player_list = Some(result);
                            if self.result.snet_local_player_list.is_some() {
                                // local player list access was inlined, and found in
                                // flag4 check, can stop now
                                ctrl.end_analysis();
                            } else {
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                                self.state = SnetRecvState::LocalPlayerList;
                            }
                        } else {
                            self.result.snet_local_player_list = Some(result);
                            ctrl.end_analysis();
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let a1 = ctrl.resolve_arg(0);
                            let a1_mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                            let a1_mem_value = ctrl.read_memory(&a1_mem);
                            let inline = ctrl.if_mem_word(a1_mem_value)
                                .is_some_and(|x| x.address().0.if_custom() == Some(0));
                            if inline {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.snet_player_list.is_some() &&
                                    self.result.snet_local_player_list.is_some()
                                {
                                    // local player list access was inlined, and found in
                                    // flag4 check, can stop now
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            SnetRecvState::LocalPlayerList => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some(x) = condition.if_arithmetic_eq_neq_zero(ctx) &&
                        let Some(custom) = x.0.unwrap_and_mask().if_custom()
                    {
                        if let Some(addr) = self.call_tracker.custom_id_to_func(custom) {
                            self.state = SnetRecvState::LocalPlayerListGetFn;
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, addr);
                            self.inline_depth -= 1;
                            if self.result.snet_local_player_list.is_some() {
                                ctrl.end_analysis();
                            } else {
                                self.state = SnetRecvState::LocalPlayerList;
                            }
                        }
                    }
                }
            }
        }
    }
}

// find_storm_session_player scans the session-player list for the node whose slot field
// ([node + 0x21a]) equals the requested slot, returning that node or null. storm_receive_turns
// calls it (in several places) passing a slot value. The callee is recognised by a jump whose
// condition compares the +0x21a slot field of a list node against the function's own first
// argument (masked to slot width). Comparing the slot field against the *argument* -- rather than
// against a constant -- is what distinguishes it from sibling scan helpers, and 0x21a is a
// serialized struct field offset that survives recompiles.
pub(crate) fn find_storm_session_player<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    storm_receive_turns: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = FindStormSessionPlayerCaller::<E> {
        result: None,
        checked: BumpVec::new_in(&actx.bump),
        actx,
    };
    FuncAnalysis::new(binary, ctx, storm_receive_turns).analyze(&mut analyzer);
    analyzer.result
}

struct FindStormSessionPlayerCaller<'acx, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    checked: BumpVec<'acx, E::VirtualAddress>,
    actx: &'acx AnalysisCtx<'e, E>,
}

impl<'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    FindStormSessionPlayerCaller<'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if !self.checked.contains(&dest) {
                    self.checked.push(dest);
                    if is_find_storm_session_player(self.actx, dest) {
                        self.result = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

fn is_find_storm_session_player<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> bool {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = IsFindStormSessionPlayer::<E> {
        result: false,
        budget: 0x1000,
        arg1: actx.arg_cache.on_entry(0),
        phantom: Default::default(),
    };
    FuncAnalysis::new(binary, ctx, func).analyze(&mut analyzer);
    analyzer.result
}

struct IsFindStormSessionPlayer<'e, E: ExecutionState<'e>> {
    result: bool,
    budget: u32,
    arg1: Operand<'e>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsFindStormSessionPlayer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.budget == 0 {
            ctrl.end_analysis();
            return;
        }
        self.budget -= 1;
        if let Operation::Jump { condition, .. } = *op {
            let condition = ctrl.resolve(condition);
            if let Some((l, r, _)) = condition.if_arithmetic_eq_neq() {
                let slot_offset = crate::game_init::session_player_slot_offset::<E>();
                // One side reads a node slot field; the other is arg1 (the slot the caller asked
                // for), read from the arg location at whatever width.
                let field = [(l, r), (r, l)].into_iter().find_map(|(field, other)| {
                    let mem = field.if_mem8().or_else(|| field.if_mem16())?;
                    if mem.address().1 != slot_offset {
                        return None;
                    }
                    let same_arg_addr = match (other.if_memory(), self.arg1.if_memory()) {
                        (Some(a), Some(b)) => a.address() == b.address(),
                        _ => false,
                    };
                    let matches = other == self.arg1 ||
                        other.unwrap_and_mask() == self.arg1 ||
                        same_arg_addr;
                    matches.then_some(())
                });
                if field.is_some() {
                    self.result = true;
                    ctrl.end_analysis();
                }
            }
        }
    }
}

impl<'acx, 'a, 'e, E: ExecutionState<'e>> SnetRecvAnalyzer<'acx, 'a, 'e, E> {
    fn check_player_list_head_bit1(&self, condition: Operand<'e>) -> Option<Operand<'e>> {
        let ctx = self.ctx;
        condition.if_and_mask_eq_neq(0x1)
            .and_then(|x| {
                let mem = x.0.if_memory()?;
                if mem.is_global() {
                    let offset = 0u64.wrapping_sub(2 * E::VirtualAddress::SIZE as u64);
                    Some(mem.with_offset(offset).address_op(ctx))
                } else {
                    None
                }
            })
    }
}
