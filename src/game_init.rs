use scarf::{DestOperand, Operand, OperandCtx, Operation, BinaryFile};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{OperandType, ArithOpType, MemAccessSize};

use crate::{
    Analysis, ArgCache, entry_of_until, EntryOfResult, EntryOf, OptionExt, find_callers,
    string_refs, if_arithmetic_eq_neq,
};

use scarf::exec_state::{ExecutionState, VirtualAddress};

/// Actually a better name would be ProcessInit
pub struct GameInit<'e, Va: VirtualAddress> {
    pub sc_main: Option<Va>,
    pub mainmenu_entry_hook: Option<Va>,
    pub game_loop: Option<Va>,
    pub scmain_state: Option<Operand<'e>>,
}

/// Data related to game (map) (gameplay state) initialization
pub struct InitGame<'e, Va: VirtualAddress> {
    pub loaded_save: Option<Operand<'e>>,
    pub init_game: Option<Va>,
}

pub struct SinglePlayerStart<'e, Va: VirtualAddress> {
    pub single_player_start: Option<Va>,
    pub local_storm_player_id: Option<Operand<'e>>,
    pub local_unique_player_id: Option<Operand<'e>>,
    pub net_player_to_game: Option<Operand<'e>>,
    pub net_player_to_unique: Option<Operand<'e>>,
    pub game_data: Option<Operand<'e>>,
    pub skins: Option<Operand<'e>>,
    pub player_skins: Option<Operand<'e>>,
    pub skins_size: u32,
}

pub struct SelectMapEntry<'e, Va: VirtualAddress> {
    pub select_map_entry: Option<Va>,
    pub is_multiplayer: Option<Operand<'e>>,
}

impl<'e, Va: VirtualAddress> Default for SinglePlayerStart<'e, Va> {
    fn default() -> Self {
        SinglePlayerStart {
            single_player_start: None,
            local_storm_player_id: None,
            local_unique_player_id: None,
            net_player_to_game: None,
            net_player_to_unique: None,
            game_data: None,
            skins: None,
            player_skins: None,
            skins_size: 0,
        }
    }
}

impl<'e, Va: VirtualAddress> Default for SelectMapEntry<'e, Va> {
    fn default() -> Self {
        SelectMapEntry {
            select_map_entry: None,
            is_multiplayer: None,
        }
    }
}

pub fn play_smk<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];

    // Find ref for char *smk_filenames[0x1c]; smk_filenames[0] == "smk\\blizzard.webm"
    let rdata = binary.section(b".rdata\0\0")?;
    let data = binary.section(b".data\0\0\0")?;
    let str_ref_addrs = crate::find_strings_casei(&rdata.data, b"smk\\blizzard.");

    let data_rvas = str_ref_addrs.iter().flat_map(|&str_rva| {
        crate::find_address_refs(&data.data, rdata.virtual_address + str_rva.0)
    }).collect::<Vec<_>>();
    let global_refs = data_rvas.iter().flat_map(|&rva| {
        crate::find_functions_using_global(analysis, data.virtual_address + rva.0)
    }).collect::<Vec<_>>();

    let mut result = None;
    for global in global_refs {
        let new = entry_of_until(binary, funcs, global.use_address, |entry| {
            let mut analyzer = IsPlaySmk::<E> {
                result: EntryOf::Retry,
                use_address: global.use_address,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(entry, ()) = new {
            if crate::single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsPlaySmk<'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsPlaySmk<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        if address.as_u64() > self.use_address.as_u64() - 8 && address < self.use_address {
            if let Operation::Move(_, value, None) = *op {
                let value = ctrl.resolve(value);
                let ok = value.if_mem32()
                    .and_then(|x| x.if_arithmetic_add())
                    .and_either(|x| x.if_arithmetic_mul())
                    .map(|((l, r), _)| (l, r))
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 4))
                    .filter(|&x| is_arg1(x))
                    .is_some();
                if ok {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
        }
    }
}

fn is_arg1(operand: Operand<'_>) -> bool {
    operand.if_memory()
        .and_then(|x| x.address.if_arithmetic_add())
        .and_either_other(|x| x.if_constant().filter(|&c| c == 4))
        .and_then(|x| x.if_register())
        .filter(|x| x.0 == 4)
        .is_some()
}

pub fn game_init<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> GameInit<'e, E::VirtualAddress> {
    let mut result = GameInit {
        sc_main: None,
        mainmenu_entry_hook: None,
        game_loop: None,
        scmain_state: None,
    };
    let play_smk = match analysis.play_smk() {
        Some(s) => s,
        None => return result,
    };
    let game = match analysis.game() {
        Some(s) => s,
        None => return result,
    };
    let mut game_pointers = Vec::with_capacity(4);
    collect_game_pointers(game, &mut game_pointers);
    // The main loop function (sc_main) calls play_smk a few times after initialization
    // but before main load.
    // Since the function is being obfuscated, confirm it being sc_main by that it writes to a
    // game pointer.
    let callers = crate::find_callers(analysis, play_smk);
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    for caller in callers {
        let new = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = IsScMain::<E> {
                result: EntryOf::Retry,
                play_smk,
                game_pointers: &game_pointers,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry().map(|x| x.0);

        if crate::single_result_assign(new, &mut result.sc_main) {
            break;
        }
    }
    if let Some(sc_main) = result.sc_main {
        let mut analyzer = ScMainAnalyzer {
            result: &mut result,
            binary,
            make_undef: None,
        };
        let exec_state = E::initial_state(ctx, binary);
        let mut analysis = FuncAnalysis::custom_state(
            binary,
            ctx,
            sc_main,
            exec_state,
            ScMainAnalyzerState::SearchingEntryHook,
        );
        analysis.analyze(&mut analyzer);
    }
    result
}

fn collect_game_pointers<'e>(operand: Operand<'e>, out: &mut Vec<Operand<'e>>) {
    match operand.ty() {
        OperandType::Memory(mem) => out.push(mem.address),
        OperandType::Arithmetic(arith) if arith.ty == ArithOpType::Xor => {
            collect_game_pointers(arith.left, out);
            collect_game_pointers(arith.right, out);
        }
        _ => (),
    }
}

struct IsScMain<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    play_smk: E::VirtualAddress,
    game_pointers: &'a [Operand<'e>],
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsScMain<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    if dest == self.play_smk.as_u64() {
                        self.result = EntryOf::Stop;
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), _, None) => {
                let addr = ctrl.resolve(mem.address);
                if self.game_pointers.iter().any(|&x| addr == x) {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

struct ScMainAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut GameInit<'e, E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    make_undef: Option<DestOperand<'e>>,
}

#[allow(bad_style)]
#[derive(Copy, Clone, Eq, PartialEq, Debug, Ord, PartialOrd)]
enum ScMainAnalyzerState {
    SearchingEntryHook,
    SearchingGameLoop,
    SearchingGameLoop_SwitchJumped,
}

impl analysis::AnalysisState for ScMainAnalyzerState {
    fn merge(&mut self, newer: Self) {
        if *self < newer {
            *self = newer;
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for ScMainAnalyzer<'a, 'e, E> {
    type State = ScMainAnalyzerState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Some(to) = self.make_undef.take() {
            let ctx = ctrl.ctx();
            let exec_state = ctrl.exec_state();
            exec_state.move_to(&to, ctx.new_undef());
        }
        match *op {
            Operation::Jump { to, condition } => {
                let condition = ctrl.resolve(condition);
                if condition.if_constant().unwrap_or(0) != 0 {
                    let to = ctrl.resolve(to);
                    if to.if_memory().is_some() {
                        // Switch jump, follow case 3 if searching for game loop,
                        // switch expression is also scmain_state then
                        if *ctrl.user_state() == ScMainAnalyzerState::SearchingGameLoop {
                            let base_offset = to.if_mem32()
                                .and_then(|x| x.if_arithmetic_add())
                                .and_either(|x| x.if_constant())
                                .and_then(|(switch_table, other)| {
                                    other.if_arithmetic_mul()
                                        .and_either_other(|x| x.if_constant().filter(|&c| c == 4))
                                        .map(|o| (switch_table, o))
                                });
                            if let Some((base, offset)) = base_offset {
                                let addr_size = <E::VirtualAddress as VirtualAddress>::SIZE;
                                let case = E::VirtualAddress::from_u64(base) + 3 * addr_size;
                                if let Ok(addr) = self.binary.read_address(case) {
                                    let offset = ctrl.unresolve_memory(offset)
                                        .unwrap_or_else(|| offset.clone());
                                    self.result.scmain_state = Some(offset);
                                    *ctrl.user_state() =
                                        ScMainAnalyzerState::SearchingGameLoop_SwitchJumped;
                                    ctrl.analyze_with_current_state(self, addr);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                } else {
                    if *ctrl.user_state() == ScMainAnalyzerState::SearchingEntryHook {
                        // BW does if options & 0x800 != 0 { play_smk(..); }
                        // at the hook point
                        let ok = crate::if_arithmetic_eq_neq(condition)
                            .map(|(l, r, _)| (l, r))
                            .and_either(|x| x.if_arithmetic_and())
                            .map(|x| x.0)
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 0x8))
                            .and_then(|other| other.if_memory())
                            .is_some();
                        if ok {
                            self.result.mainmenu_entry_hook = Some(ctrl.address());
                            *ctrl.user_state() = ScMainAnalyzerState::SearchingGameLoop;
                        }
                    }
                }
            }
            Operation::Call(to) => {
                if *ctrl.user_state() == ScMainAnalyzerState::SearchingGameLoop_SwitchJumped {
                    let to = ctrl.resolve(to);
                    if let Some(dest) = to.if_constant() {
                        self.result.game_loop = Some(E::VirtualAddress::from_u64(dest));
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Move(ref to @ DestOperand::Memory(..), val, _) => {
                // Skip any moves of constant 4 to memory as it is likely scmain_state write
                if *ctrl.user_state() == ScMainAnalyzerState::SearchingEntryHook {
                    if ctrl.resolve(val).if_constant() == Some(4) {
                        self.make_undef = Some(to.clone());
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn init_map_from_path<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    // init_map_from_path calls another function
    // that calls chk validation function.
    // Chk validation array is static data in format
    // u32 b"VER\x20", fnptr, u32 1, ...
    let chk_validated_sections = &[
        b"VER\x20",
        b"DIM\x20",
        b"ERA\x20",
        b"OWNR",
        b"SIDE",
        b"STR\x20",
        b"SPRP",
    ];
    let binary = analysis.binary;
    let rdata = binary.section(b".rdata\0\0")?;
    let mut chk_data = crate::find_bytes(&rdata.data, &chk_validated_sections[0][..]);
    chk_data.retain(|&rva| {
        if rva.0 & 3 != 0 {
            return false;
        }
        for (i, other_section) in chk_validated_sections.iter().enumerate().skip(1) {
            let index = rva.0 as usize + i * 0xc;
            let bytes = match rdata.data.get(index..index + 4) {
                Some(s) => s,
                None => return false,
            };
            if bytes != &other_section[..] {
                return false;
            }
        }
        true
    });
    let section_refs = chk_data.into_iter().flat_map(|rva| {
        let address = rdata.virtual_address + rva.0;
        crate::find_address_refs(&rdata.data, address)
    }).collect::<Vec<_>>();
    let chk_validating_funcs = section_refs.into_iter().flat_map(|rva| {
        let address = rdata.virtual_address + rva.0;
        crate::find_functions_using_global(analysis, address)
    }).collect::<Vec<_>>();
    let mut call_points = chk_validating_funcs.into_iter().flat_map(|f| {
        crate::find_callers(analysis, f.func_entry)
    }).collect::<Vec<_>>();
    call_points.sort();
    call_points.dedup();

    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;
    let mut result = None;
    for addr in call_points {
        let new = entry_of_until(binary, funcs, addr, |entry| {
            let state = IsInitMapFromPathState {
                jump_count: 0,
                is_after_arg3_check: false,
            };
            let mut analyzer = IsInitMapFromPath {
                result: EntryOf::Retry,
                arg_cache,
            };
            let exec = E::initial_state(ctx, binary);
            let mut analysis = FuncAnalysis::custom_state(binary, ctx, entry, exec, state);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(entry, ()) = new {
            if crate::single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsInitMapFromPath<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    arg_cache: &'a ArgCache<'e, E>,
}

#[derive(Default, Clone, Debug)]
struct IsInitMapFromPathState {
    jump_count: u8,
    is_after_arg3_check: bool,
}

impl analysis::AnalysisState for IsInitMapFromPathState {
    fn merge(&mut self, newer: Self) {
        self.jump_count = newer.jump_count.min(self.jump_count);
        self.is_after_arg3_check = self.is_after_arg3_check & newer.is_after_arg3_check;
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsInitMapFromPath<'a, 'e, E> {
    type State = IsInitMapFromPathState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // init_map_from_path does
        // if (arg3 == 0) {
        //     game.campaign_mission = 0;
        // }
        // as its first operation (Unless assertions enabled)
        match *op {
            Operation::Move(ref to, val, None) => {
                if ctrl.user_state().is_after_arg3_check {
                    let val = ctrl.resolve(val);
                    if val.if_constant() == Some(0) {
                        if let DestOperand::Memory(mem) = to {
                            let addr = ctrl.resolve(mem.address);
                            if let Some((_, r)) = addr.if_arithmetic_add() {
                                if r.if_constant() == Some(0x154) {
                                    self.result = EntryOf::Ok(());
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if ctrl.user_state().jump_count > 5 {
                    ctrl.end_branch();
                }
                ctrl.user_state().jump_count += 1;
                let cond = ctrl.resolve(condition);
                let mut arg3_check = false;
                if let Some((l, r, _)) = crate::if_arithmetic_eq_neq(cond) {
                    if r.if_constant() == Some(0) {
                        if self.arg_cache.on_entry(2) == l {
                            arg3_check = true;
                        }
                    }
                }
                ctrl.user_state().is_after_arg3_check = arg3_check;
            }
            _ => (),
        }
    }
}

pub fn choose_snp<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    // Search for vtable of AVSelectConnectionScreen, whose event handler (Fn vtable + 0x18)
    // with arg1 == 9 calls a child function doing
    // if this.provider_id == ID_BNAU {
    //    unk(this.field2, this.field3)
    //    choose_snp_for_net(this.provider_id)
    // }
    // In 1232e it is done immediately, 1221 has some extra step (inlined?)
    // which also compares for ID_BNAU
    //
    // The choose_snp_for_net is actually slightly different from choose_snp,
    // but the difference isn't really important. choose_snp is only called
    // as is for provider 0, and choose_snp_for_net just immediately calls
    // choose_snp if provider id isn't BNET.
    let vtables = crate::vtables::vtables(analysis, b".?AVSelectConnectionScreen@glues@@\0");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let arg_cache = &analysis.arg_cache;
    let mut result = None;
    for vtable in vtables {
        let func = match binary.read_address(vtable + 0x6 * E::VirtualAddress::SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let state = FindChooseSnpState {
            provider_id_offset: None,
        };
        let mut analyzer = FindChooseSnp {
            result: None,
            arg_cache,
            inlining: false,
        };
        let mut exec = E::initial_state(ctx, binary);
        exec.move_to(
            &DestOperand::from_oper(arg_cache.on_entry(0)),
            ctx.constant(9),
        );
        let mut analysis = FuncAnalysis::custom_state(binary, ctx, func, exec, state);
        analysis.analyze(&mut analyzer);
        if crate::single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    // The first returned value is likely choose_snp_for_net()
    // which has some extra features if provider_id == BNET.
    // Would be fine but single_player_start calls the actual
    // choose_snp, so find it for analysis depending on that.
    if let Some(addr) = result {
        let mut analyzer = FindRealChooseSnp::<E> {
            result: None,
            funcs,
            ctx,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, addr);
        analysis.analyze(&mut analyzer);
        if analyzer.result.is_some() {
            result = analyzer.result;
        }
    }
    result
}

struct FindRealChooseSnp<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    funcs: &'a [E::VirtualAddress],
    ctx: OperandCtx<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindRealChooseSnp<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // Search for tail call func
        match *op {
            Operation::Jump { condition, to } => {
                if let Some(c) = condition.if_constant() {
                    if c != 0 {
                        let esp_nonchanged = ctrl.resolve(self.ctx.register(4))
                            .if_register().filter(|x| x.0 == 4)
                            .is_some();
                        if esp_nonchanged {
                            if let Some(to) = to.if_constant() {
                                let to = E::VirtualAddress::from_u64(to);
                                if self.funcs.binary_search(&to).is_ok() {
                                    self.result = Some(to);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            Operation::Call(_) => {
                ctrl.end_branch();
            }
            _ => (),
        }
    }
}

struct FindChooseSnp<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining: bool,
}

#[derive(Default, Clone, Debug)]
struct FindChooseSnpState<'e> {
    provider_id_offset: Option<Operand<'e>>,
}

impl<'e> analysis::AnalysisState for FindChooseSnpState<'e> {
    fn merge(&mut self, newer: Self) {
        if self.provider_id_offset != newer.provider_id_offset {
            self.provider_id_offset = None;
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindChooseSnp<'a, 'e, E> {
    type State = FindChooseSnpState<'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        const ID_BNAU: u32 = 0x424E4155;
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if let Some(off) = ctrl.user_state().provider_id_offset.clone() {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1 == off {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    if !self.inlining {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                let provider_id = crate::if_arithmetic_eq_neq(cond)
                    .map(|x| (x.0, x.1))
                    .and_either_other(|x| x.if_constant().filter(|&c| c == ID_BNAU as u64));
                ctrl.user_state().provider_id_offset = provider_id;
            }
            _ => (),
        }
    }
}

pub fn single_player_start<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> SinglePlayerStart<'e, E::VirtualAddress> {
    let mut result = SinglePlayerStart::default();
    let choose_snp = match analysis.choose_snp() {
        Some(s) => s,
        None => return result,
    };
    let local_player_id = match analysis.local_player_id() {
        Some(s) => s,
        None => return result,
    };
    let callers = crate::find_callers(analysis, choose_snp);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let arg_cache = &analysis.arg_cache;
    for caller in callers {
        let ok = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = SinglePlayerStartAnalyzer {
                result: &mut result,
                arg_cache,
                local_player_id: &local_player_id,
                inlining: false,
                ctx,
            };
            let exec = E::initial_state(ctx, binary);
            let state = SinglePlayerStartState::SearchingStorm101;
            let mut analysis = FuncAnalysis::custom_state(binary, ctx, entry, exec, state);
            analysis.analyze(&mut analyzer);
            if result.local_storm_player_id.is_some() {
                result.single_player_start = Some(entry);
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        });
        if let EntryOfResult::Ok(..) = ok {
            break;
        }
    }
    result
}

struct SinglePlayerStartAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SinglePlayerStart<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    local_player_id: &'a Operand<'e>,
    inlining: bool,
    ctx: OperandCtx<'e>,
}

/// These are ordered from first step to last
#[derive(Ord, Eq, PartialEq, PartialOrd, Debug, Copy, Clone)]
enum SinglePlayerStartState {
    // calls Storm#101(addr, "", "", 0, 0, 0, u8[x], "", &mut local_storm_player_id)
    SearchingStorm101,
    // Does
    //  net_player_to_game(*)[local_storm_player_id] = local_player_id
    //  net_player_to_unique(*)[local_storm_player_id] = local_unique_player_id(*)
    //  memcpy(&mut game_data(*), arg1)
    // finds ones marked(*), inlining is necessary.
    AssigningPlayerMappings,
    // Does memcpy(&mut player_skins[local_storm_player_id], &skins.active_skins)
    FindingSkins,
}

impl analysis::AnalysisState for SinglePlayerStartState {
    fn merge(&mut self, newer: Self) {
        if *self < newer {
            *self = newer;
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SinglePlayerStartAnalyzer<'a, 'e, E>
{
    type State = SinglePlayerStartState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *ctrl.user_state() {
            SinglePlayerStartState::SearchingStorm101 => {
                if let Operation::Call(_) = op {
                    let ok = Some(ctrl.resolve(self.arg_cache.on_call(3)))
                        .filter(|x| x.if_constant() == Some(0))
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(4)))
                        .filter(|x| x.if_constant() == Some(0))
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(5)))
                        .filter(|x| x.if_constant() == Some(0))
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(6)))
                        .filter(|x| x.if_mem8().is_some())
                        .is_some();
                    if ok {
                        let arg10 = ctrl.resolve(self.arg_cache.on_call(9));
                        *ctrl.user_state() = SinglePlayerStartState::AssigningPlayerMappings;
                        self.result.local_storm_player_id = Some(self.ctx.mem32(arg10));
                    }
                }
            }
            SinglePlayerStartState::AssigningPlayerMappings => {
                if let Operation::Call(dest) = *op {
                    // Check for memcpy(&mut game_data, arg1, 0x8d) call
                    // Maybe broken since 1232e at least uses rep movs
                    let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                    if arg3.if_constant() == Some(0x8d) {
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        if arg2 == self.arg_cache.on_entry(0) {
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(1));
                            self.result.game_data = Some(arg1);
                        }
                    }
                    if !self.inlining {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inlining = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inlining = false;
                        }
                    }
                } else if let Operation::Move(ref dest, val, None) = *op {
                    if let DestOperand::Memory(mem) = dest {
                        let val = ctrl.resolve(val);
                        let dest_addr = ctrl.resolve(mem.address);
                        let is_move_to_u32_arr = dest_addr.if_arithmetic_add()
                            .and_either(|x| {
                                x.if_arithmetic_mul()
                                    .filter(|(_l, r)| r.if_constant() == Some(4))
                                    .map(|(l, _r)| l)
                            });
                        if let Some((index, base)) = is_move_to_u32_arr {
                            if let Some(storm_id) = self.result.local_storm_player_id {
                                if index == storm_id {
                                    if val == *self.local_player_id {
                                        self.result.net_player_to_game = Some(base.clone());
                                    } else {
                                        self.result.net_player_to_unique = Some(base.clone());
                                        self.result.local_unique_player_id = Some(val.clone());
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Special(ref bytes) = op {
                    // (Rep) movs dword
                    if bytes == &[0xf3, 0xa5] {
                        let len = ctrl.resolve(self.ctx.register_ref(1));
                        let from = ctrl.resolve(self.ctx.register_ref(6));
                        let dest = ctrl.resolve(self.ctx.register_ref(7));
                        if len.if_constant() == Some(0x23) {
                            if from == self.arg_cache.on_entry(0) {
                                self.result.game_data = Some(dest);
                            }
                        }
                    }
                }
                let all_found = self.result.game_data.is_some() &&
                    self.result.net_player_to_game.is_some() &&
                    self.result.net_player_to_unique.is_some();
                if all_found {
                    *ctrl.user_state() = SinglePlayerStartState::FindingSkins;
                }
            }
            SinglePlayerStartState::FindingSkins => {
                let result = &mut self.result;
                let ctx = self.ctx;
                if let Operation::Call(dest) = *op {
                    if !self.inlining {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inlining = true;
                            ctrl.inline(self, dest);
                            ctrl.skip_operation();
                            self.inlining = false;
                        }
                    }
                } else {
                    let dest_from = match *op {
                        Operation::Move(ref dest, val, None) => match dest {
                            DestOperand::Memory(mem) => {
                                let dest = ctrl.resolve(mem.address);
                                let val = ctrl.resolve(val);
                                if let Some(mem) = val.if_memory() {
                                    Some((dest, mem.address.clone()))
                                } else {
                                    None
                                }
                            },
                            _ => None,
                        }
                        Operation::Special(ref bytes) => {
                            // (Rep) movs dword
                            if bytes == &[0xf3, 0xa5] {
                                let from = ctrl.resolve(ctx.register(6));
                                let dest = ctrl.resolve(ctx.register(7));
                                Some((dest, from))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };

                    if let Some((dest, addr)) = dest_from {
                        let index_base = dest.if_arithmetic_add()
                            .and_either(|x| x.if_arithmetic_mul());
                        if let Some((index, base)) = index_base {
                            if let Some(size) = index.1.if_constant() {
                                if let Some(storm_id) = result.local_storm_player_id {
                                    if index.0 == storm_id {
                                        let addr = ctx.sub_const(addr, 0x14);
                                        if size > 16 {
                                            crate::single_result_assign(
                                                Some(addr),
                                                &mut result.skins,
                                            );
                                            crate::single_result_assign(
                                                Some(base),
                                                &mut result.player_skins,
                                            );
                                            result.skins_size = size as u32;
                                            if !crate::test_assertions() {
                                                ctrl.end_analysis();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn select_map_entry<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> SelectMapEntry<'e, E::VirtualAddress> {
    let mut result = SelectMapEntry::default();
    let start = analysis.single_player_start();
    let single_player_start = match start.single_player_start{
        Some(s) => s,
        None => return result,
    };
    // select_map_entry is one of functions calling single_player_start.
    // Assume also that it moves 0 to arg3.fc (Older versions use a different offset)
    // on start and that first global u8 that is used as jump condition after that is
    // is_multiplayer.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let callers = crate::find_callers(analysis, single_player_start);
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let arg_cache = &analysis.arg_cache;
    for caller in callers {
        entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = FindSelectMapEntry::<E> {
                arg_cache,
                first_branch: true,
                arg3_write_seen: false,
                mem_byte_conds: Vec::new(),
                mem_bytes_written: Vec::new(),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if analyzer.arg3_write_seen {
                let mut is_multiplayer_candidates = analyzer.mem_byte_conds;
                let not_is_multiplayer = analyzer.mem_bytes_written;
                is_multiplayer_candidates.sort();
                result.select_map_entry = Some(entry);
                let is_multiplayer = is_multiplayer_candidates.iter()
                    .map(|x| x.1)
                    .filter(|&x| !not_is_multiplayer.iter().any(|&y| x == y))
                    .next()
                    .map(|x| ctx.mem8(x));
                result.is_multiplayer = is_multiplayer;
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        });
        if result.select_map_entry.is_some() {
            break;
        }
    }
    result
}

struct FindSelectMapEntry<'a, 'e, E: ExecutionState<'e>> {
    first_branch: bool,
    arg3_write_seen: bool,
    arg_cache: &'a ArgCache<'e, E>,
    // Don't accept Mem8[x] == 0 condition if the same location gets written.
    // (Filters out assert-once globals)
    mem_byte_conds: Vec<(E::VirtualAddress, Operand<'e>)>,
    mem_bytes_written: Vec<Operand<'e>>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSelectMapEntry<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                if self.first_branch {
                    if !self.arg3_write_seen {
                        ctrl.end_analysis();
                    }
                    self.first_branch = false;
                } else {
                    let condition = ctrl.resolve(condition);
                    let mem_byte = crate::if_arithmetic_eq_neq(condition)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                        .and_then(|x| x.if_mem8());
                    if let Some(addr) = mem_byte {
                        self.mem_byte_conds.push((ctrl.address(), addr.clone()));
                    }
                }
            }
            Operation::Move(ref dest, _, _) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem8 {
                        let addr = ctrl.resolve(mem.address);
                        if self.first_branch {
                            if let Some((l, r)) = addr.if_arithmetic_add() {
                                let right_ok = r.if_constant()
                                    .filter(|&c| c > 0x20)
                                    .is_some();
                                // Older versions of the function had arg1 as
                                // map entry (and used 5 args total instead of 3)
                                let left_ok = l == self.arg_cache.on_entry(2) ||
                                    l == self.arg_cache.on_entry(0);
                                if right_ok && left_ok {
                                    self.arg3_write_seen = true;
                                }
                            }
                        }
                        self.mem_bytes_written.push(addr.clone());
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn load_images<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    // First operation of load_images is to call
    // func("scripts\\iscript.bin", 0, &mut iscript_bin_size, "", 0)
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let str_refs = string_refs(binary, analysis, b"scripts\\iscript.bin\0");
    let mut result = None;
    for string in str_refs {
        let new = entry_of_until(binary, funcs, string.use_address, |entry| {
            let arg_cache = &analysis.arg_cache;
            let mut analyzer = IsLoadImages::<E> {
                result: EntryOf::Retry,
                use_address: string.use_address,
                string_address: string.string_address,
                arg_cache,
                jump_limit: 3,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(entry, ()) = new {
            if crate::single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsLoadImages<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    string_address: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
    jump_limit: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsLoadImages<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        if address + 8 > self.use_address && address < self.use_address {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Call(_) => {
                if let Some(c) = ctrl.resolve(self.arg_cache.on_call(0)).if_constant() {
                    if c == self.string_address.as_u64() {
                        self.result = EntryOf::Ok(());
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { .. } | Operation::Return(..) => {
                if self.jump_limit == 0 {
                    ctrl.end_analysis();
                } else {
                    self.jump_limit -= 1;
                }
            }
            _ => (),
        }
    }
}

pub fn images_loaded<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let load_images = analysis.load_images()?;
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let callers = crate::find_callers(analysis, load_images);
    let mut result = None;
    for caller in callers {
        let new = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = FindImagesLoaded::<E> {
                result: EntryOf::Retry,
                load_images,
                conditions: Vec::new(),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(_, res) = new {
            if crate::single_result_assign(Some(res), &mut result) {
                break;
            }
        }
    }
    result
}

struct FindImagesLoaded<'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    load_images: E::VirtualAddress,
    conditions: Vec<(E::VirtualAddress, Operand<'e>)>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindImagesLoaded<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // images_loaded if checked right before calling load_images
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    if dest == self.load_images.as_u64() {
                        let cond = self.conditions.iter()
                            .filter(|x| x.0 < ctrl.address())
                            .max_by_key(|x| x.0)
                            .map(|x| x.1);
                        if let Some(cond) = cond {
                            let cond = if_arithmetic_eq_neq(cond)
                                .map(|(l, r, _)| (l, r))
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                                .filter(|x| x.if_mem8().is_some());
                            if let Some(cond) = cond {
                                self.result = EntryOf::Ok(cond.clone());
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        self.result = EntryOf::Stop;
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                self.conditions.push((ctrl.address(), ctrl.resolve(condition)));
            }
            _ => (),
        }
    }
}

pub fn local_player_name<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    #[allow(bad_style)]
    let VA_SIZE: u32 = E::VirtualAddress::SIZE;

    let mut vtables = crate::vtables::vtables(analysis, b".?AVCreateGameScreen@glues@@\0");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let relocs = analysis.relocs();
    let mut vtable_lengths = vtables.iter().map(|&addr| {
        let reloc_pos = match relocs.binary_search(&addr) {
            Ok(o) => o,
            Err(_) => return 0,
        };
        let mut len = 0;
        while reloc_pos + len < relocs.len() {
            if relocs[reloc_pos + len] == addr + (len as u32) * VA_SIZE {
                len += 1;
            } else {
                break;
            }
        }
        len as u32
    }).collect::<Vec<_>>();
    for i in (0..vtables.len()).rev() {
        if vtable_lengths[i] < 0x30 {
            vtable_lengths.swap_remove(i);
            vtables.swap_remove(i);
        }
    }
    let highest_length = vtable_lengths.iter().max()?;
    let mut acceptable_funcs = Vec::with_capacity(0x20);
    // The get_player_name function is same for all others than bnet create game screen
    'outer: for index in 0x30..(highest_length + 1) {
        let pos = match vtable_lengths.iter().position(|&len| len >= index) {
            Some(s) => s,
            None => continue,
        };
        let addr1 = match binary.read_address(vtables[pos] + index * VA_SIZE) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let mut addr1_count = 1;
        let mut addr2 = E::VirtualAddress::from_u64(0);
        let mut addr2_count = 0;
        for pos in (pos + 1)..vtables.len() {
            if vtable_lengths[pos] >= index {
                let addr = match binary.read_address(vtables[pos] + index * VA_SIZE) {
                    Ok(o) => o,
                    Err(_) => continue,
                };
                if addr != addr1 {
                    if addr2_count != 0 && addr != addr2 {
                        // Had another different address, this function
                        // isn't what we're looking for.
                        continue 'outer;
                    }
                    addr2 = addr;
                    addr2_count += 1;
                } else {
                    addr1_count += 1;
                }
            }
        }
        if addr2_count == 1 && addr1_count > 4 {
            acceptable_funcs.push(addr1);
        } else if addr1_count == 1 && addr2_count > 4 {
            acceptable_funcs.push(addr2);
        }
    }

    let mut result = None;
    for entry in acceptable_funcs {
        let mut analyzer = CheckLocalPlayerName::<E> {
            result: None,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        analysis.analyze(&mut analyzer);
        if crate::single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    result
}

struct CheckLocalPlayerName<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CheckLocalPlayerName<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // First condition checks `if (local_player_name[0] != 0)`
        match *op {
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                let address = if_arithmetic_eq_neq(cond)
                    .map(|(l, r, _)| (l, r))
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                    .and_then(|x| x.if_mem8());
                if let Some(address) = address {
                    self.result = Some(address.clone());
                }
                ctrl.end_analysis();
            }
            Operation::Call(_) => {
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

pub fn init_game_network<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let single_player_start = analysis.single_player_start();
    let local_storm_player = single_player_start.local_storm_player_id?;
    let vtables = crate::vtables::vtables(analysis, b".?AVGameLobbyScreen@glues@@\0");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    // Lobby screen vtable's Control::init calls init_game_network,
    // init_game_network immediately compares local_storm_player == 0
    let mut result = None;
    for vtable in vtables {
        let addr = match binary.read_address(vtable + E::VirtualAddress::SIZE * 3) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let mut analyzer = FindInitGameNetwork::<E> {
            result: None,
            local_storm_player,
            inlining: false,
            jump_limit: 0,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, addr);
        analysis.analyze(&mut analyzer);
        if crate::single_result_assign(analyzer.result, &mut result) {
            break;
        }
    }
    result
}

struct FindInitGameNetwork<'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    local_storm_player: Operand<'e>,
    inlining: bool,
    jump_limit: u8,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindInitGameNetwork<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        // Assert-enabled builds have a lot of assertions at start
                        self.jump_limit = 10;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.result.is_some() {
                            self.result = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.inlining {
                    let condition = ctrl.resolve(condition);
                    let ok = if_arithmetic_eq_neq(condition)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                        .filter(|&x| x == self.local_storm_player)
                        .is_some();
                    if ok {
                        // Set properly in Call branch
                        self.result = Some(E::VirtualAddress::from_u64(0));
                    }
                    self.jump_limit -= 1;
                    if ok || self.jump_limit == 0 {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn lobby_state<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let (switch, _) = analysis.process_lobby_commands_switch()?;

    // Command 0x48 compares state == 8 at start of the function
    let branch = switch.branch(0x48)?;
    let mut analyzer = FindLobbyState::<E> {
        result: None,
        inlining: false,
        jump_limit: 0,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, branch);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindLobbyState<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    jump_limit: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindLobbyState<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.jump_limit = 7;
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if !self.inlining {
                    if to.if_constant().is_none() {
                        // Stop at switch jump
                        ctrl.end_branch();
                    }
                } else {
                    let cond = ctrl.resolve(condition);
                    let lobby_state = if_arithmetic_eq_neq(cond)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 8));
                    if let Some(lobby_state) = lobby_state {
                        self.result = Some(lobby_state.clone());
                        ctrl.end_analysis();
                    }
                    self.jump_limit -= 1;
                    if self.jump_limit == 0 {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn init_game<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> InitGame<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = InitGame {
        loaded_save: None,
        init_game: None,
    };
    let init_units = match analysis.init_units() {
        Some(s) => s,
        None => return result,
    };
    let functions = analysis.functions();

    let callers = find_callers(analysis, init_units);
    for call in callers {
        let mut invalid_handle_cmps: Vec<(E::VirtualAddress, _)> = Vec::new();
        let val = entry_of_until(binary, &functions, call, |entry| {
            invalid_handle_cmps.clear();
            let mut analyzer = InitGameAnalyzer::<E> {
                result: EntryOf::Retry,
                init_units,
                invalid_handle_cmps: &mut invalid_handle_cmps,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();
        if let Some((entry, loaded_save)) = val {
            result.loaded_save = Some(loaded_save);
            result.init_game = Some(entry);
            break;
        }
    }

    result
}

struct InitGameAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    invalid_handle_cmps: &'a mut Vec<(E::VirtualAddress, Operand<'e>)>,
    result: EntryOf<Operand<'e>>,
    init_units: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for InitGameAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                let cmp_invalid_handle = cond.iter_no_mem_addr()
                    .filter_map(|x| x.if_arithmetic_eq())
                    .filter_map(|(l, r)| {
                        Operand::either(l, r, |x| x.if_constant())
                    })
                    .filter(|&(c, _)| c as u32 == u32::max_value())
                    .map(|x| x.1.clone())
                    .next();
                if let Some(h) = cmp_invalid_handle {
                    let address = ctrl.address();
                    if !self.invalid_handle_cmps.iter().any(|x| x.0 == address) {
                        self.invalid_handle_cmps.push((address, h));
                    }
                    if self.invalid_handle_cmps.len() >= 3 {
                        let first = &self.invalid_handle_cmps[0].1;
                        let ok = (&self.invalid_handle_cmps[1..]).iter()
                            .all(|x| x.1 == *first);
                        if ok {
                            self.result = EntryOf::Ok(self.invalid_handle_cmps.swap_remove(0).1);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(c) = ctrl.resolve(dest).if_constant() {
                    if c == self.init_units.as_u64() {
                        self.result = EntryOf::Stop;
                    }
                }
            }
            _ => (),
        }
    }
}
