use std::collections::hash_map::Entry;
use std::convert::TryFrom;

use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use scarf::{DestOperand, Operand, OperandCtx, Operation, BinaryFile, BinarySection};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{OperandType, ArithOpType, MemAccessSize};

use crate::switch::CompleteSwitch;
use crate::{
    AnalysisCtx, ArgCache, entry_of_until, EntryOfResult, EntryOf, OptionExt, OperandExt,
    if_arithmetic_eq_neq, single_result_assign, bumpvec_with_capacity, FunctionFinder,
    ControlExt,
};

use scarf::exec_state::{ExecutionState, VirtualAddress};

/// Actually a better name would be ProcessInit
pub struct GameInit<'e, Va: VirtualAddress> {
    pub sc_main: Option<Va>,
    pub mainmenu_entry_hook: Option<Va>,
    pub game_loop: Option<Va>,
    pub run_menus: Option<Va>,
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

pub(crate) struct ImagesLoaded<'e, Va: VirtualAddress> {
    pub images_loaded: Option<Operand<'e>>,
    pub init_real_time_lighting: Option<Va>,
    pub asset_scale: Option<Operand<'e>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct InitMapFromPath<Va: VirtualAddress> {
    pub init_map_from_path: Va,
    pub map_init_chk_callbacks: Va,
}

pub(crate) struct LoadImagesAnalysis<'e, Va: VirtualAddress> {
    pub open_anim_single_file: Option<Va>,
    pub open_anim_multi_file: Option<Va>,
    pub init_skins: Option<Va>,
    pub add_asset_change_cb: Option<Va>,
    pub anim_asset_change_cb: Option<Va>,
    pub base_anim_set: Option<Operand<'e>>,
    pub image_grps: Option<Operand<'e>>,
    pub image_overlays: Option<Operand<'e>>,
    pub fire_overlay_max: Option<Operand<'e>>,
    pub anim_struct_size: u16,
}

pub(crate) struct GameLoopAnalysis<'e, Va: VirtualAddress> {
    pub step_network: Option<Va>,
    pub render_screen: Option<Va>,
    pub load_pcx: Option<Va>,
    pub set_music: Option<Va>,
    pub step_game_loop: Option<Va>,
    pub step_game_logic: Option<Va>,
    pub process_events: Option<Va>,
    pub menu_screen_id: Option<Operand<'e>>,
    pub main_palette: Option<Operand<'e>>,
    pub palette_set: Option<Operand<'e>>,
    pub tfontgam: Option<Operand<'e>>,
    pub sync_data: Option<Operand<'e>>,
    pub sync_active: Option<Operand<'e>>,
    pub continue_game_loop: Option<Operand<'e>>,
    pub anti_troll: Option<Operand<'e>>,
    pub step_game_frames: Option<Operand<'e>>,
    pub next_game_step_tick: Option<Operand<'e>>,
    pub replay_seek_frame: Option<Operand<'e>>,
}

pub(crate) struct ProcessEventsAnalysis<'e, Va: VirtualAddress> {
    pub bnet_controller: Option<Operand<'e>>,
    pub step_bnet_controller: Option<Va>,
    pub bnet_message_switch: Option<CompleteSwitch<'e>>,
    pub message_vtable_type: u16,
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

pub(crate) fn play_smk<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    // Find ref for char *smk_filenames[0x1c]; smk_filenames[0] == "smk\\blizzard.webm"
    let rdata = binary.section(b".rdata\0\0")?;
    let data = binary.section(b".data\0\0\0")?;
    let str_ref_addrs = crate::find_strings_casei(bump, &rdata.data, b"smk\\blizzard.");

    let data_rvas = str_ref_addrs.iter().flat_map(|&str_rva| {
        crate::find_address_refs(bump, &data.data, rdata.virtual_address + str_rva.0)
    });
    let data_rvas = BumpVec::from_iter_in(data_rvas, bump);
    let global_refs = data_rvas.iter().flat_map(|&rva| {
        functions.find_functions_using_global(analysis, data.virtual_address + rva.0)
    });
    let global_refs = BumpVec::from_iter_in(global_refs, bump);

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
            if single_result_assign(Some(entry), &mut result) {
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

pub(crate) fn game_init<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    play_smk: E::VirtualAddress,
    game: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> GameInit<'e, E::VirtualAddress> {
    let mut result = GameInit {
        sc_main: None,
        mainmenu_entry_hook: None,
        game_loop: None,
        run_menus: None,
        scmain_state: None,
    };
    let bump = &analysis.bump;
    let mut game_pointers = bumpvec_with_capacity(4, bump);
    collect_game_pointers(game, &mut game_pointers);
    // The main loop function (sc_main) calls play_smk a few times after initialization
    // but before main load.
    // Since the function is being obfuscated, confirm it being sc_main by that it writes to a
    // game pointer.
    let callers = functions.find_callers(analysis, play_smk);
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = functions.functions();
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

        if single_result_assign(new, &mut result.sc_main) {
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

fn collect_game_pointers<'e>(operand: Operand<'e>, out: &mut BumpVec<'_, Operand<'e>>) {
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
    SwitchJumped(u8),
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
                if let ScMainAnalyzerState::SwitchJumped(..) = *ctrl.user_state() {
                    // Expecting call immediately after switch jump
                    ctrl.end_analysis();
                    return;
                }
                let condition = ctrl.resolve(condition);
                if condition.if_constant().unwrap_or(0) != 0 {
                    let to = ctrl.resolve(to);
                    if to.if_memory().is_some() {
                        // Switch jump, follow cases 3 & 4 if searching for game loop,
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
                                for case_n in 3..5 {
                                    let case = E::VirtualAddress::from_u64(base) +
                                        case_n as u32 * addr_size;
                                    if let Ok(addr) = self.binary.read_address(case) {
                                        let offset = ctrl.unresolve_memory(offset)
                                            .unwrap_or_else(|| offset.clone());
                                        self.result.scmain_state = Some(offset);
                                        *ctrl.user_state() =
                                            ScMainAnalyzerState::SwitchJumped(case_n);
                                        ctrl.analyze_with_current_state(self, addr);
                                    }
                                }
                                ctrl.end_analysis();
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
                if let ScMainAnalyzerState::SwitchJumped(case) = *ctrl.user_state() {
                    let to = ctrl.resolve(to);
                    if let Some(dest) = to.if_constant() {
                        if case == 3 {
                            self.result.game_loop = Some(E::VirtualAddress::from_u64(dest));
                        } else {
                            self.result.run_menus = Some(E::VirtualAddress::from_u64(dest));
                        }
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

pub(crate) fn init_map_from_path<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<InitMapFromPath<E::VirtualAddress>> {
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
    let bump = &analysis.bump;
    let rdata = analysis.binary_sections.rdata;
    let mut chk_data = crate::find_bytes(bump, &rdata.data, &chk_validated_sections[0][..]);
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
        crate::find_address_refs(bump, &rdata.data, address)
            .into_iter()
            .map(move |x| (rva, x))
    });
    let section_refs = BumpVec::from_iter_in(section_refs, bump);
    let chk_validating_funcs = section_refs.into_iter().flat_map(|(chk_funcs_rva, rva)| {
        let address = rdata.virtual_address + rva.0;
        functions.find_functions_using_global(analysis, address)
            .into_iter()
            .map(move |x| (chk_funcs_rva, x))
    });
    let chk_validating_funcs = BumpVec::from_iter_in(chk_validating_funcs, bump);
    let call_points = chk_validating_funcs.into_iter().flat_map(|(chk_funcs_rva, f)| {
        functions.find_callers(analysis, f.func_entry)
            .into_iter()
            .map(move |x| (chk_funcs_rva, x))
    });
    let mut call_points = BumpVec::from_iter_in(call_points, bump);
    call_points.sort_unstable_by_key(|x| x.1);
    call_points.dedup_by_key(|x| x.1);

    let funcs = functions.functions();
    let arg_cache = &analysis.arg_cache;
    let ctx = analysis.ctx;
    let mut result = None;
    for (chk_funcs_rva, addr) in call_points {
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
            let new = InitMapFromPath {
                init_map_from_path: entry,
                map_init_chk_callbacks: rdata.virtual_address + chk_funcs_rva.0,
            };
            if single_result_assign(Some(new), &mut result) {
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

#[derive(Default, Copy, Clone, Debug)]
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

pub(crate) fn choose_snp<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
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
    let vtables =
        crate::vtables::vtables(analysis, functions, b".?AVSelectConnectionScreen@glues@@\0");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
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
        if single_result_assign(analyzer.result, &mut result) {
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

#[derive(Default, Copy, Clone, Debug)]
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

pub(crate) fn single_player_start<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    choose_snp: E::VirtualAddress,
    local_player_id: Operand<'e>,
) -> SinglePlayerStart<'e, E::VirtualAddress> {
    let mut result = SinglePlayerStart::default();
    let callers = functions.find_callers(analysis, choose_snp);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
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
                    if &bytes[..] == &[0xf3, 0xa5] {
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
                            if &bytes[..] == &[0xf3, 0xa5] {
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
                                            single_result_assign(
                                                Some(addr),
                                                &mut result.skins,
                                            );
                                            single_result_assign(
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

pub(crate) fn select_map_entry<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    single_player_start: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> SelectMapEntry<'e, E::VirtualAddress> {
    let mut result = SelectMapEntry::default();
    // select_map_entry is one of functions calling single_player_start.
    // Assume also that it moves 0 to arg3.fc (Older versions use a different offset)
    // on start and that first global u8 that is used as jump condition after that is
    // is_multiplayer.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let callers = functions.find_callers(analysis, single_player_start);
    let funcs = functions.functions();
    let arg_cache = &analysis.arg_cache;
    let bump = &analysis.bump;
    for caller in callers {
        entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = FindSelectMapEntry::<E> {
                arg_cache,
                first_branch: true,
                arg3_write_seen: false,
                mem_byte_conds: bumpvec_with_capacity(8, bump),
                mem_bytes_written: bumpvec_with_capacity(8, bump),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if analyzer.arg3_write_seen {
                let mut is_multiplayer_candidates = analyzer.mem_byte_conds;
                let not_is_multiplayer = analyzer.mem_bytes_written;
                is_multiplayer_candidates.sort_unstable();
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

struct FindSelectMapEntry<'acx, 'e, E: ExecutionState<'e>> {
    first_branch: bool,
    arg3_write_seen: bool,
    arg_cache: &'acx ArgCache<'e, E>,
    // Don't accept Mem8[x] == 0 condition if the same location gets written.
    // (Filters out assert-once globals)
    mem_byte_conds: BumpVec<'acx, (E::VirtualAddress, Operand<'e>)>,
    mem_bytes_written: BumpVec<'acx, Operand<'e>>,
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

pub(crate) fn load_images<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // First operation of load_images is to call
    // func("scripts\\iscript.bin", 0, &mut iscript_bin_size, "", 0)
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
    let str_refs = functions.string_refs(analysis, b"scripts\\iscript.bin\0");
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
            if single_result_assign(Some(entry), &mut result) {
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

pub(crate) fn images_loaded<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    load_images: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> ImagesLoaded<'e, E::VirtualAddress> {
    let mut result = ImagesLoaded {
        images_loaded: None,
        init_real_time_lighting: None,
        asset_scale: None,
    };
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let funcs = functions.functions();
    let callers = functions.find_callers(analysis, load_images);
    for caller in callers {
        let res = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = FindImagesLoaded::<E> {
                result: EntryOf::Retry,
                load_images,
                conditions: bumpvec_with_capacity(8, bump),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(_, (images_loaded, else_branch)) = res {
            single_result_assign(Some(images_loaded), &mut result.images_loaded);
            let mut analyzer = FindBeginLoadingRtl::<E> {
                result: &mut result,
                checking_func: false,
                call_limit: 5,
                func_returns: Vec::with_capacity(8),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, else_branch);
            analysis.analyze(&mut analyzer);
            if result.init_real_time_lighting.is_some() {
                break;
            }
        }
    }
    result
}

struct FindBeginLoadingRtl<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ImagesLoaded<'e, E::VirtualAddress>,
    checking_func: bool,
    call_limit: u8,
    func_returns: Vec<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindBeginLoadingRtl<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            // init_rtl should be called immediately at the branch
            // if images_loaded == 1
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if !self.checking_func {
                        self.check_func(ctrl, dest);
                    } else {
                        if self.call_limit == 0 {
                            ctrl.end_analysis();
                            return;
                        }
                        self.call_limit -= 1;
                        let ctx = ctrl.ctx();
                        let exec = ctrl.exec_state();
                        let idx = self.func_returns.len() as u32;
                        let custom = ctx.custom(idx);
                        self.func_returns.push(dest);
                        exec.move_to(
                            &DestOperand::Register64(scarf::operand::Register(0)),
                            custom,
                        );
                        ctrl.skip_operation();
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if !self.checking_func {
                    let ctx = ctrl.ctx();
                    if condition == ctx.const_1() {
                        // Assuming tail call
                        if let Some(dest) = ctrl.resolve_va(to) {
                            self.check_func(ctrl, dest);
                        }
                    } else {
                        ctrl.end_analysis();
                    }
                } else {
                    let condition = ctrl.resolve(condition);
                    let asset_scale = if_arithmetic_eq_neq(condition)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 4));
                    if let Some(scale) = asset_scale {
                        let funcs = &self.func_returns;
                        let ctx = ctrl.ctx();
                        let binary = ctrl.binary();
                        let scale = ctx.transform(scale, 8, |op| {
                            if let Some(idx) = op.if_custom() {
                                let func = funcs[idx as usize];
                                crate::call_tracker::analyze_func_return::<E>(func, ctx, binary)
                            } else {
                                None
                            }
                        });
                        self.result.init_real_time_lighting =
                            Some(E::VirtualAddress::from_u64(0));
                        self.result.asset_scale = Some(scale);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindBeginLoadingRtl<'a, 'e, E> {
    fn check_func(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, dest: E::VirtualAddress) {
        self.checking_func = true;
        ctrl.analyze_with_current_state(self, dest);
        if self.result.init_real_time_lighting.is_some() {
            self.result.init_real_time_lighting = Some(dest);
        }
        self.checking_func = false;
        ctrl.end_analysis();
    }
}

struct FindImagesLoaded<'acx, 'e, E: ExecutionState<'e>> {
    result: EntryOf<(Operand<'e>, E::VirtualAddress)>,
    load_images: E::VirtualAddress,
    conditions: BumpVec<'acx, (E::VirtualAddress, Operand<'e>, E::VirtualAddress)>,
}

impl<'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindImagesLoaded<'acx, 'e, E> {
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
                            .map(|x| (x.1, x.2));
                        if let Some((cond, to)) = cond {
                            let cond = if_arithmetic_eq_neq(cond)
                                .map(|(l, r, _)| (l, r))
                                .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                                .filter(|x| x.if_mem8().is_some());
                            if let Some(cond) = cond {
                                self.result = EntryOf::Ok((cond, to));
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        self.result = EntryOf::Stop;
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let to = ctrl.resolve(to);
                if let Some(to) = to.if_constant().map(E::VirtualAddress::from_u64) {
                    self.conditions.push((ctrl.address(), ctrl.resolve(condition), to));
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn local_player_name<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    relocs: &[E::VirtualAddress],
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    #[allow(bad_style)]
    let VA_SIZE: u32 = E::VirtualAddress::SIZE;

    let mut vtables =
        crate::vtables::vtables(analysis, functions, b".?AVCreateGameScreen@glues@@\0");
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let vtable_lengths = vtables.iter().map(|&addr| {
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
    });
    let mut vtable_lengths = BumpVec::from_iter_in(vtable_lengths, bump);
    for i in (0..vtables.len()).rev() {
        if vtable_lengths[i] < 0x30 {
            vtable_lengths.swap_remove(i);
            vtables.swap_remove(i);
        }
    }
    let highest_length = vtable_lengths.iter().max()?;
    let mut acceptable_funcs = bumpvec_with_capacity(0x20, bump);
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
        if single_result_assign(analyzer.result, &mut result) {
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

pub(crate) fn init_game_network<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    local_storm_player: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let vtables = crate::vtables::vtables(analysis, functions, b".?AVGameLobbyScreen@glues@@\0");
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
        if single_result_assign(analyzer.result, &mut result) {
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

pub(crate) fn lobby_state<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    process_lobby_commands_switch: &CompleteSwitch<'e>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // Command 0x48 compares state == 8 at start of the function
    let branch = process_lobby_commands_switch.branch(binary, 0x48)?;
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

pub(crate) fn init_game<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    init_units: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> InitGame<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = InitGame {
        loaded_save: None,
        init_game: None,
    };

    let callers = functions.find_callers(analysis, init_units);
    let functions = functions.functions();
    for call in callers {
        let mut invalid_handle_cmps: BumpVec<'_, (E::VirtualAddress, _)> =
            bumpvec_with_capacity(8, bump);
        let val = entry_of_until(binary, functions, call, |entry| {
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

struct InitGameAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    invalid_handle_cmps: &'a mut BumpVec<'acx, (E::VirtualAddress, Operand<'e>)>,
    result: EntryOf<Operand<'e>>,
    init_units: E::VirtualAddress,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    InitGameAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                let cmp_invalid_handle = cond.iter_no_mem_addr()
                    .filter_map(|x| {
                        let (l, r) = x.if_arithmetic_eq()?;
                        r.if_constant().filter(|&c| c as u32 == u32::max_value())?;
                        Some(l)
                    })
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

pub(crate) fn create_game_dialog_vtbl_on_multiplayer_create<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    select_map_entry: E::VirtualAddress,
) -> Option<usize> {
    struct Analyzer<'a, 'e, E: ExecutionState<'e>> {
        arg_cache: &'a ArgCache<'e, E>,
        result: Option<usize>,
    }

    impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'a, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Call(dest) => {
                    let dest = ctrl.resolve(dest);
                    let offset = ctrl.if_mem_word(dest)
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_then(|(l, r)| {
                            ctrl.if_mem_word(l)
                                .filter(|&l| {
                                    l == self.arg_cache.on_entry(1) ||
                                        l.if_register().filter(|r| r.0 == 1).is_some()
                                })
                                .and_then(|_| r.if_constant())
                                .map(|x| x as usize)
                                .filter(|&x| x > 0x40)
                        });
                    if let Some(offset) = offset {
                        self.result = Some(offset);
                        ctrl.end_analysis();
                    }
                }
                _ => (),
            }
        }
    }
    // select_map_entry arg2 is CreateGameScreen; and it calls this relevant function
    // For some older versions it also has been arg ecx
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = Analyzer::<E> {
        result: None,
        arg_cache: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, select_map_entry);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub(crate) fn join_game<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    local_storm_id: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let local_storm_id = local_storm_id.if_memory()
        .and_then(|x| x.address.if_constant())
        .map(|x| E::VirtualAddress::from_u64(x))?;
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = functions.functions();
    let mut global_refs = functions.find_functions_using_global(analysis, local_storm_id);
    global_refs.sort_unstable_by_key(|x| x.func_entry);
    global_refs.dedup_by_key(|x| x.func_entry);
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    for global in global_refs {
        let new = entry_of_until(binary, funcs, global.use_address, |entry| {
            let mut analyzer = IsJoinGame::<E> {
                result: EntryOf::Retry,
                use_address: global.use_address,
                local_storm_id,
                arg_cache,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
        if let EntryOfResult::Ok(entry, ()) = new {
            if single_result_assign(Some(entry), &mut result) {
                break;
            }
        }
    }
    result
}

struct IsJoinGame<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    local_storm_id: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsJoinGame<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        if self.use_address >= address && self.use_address < ctrl.current_instruction_end() {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Call(_) => {
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                let ok = arg1.if_mem32()
                    .filter(|&val| val == self.arg_cache.on_entry(1))
                    .and_then(|_| arg4.if_constant())
                    .filter(|&c| c == self.local_storm_id.as_u64())
                    .is_some();
                if ok {
                    self.result = EntryOf::Ok(());
                }
                if matches!(self.result, EntryOf::Retry) == false {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}


pub(crate) fn snet_initialize_provider<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    choose_snp: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;

    let mut analyzer = FindSnetInitProvider::<E> {
        result: None,
        arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, choose_snp);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindSnetInitProvider<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSnetInitProvider<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let arg5 = ctrl.resolve(self.arg_cache.on_call(4));
                    let ok = Some(())
                        .filter(|()| arg1 == self.arg_cache.on_entry(0))
                        .and_then(|_| arg5.if_constant())
                        .is_some();
                    if ok {
                        self.result = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn chk_init_players<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    chk_callbacks: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut ownr_callback = None;
    for i in 0.. {
        let struct_size = if E::WORD_SIZE == MemAccessSize::Mem32 { 0xc } else { 0x10 };
        let section_id = binary.read_u32(chk_callbacks + i * struct_size).ok()?;
        if section_id == 0 {
            break;
        }
        if section_id == 0x524e574f {
            let callback = binary.read_address(chk_callbacks + i * struct_size + 4).ok()?;
            ownr_callback = Some(callback);
            break;
        }
    }
    let ownr_callback = ownr_callback?;

    let mut analyzer = FindChkInitPlayer::<E> {
        result: None,
        phantom: Default::default(),
        inlining: false,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, ownr_callback);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindChkInitPlayer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
    inlining: bool,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindChkInitPlayer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // Just check for a store to chk_init_players.type
        // Mem8[chk_init_players + x * 0x24 + 0x8]
        // It is also looped from reverse, so the index is actually end_type - 24 * x
        match *op {
            Operation::Move(DestOperand::Memory(dest), val, None) => {
                if !self.inlining && dest.size == MemAccessSize::Mem8 {
                    let val = ctrl.resolve(val);
                    if val.if_mem8().is_some() {
                        let addr = ctrl.resolve(dest.address);
                        let ctx = ctrl.ctx();
                        let result = addr.if_constant()
                            .and_then(|x| Some(ctx.constant(x.checked_sub(0x24 * 11 + 8)?)));
                        if single_result_assign(result, &mut self.result) {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        self.inlining = false;
                        ctrl.skip_operation();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn original_chk_player_types<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    chk_init_players: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let chk_init_players = chk_init_players.if_constant()
        .map(|x| E::VirtualAddress::from_u64(x))?;
    let mut global_refs = functions.find_functions_using_global(analysis, chk_init_players);
    global_refs.sort_unstable_by_key(|x| x.func_entry);
    global_refs.dedup_by_key(|x| x.func_entry);
    let funcs = functions.functions();
    let arg_cache = &analysis.arg_cache;
    let mut result = None;
    for global in &global_refs {
        let new_result = entry_of_until(binary, funcs, global.use_address, |entry| {
            let mut analyzer = FindOrigPlayerTypes::<E> {
                result: EntryOf::Retry,
                arg_cache,
                use_address: global.use_address,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option();
        if single_result_assign(new_result, &mut result) {
            break;
        }
    }
    result
}

struct FindOrigPlayerTypes<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    use_address: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindOrigPlayerTypes<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.result = EntryOf::Stop;
        }
        // Command_48 does memcpy(original_chk_player_types, arg1 + 0x1f, 0xc)
        // (Well, not a memcpy call)
        match *op {
            Operation::Move(DestOperand::Memory(dest), val, None) => {
                let val = ctrl.resolve(val);
                let input_ok = val.if_memory()
                    .filter(|x| x.size == dest.size)
                    .and_then(|mem| mem.address.if_arithmetic_add_const(0x1f))
                    .filter(|&x| x == self.arg_cache.on_entry(0))
                    .is_some();
                if input_ok {
                    let addr = ctrl.resolve(dest.address);
                    self.result = EntryOf::Ok(addr);
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_load_images<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    load_images: E::VirtualAddress,
    load_dat: E::VirtualAddress,
    images_dat: (E::VirtualAddress, u32),
) -> LoadImagesAnalysis<'e, E::VirtualAddress> {
    let mut result = LoadImagesAnalysis {
        open_anim_single_file: None,
        open_anim_multi_file: None,
        init_skins: None,
        add_asset_change_cb: None,
        anim_asset_change_cb: None,
        base_anim_set: None,
        image_grps: None,
        image_overlays: None,
        fire_overlay_max: None,
        anim_struct_size: 0,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let images_dat_grp = match binary.read_address(images_dat.0 + images_dat.1 * 0x0) {
        Ok(o) => ctx.constant(o.as_u64()),
        Err(_) => return result,
    };
    // This isn't actually attack overlay, but can't bother to figure out which this is.
    let images_dat_attack_overlay = match binary.read_address(images_dat.0 + images_dat.1 * 0x9) {
        Ok(o) => ctx.constant(o.as_u64()),
        Err(_) => return result,
    };
    let mut analyzer = LoadImagesAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        load_dat,
        inline_depth: 0,
        inline_limit: 0,
        checking_init_skins: false,
        func_addr_to_return_custom: FxHashMap::with_capacity_and_hasher(32, Default::default()),
        custom_to_func_addr: bumpvec_with_capacity(32, &actx.bump),
        images_dat_grp,
        images_dat_attack_overlay,
        rdata: actx.binary_sections.rdata,
        text: actx.binary_sections.text,
        min_state: LoadImagesAnalysisState::BeforeLoadDat,
    };
    let exec = E::initial_state(ctx, binary);
    let state = LoadImagesAnalysisState::BeforeLoadDat;
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, load_images, exec, state);
    analysis.analyze(&mut analyzer);
    analyzer.finish(ctx, binary);
    result
}

struct LoadImagesAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut LoadImagesAnalysis<'e, E::VirtualAddress>,
    load_dat: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    inline_limit: u8,
    checking_init_skins: bool,
    images_dat_grp: Operand<'e>,
    images_dat_attack_overlay: Operand<'e>,
    func_addr_to_return_custom: FxHashMap<E::VirtualAddress, u32>,
    // Operand is this arg, set when open_anim_single_file candidate
    custom_to_func_addr: BumpVec<'acx, (E::VirtualAddress, Option<Operand<'e>>)>,
    rdata: &'a BinarySection<E::VirtualAddress>,
    text: &'a BinarySection<E::VirtualAddress>,
    min_state: LoadImagesAnalysisState,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum LoadImagesAnalysisState {
    // Move forward until past load_dat call
    BeforeLoadDat,
    // Finds open_anim_single_file(this = &base_anim_set[1], 0, 1, 1)
    // open_anim_multi_file(this = &base_anim_set[0], 0, 999, 1, 2, 1)
    // Inline to 1 depth load_images_aux, stop inlining if first there call
    // isn't func(_, "arr\\images.tbl", _, _, _)
    // + Start keeping track of func return values, don't inline other than load_images_aux
    FindOpenAnims,
    // Expected to be first call after open_anim_multi_file, recognized from "/skins" const str
    // access
    FindInitSkins,
    // add_asset_change_cb(&mut out_handle, func (0x14 bytes by value))
    // func.x4 (arg3) is anim_asset_change_cb
    FindAssetChangeCb,
    // load_grps(image_grps, images_dat_grp, &mut out, 999)
    // Single caller so some build may inline this??
    // Currently not handling that.
    FindImageGrps,
    // load_lo_set(&image_overlays[0], images_dat_attack_overlay, &mut out, 999)
    FindImageOverlays,
    // Stop inlining if inline depth == 1 (since FindOpenAnims)
    // Find move Mem8[x + undef] = x * 2
    FindFireOverlayMax,
}

impl analysis::AnalysisState for LoadImagesAnalysisState {
    fn merge(&mut self, newer: Self) {
        // Merge most to smallest state possible,
        // but there's code that skips past add_asset_change_cb so have an exception
        // to merge that to a higher state.
        if *self == LoadImagesAnalysisState::FindImageGrps &&
            newer == LoadImagesAnalysisState::FindAssetChangeCb
        {
            // Nothing
        } else if newer == LoadImagesAnalysisState::FindImageGrps &&
            *self == LoadImagesAnalysisState::FindAssetChangeCb
        {
            *self = newer;
        } else if *self > newer {
            *self = newer;
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    LoadImagesAnalyzer<'a, 'acx, 'e, E>
{
    type State = LoadImagesAnalysisState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *ctrl.user_state() {
            LoadImagesAnalysisState::BeforeLoadDat => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.load_dat {
                            *ctrl.user_state() = LoadImagesAnalysisState::FindOpenAnims;
                            self.min_state = LoadImagesAnalysisState::FindOpenAnims;
                        }
                    }
                }
            }
            LoadImagesAnalysisState::FindOpenAnims => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.inline_limit != 0 {
                            // Verify arg2 = arr\\images.tbl or exit
                            // Older versions used arg1
                            let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            let binary = ctrl.binary();
                            let cmp = b"arr\\images.tbl\0";
                            let cmp_len = cmp.len() as u32;
                            let ok = [arg2, arg1].iter().any(|&x| {
                                x.if_constant()
                                    .map(E::VirtualAddress::from_u64)
                                    .and_then(|x| binary.slice_from_address(x, cmp_len).ok())
                                    .filter(|&x| x == cmp)
                                    .is_some()
                            });
                            if ok {
                                self.inline_limit = 0;
                            } else {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                        let (new, ok) = self.check_open_anim_call(ctrl, dest);
                        if ok {
                            *ctrl.user_state() = LoadImagesAnalysisState::FindInitSkins;
                            self.min_state = LoadImagesAnalysisState::FindInitSkins;
                            return;
                        }
                        if self.inline_depth == 0 && new {
                            // Inline
                            self.inline_limit = 1;
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_limit = 0;
                            self.inline_depth = 0;
                            if self.result.open_anim_single_file.is_some() {
                                *ctrl.user_state() = LoadImagesAnalysisState::FindFireOverlayMax;
                                self.min_state = LoadImagesAnalysisState::FindFireOverlayMax;
                            }
                        }
                    }
                }
            }
            LoadImagesAnalysisState::FindInitSkins => {
                if self.checking_init_skins {
                    if let Operation::Move(_, val, None) = *op {
                        let val = ctrl.resolve(val);
                        let cmp = b"/skins";
                        let addr = if let Some(mem) = val.if_memory() {
                            mem.address
                        } else {
                            val
                        };
                        let binary = ctrl.binary();
                        let ok = addr.if_constant()
                            .map(E::VirtualAddress::from_u64)
                            .and_then(|x| binary.slice_from_address(x, cmp.len() as u32).ok())
                            .filter(|&x| x == cmp)
                            .is_some();
                        if ok {
                            self.result.init_skins = Some(E::VirtualAddress::from_u64(0));
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    if let Operation::Call(dest) = *op {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.checking_init_skins = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.checking_init_skins = false;
                            if self.result.init_skins.is_some() {
                                self.result.init_skins = Some(dest);
                                *ctrl.user_state() = LoadImagesAnalysisState::FindAssetChangeCb;
                                self.min_state = LoadImagesAnalysisState::FindAssetChangeCb;
                                return;
                            }
                        }
                    }
                    // Allow failure if init_skins is weird (old) or inlined
                    self.check_asset_change_cb(ctrl, op);
                }
            }
            LoadImagesAnalysisState::FindAssetChangeCb => {
                self.check_asset_change_cb(ctrl, op);
            }
            LoadImagesAnalysisState::FindImageGrps |
                LoadImagesAnalysisState::FindImageOverlays =>
            {
                // load_grps(image_grps, images_dat_grp, &mut out, 999)
                // load_lo_set(&image_overlays[0], images_dat_attack_overlay, &mut out, 999)
                if let Operation::Call(_) = *op {
                    let is_find_grps =
                        *ctrl.user_state() == LoadImagesAnalysisState::FindImageGrps;
                    let dat_arr = match is_find_grps {
                        true => self.images_dat_grp,
                        false => self.images_dat_attack_overlay,
                    };
                    let result = Some(())
                        .and_then(|_| ctrl.resolve(self.arg_cache.on_call(3)).if_constant())
                        .filter(|&c| c == 999)
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                        .filter(|&x| x == dat_arr)
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(0)));
                    if let Some(result) = result {
                        if is_find_grps {
                            self.result.image_grps = Some(result);
                            *ctrl.user_state() = LoadImagesAnalysisState::FindImageOverlays;
                            self.min_state = LoadImagesAnalysisState::FindImageOverlays;
                        } else {
                            self.result.image_overlays = Some(result);
                            *ctrl.user_state() = LoadImagesAnalysisState::FindFireOverlayMax;
                            self.min_state = LoadImagesAnalysisState::FindFireOverlayMax;
                            if self.inline_depth != 0 {
                                // Go back to outer load_images
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            LoadImagesAnalysisState::FindFireOverlayMax => {
                if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if mem.size == MemAccessSize::Mem8 {
                        let value = ctrl.resolve(value);
                        let ok = value.if_arithmetic_and_const(0xfe)
                            .or_else(|| Some(value))
                            .and_then(|x| x.if_arithmetic_mul_const(0x2))
                            .is_some();
                        if ok {
                            let dest = ctrl.resolve(mem.address);
                            let base = dest.if_arithmetic_add()
                                .and_if_either_other(|x| x.is_undefined());
                            if let Some(base) = base {
                                self.result.fire_overlay_max = Some(base);
                            }
                        }
                    }
                }
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if *ctrl.user_state() < self.min_state {
            ctrl.end_branch();
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> LoadImagesAnalyzer<'a, 'acx, 'e, E> {
    /// First bool is true if the func hadn't been seen before,
    /// second is true when result was found.
    fn check_open_anim_call(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        func: E::VirtualAddress,
    ) -> (bool, bool) {
        let entry = self.func_addr_to_return_custom.entry(func);
        let ctx = ctrl.ctx();
        if let Entry::Occupied(ref e) = entry {
            let &val = e.get();
            let custom = ctx.custom(val);
            ctrl.do_call_with_result(custom);
            return (false, false);
        }

        let idx = self.custom_to_func_addr.len() as u32;
        entry.or_insert(idx);
        let custom = ctx.custom(idx);
        let result = self.check_new_open_anim_call(ctrl, func);
        ctrl.do_call_with_result(custom);
        result
    }

    fn check_new_open_anim_call(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        func: E::VirtualAddress,
    ) -> (bool, bool) {
        // open_anim_single_file(this = &base_anim_set[1], 0, 1, 1)
        // open_anim_multi_file(this = &base_anim_set[0], 0, 999, 1, 2, 1)
        let ctx = ctrl.ctx();
        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
        let is_single_file = arg1.if_constant().filter(|&c| c == 0)
            .and_then(|_| arg2.if_constant().filter(|&c| c == 1))
            .and_then(|_| arg3.if_constant().filter(|&c| c == 1))
            .is_some();
        let this = ctrl.resolve(ctx.register(1));
        if is_single_file {
            self.custom_to_func_addr.push((func, Some(this)));
            return (true, false);
        }
        self.custom_to_func_addr.push((func, None));
        let is_multi_file_1 = arg1.if_constant().filter(|&c| c == 0)
            .and_then(|_| arg2.if_constant().filter(|&c| c == 999))
            .and_then(|_| arg3.if_constant().filter(|&c| c == 1))
            .is_some();
        if is_multi_file_1 {
            let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
            let arg5 = ctrl.resolve(self.arg_cache.on_call(4));
            let is_multi_file = arg4.if_constant().filter(|&c| c == 2)
                .and_then(|_| arg5.if_constant().filter(|&c| c == 1))
                .is_some();
            if is_multi_file {
                let (base, off) = Operand::const_offset(this, ctx)
                    .unwrap_or_else(|| (this, 0));
                let single_file = self.custom_to_func_addr.iter().rev()
                    .find_map(|&(addr, single_this)| {
                        let single_this = single_this?;
                        let (base2, off2) = Operand::const_offset(single_this, ctx)?;
                        if base == base2 && off2 > off {
                            let diff = u16::try_from(off2 - off).ok()?;
                            Some((addr, diff))
                        } else {
                            None
                        }
                    });
                if let Some((single_file, struct_size)) = single_file {
                    self.result.open_anim_single_file = Some(single_file);
                    self.result.open_anim_multi_file = Some(func);
                    self.result.anim_struct_size = struct_size;
                    self.result.base_anim_set = Some(this);
                    return (true, true);
                }
            }
        }
        (true, false)
    }

    /// Checks if this, arg1 makes the function call to seem like a copy, and if yes,
    /// simulate the copy
    fn check_simulate_func_copy(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        this: Operand<'e>,
        arg1: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        // Dest.vtable == 0 or 1
        let is_copy = ctrl.resolve(ctrl.mem_word(this))
            .if_constant()
            .filter(|&c| c <= 1)
            .is_some();
        if is_copy {
            let vtbl = ctrl.resolve_va(ctrl.mem_word(arg1));
            let param = ctrl.resolve_va(ctrl.mem_word(
                ctrl.const_word_offset(arg1, 1)
            ));
            if let (Some(vtbl), Some(param)) = (vtbl, param) {
                // Copy vtbl and param to this
                let dest = ctrl.mem_word(this);
                let dest2 =
                    ctrl.mem_word(ctrl.const_word_offset(this, 1));
                let state = ctrl.exec_state();
                let vtbl = ctx.constant(vtbl.as_u64());
                let param = ctx.constant(param.as_u64());
                state.move_to(&DestOperand::from_oper(dest), vtbl);
                state.move_to(&DestOperand::from_oper(dest2), param);
                if E::VirtualAddress::SIZE == 4 {
                    // Also assuming that func copy is stdcall
                    let esp = ctrl.resolve(ctx.register(4));
                    let state = ctrl.exec_state();
                    state.move_to(
                        &scarf::DestOperand::Register64(scarf::operand::Register(4)),
                        ctx.add_const(esp, 4),
                    );
                }
            }
        }
    }

    fn check_asset_change_cb(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        if let Operation::Call(dest) = *op {
            let ctx = ctrl.ctx();
            let dest = ctrl.resolve(dest);
            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
            if let Some(dest) = dest.if_constant() {
                let dest = E::VirtualAddress::from_u64(dest);
                let this = ctrl.resolve(ctx.register(1));
                let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                // Check for add_asset_change_cb(&local, func_vtbl, func_cb, ...)
                let asset_change_cb = arg2.if_constant()
                    .map(E::VirtualAddress::from_u64)
                    .filter(|&x| is_in_section(self.rdata, x))
                    .and_then(|_| arg3.if_constant())
                    .map(E::VirtualAddress::from_u64)
                    .filter(|&x| is_in_section(self.text, x))
                    .or_else(|| {
                        // Alt function struct:
                        // a2 - vtable *func_impl
                        // a3 - vtable
                        // a4 - param
                        arg3.if_constant()
                            .map(E::VirtualAddress::from_u64)
                            .filter(|&x| is_in_section(self.rdata, x))?;
                        let param = ctrl.resolve(self.arg_cache.on_call(3))
                            .if_constant()
                            .map(E::VirtualAddress::from_u64)
                            .filter(|&x| is_in_section(self.text, x))?;
                        let arg3_loc = self.arg_cache.on_call(2).if_memory()?.address;
                        if arg2 != ctrl.resolve(arg3_loc) {
                            None
                        } else {
                            Some(param)
                        }
                    });
                if let Some(cb) = asset_change_cb {
                    self.result.add_asset_change_cb = Some(dest);
                    self.result.anim_asset_change_cb = Some(cb);
                    *ctrl.user_state() = LoadImagesAnalysisState::FindImageGrps;
                    self.min_state = LoadImagesAnalysisState::FindImageGrps;
                    return;
                }
                self.check_simulate_func_copy(ctrl, this, arg1);
            } else if E::VirtualAddress::SIZE == 4 {
                let is_vtable_fn = ctrl.if_mem_word(dest)
                    .and_then(|x| x.if_constant())
                    .map(E::VirtualAddress::from_u64)
                    .filter(|&x| is_in_section(self.rdata, x))
                    .is_some();
                if is_vtable_fn && arg1 == ctx.const_0() {
                    // Assuming to be func.vtable.delete(0), add 4 to esp to
                    // simulate stdcall
                    let esp = ctrl.resolve(ctx.register(4));
                    let state = ctrl.exec_state();
                    state.move_to(
                        &scarf::DestOperand::Register64(scarf::operand::Register(4)),
                        ctx.add_const(esp, 4),
                    );
                }
            }
            ctrl.skip_call_preserve_esp();
        }
    }

    fn finish(&mut self, ctx: OperandCtx<'e>, binary: &'e BinaryFile<E::VirtualAddress>) {
        let mut ops = [
            &mut self.result.base_anim_set,
            &mut self.result.image_grps,
            &mut self.result.image_overlays,
            &mut self.result.fire_overlay_max,
        ];
        let funcs = &self.custom_to_func_addr;
        for ref mut op in ops.iter_mut() {
            if let Some(ref mut op) = *op {
                *op = ctx.transform(*op, 8, |op| {
                    if let Some(idx) = op.if_custom() {
                        let (func, _) = funcs[idx as usize];
                        crate::call_tracker::analyze_func_return::<E>(func, ctx, binary)
                    } else {
                        None
                    }
                });
            }
        }
        // open_anim_multi_file may be simple wrapper calling actual
        // open_anim_multi_file(this, a1, a2, a3, a4, a5, &out_unused)
        if let Some(func) = self.result.open_anim_multi_file {
            if let Some(actual) =
                check_actual_open_anim_multi_file(func, ctx, binary, self.arg_cache)
            {
                self.result.open_anim_multi_file = Some(actual);
            }
        }
    }
}

/// Check if first call of `func` takes this and 5 other arguments to this function.
/// If yes, return that child function.
fn check_actual_open_anim_multi_file<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    arg_cache: &ArgCache<'e, E>,
) -> Option<E::VirtualAddress> {
    struct Analyzer<'a, 'e, E: ExecutionState<'e>> {
        result: Option<E::VirtualAddress>,
        arg_cache: &'a ArgCache<'e, E>,
    }

    impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'a, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Jump { .. } = *op {
                ctrl.end_analysis();
                return;
            }
            if let Operation::Call(dest) = *op {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ctx = ctrl.ctx();
                    if ctx.register(1) == ctrl.resolve(ctx.register(1)) {
                        if (0..5).all(|i| {
                            self.arg_cache.on_entry(i) == ctrl.resolve(self.arg_cache.on_call(i))
                        }) {
                            self.result = Some(dest);
                        }
                    }
                }
                ctrl.end_analysis();
            }
        }
    }
    let mut analyzer = Analyzer::<E> {
        result: None,
        arg_cache,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn is_in_section<Va: VirtualAddress>(section: &BinarySection<Va>, addr: Va) -> bool {
    section.virtual_address <= addr && section.virtual_address + section.virtual_size > addr
}

pub(crate) fn analyze_game_loop<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    game_loop: E::VirtualAddress,
    game: Operand<'e>,
) -> GameLoopAnalysis<'e, E::VirtualAddress> {
    let mut result = GameLoopAnalysis {
        set_music: None,
        step_network: None,
        render_screen: None,
        step_game_loop: None,
        step_game_logic: None,
        process_events: None,
        load_pcx: None,
        main_palette: None,
        palette_set: None,
        tfontgam: None,
        sync_data: None,
        sync_active: None,
        menu_screen_id: None,
        continue_game_loop: None,
        anti_troll: None,
        step_game_frames: None,
        next_game_step_tick: None,
        replay_seek_frame: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = GameLoopAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        game,
        state: GameLoopAnalysisState::SetMusic,
        inline_depth: 0,
        inline_limit: 0,
        sync_active_candidate: None,
        step_game_loop_inlined: false,
        step_game_loop_first_cond_jump: true,
        current_entry: game_loop,
        step_game_loop_analysis_start: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_loop);
    analysis.analyze(&mut analyzer);
    if let Some(step_game_loop) = analyzer.step_game_loop_analysis_start {
        let mut analyzer = StepGameLoopAnalyzer::<E> {
            result: &mut result,
            game,
            next_call_custom: 0x1000,
            state: StepGameLoopAnalysisState::NextGameStepTick,
            inlining: false,
            current_entry: None,
            inline_limit: 0,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, step_game_loop);
        analysis.analyze(&mut analyzer);
    }
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum GameLoopAnalysisState {
    // Search for call with a1 = game.music
    // Inline to 1 deep. Any later analysis is based on inline level of
    // this set_music call.
    // Also worth noting that this call is slightly different from analysis's set_music,
    // which has does call something else first (Briefing fades music out first).
    SetMusic,
    // Move of 1 to Mem8. Hopefully no conflicts.
    ContinueGameLoop,
    // Search for memcpy(palette_set[0], main_palette, 0x400)
    // Inline once if a1 == 0 and a2 == 0x100 set_palette(idx, entry_count, source)
    PaletteCopy,
    // Search for storm_load_pcx("game\\tFontGam.pcx", 0, out, 0xc0, 0, 0, 0)
    // Should be right after set_palette.
    // Inline once.
    // I'm assuming that the pcx may be removed at some point, so switch to next state
    // quickly if it doesn't get found.
    TfontGam,
    // Inline deep 1 for enable_sync(1), and deep 2 unconditionally when there's sync_active
    // candidate.
    // Find memset(sync_data, 0, 0x10c0), sync_active is a global that gets set to 1 before that.
    SyncData,
    // Recognize StepNetwork from it immediately comparing menu_screen_id == 21 (Or more)
    StepNetwork,
    // Recognize render_screen(&[funcptr], 1)
    RenderScreen,
    // Find comparision against continue_game_loop != 0, inline once
    StepGameLoop,
    // If the first call has arg1 = 3, step_game_loop got inlined and it is call
    // to process_events.
    // Otherwise iniline once and expect the first function to be call to process_events(3).
    StepGameLoopAfterContinue,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepGameLoopAnalysisState {
    // Find (current_tick - next_tick) < 0 jump
    // Call results are made Custom(x) so current_tick should be custom.
    // Due to it being signed comparision it shows up as a sign bit check condition.
    NextGameStepTick,
    StepGame,
    StepGameFrames,
}

struct GameLoopAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut GameLoopAnalysis<'e, E::VirtualAddress>,
    game: Operand<'e>,
    arg_cache: &'a ArgCache<'e, E>,
    state: GameLoopAnalysisState,
    inline_depth: u8,
    inline_limit: u8,
    sync_active_candidate: Option<Operand<'e>>,
    step_game_loop_inlined: bool,
    step_game_loop_first_cond_jump: bool,
    current_entry: E::VirtualAddress,
    // Address to start analyzing step_game_loop.
    // In middle of function, but should be fine as it does not take arguments.
    step_game_loop_analysis_start: Option<E::VirtualAddress>,
}

struct StepGameLoopAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut GameLoopAnalysis<'e, E::VirtualAddress>,
    game: Operand<'e>,
    next_call_custom: u32,
    state: StepGameLoopAnalysisState,
    inlining: bool,
    current_entry: Option<E::VirtualAddress>,
    inline_limit: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for GameLoopAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let arg_cache = self.arg_cache;
        match self.state {
            GameLoopAnalysisState::SetMusic => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(arg_cache.on_call(0));
                        let ok = arg1.if_mem16()
                            .and_then(|x| x.if_arithmetic_add_const(0xee))
                            .filter(|&x| x == self.game)
                            .is_some();
                        if ok {
                            self.result.set_music = Some(dest);
                            self.inline_depth = 0;
                            self.inline_limit = 0;
                            self.state = GameLoopAnalysisState::ContinueGameLoop;
                            ctrl.analyze_with_current_state(self, ctrl.current_instruction_end());
                            ctrl.end_analysis();
                        } else if self.inline_depth == 0 {
                            self.inline_limit = 2;
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            self.inline_limit = 0;
                            if self.result.set_music.is_some() {
                                ctrl.end_analysis();
                            }
                        } else {
                            if self.inline_limit == 0 {
                                ctrl.end_analysis();
                            } else {
                                self.inline_limit -= 1;
                            }
                        }
                    }
                }
            }
            GameLoopAnalysisState::ContinueGameLoop => {
                if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if mem.size == MemAccessSize::Mem8 && ctrl.resolve(value) == ctx.const_1() {
                        self.result.continue_game_loop =
                            Some(ctx.mem8(ctrl.resolve(mem.address)));
                        self.state = GameLoopAnalysisState::PaletteCopy;
                    }
                }
            }
            GameLoopAnalysisState::PaletteCopy => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(arg_cache.on_call(0));
                        let arg2 = ctrl.resolve(arg_cache.on_call(1));
                        let arg3 = ctrl.resolve(arg_cache.on_call(2));
                        if arg3.if_constant() == Some(0x400) {
                            self.result.palette_set = Some(arg1);
                            self.result.main_palette = Some(arg2);
                            self.state = GameLoopAnalysisState::TfontGam;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                        } else if self.inline_depth == 0 {
                            if arg1 == ctx.const_0() && arg2.if_constant() == Some(0x100) {
                                self.inline_limit = 3;
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                self.inline_limit = 0;
                            }
                        } else {
                            if self.inline_limit == 0 {
                                ctrl.end_analysis();
                            } else {
                                self.inline_limit -= 1;
                            }
                        }
                    }
                }
            }
            GameLoopAnalysisState::TfontGam => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let zero = ctx.const_0();
                        let binary = ctrl.binary();
                        // Search for storm_load_pcx("game\\tFontGam.pcx", 0, out, 0xc0, 0, 0, 0)
                        let ok = [1, 4, 5, 6].iter()
                            .all(|&x| ctrl.resolve(arg_cache.on_call(x)) == zero) &&
                            ctrl.resolve(arg_cache.on_call(3)).if_constant() == Some(0xc0) &&
                            ctrl.resolve_va(arg_cache.on_call(0))
                                .filter(|&x| is_casei_cstring(binary, x, b"game\\tfontgam.pcx"))
                                .is_some();
                        if ok {
                            self.result.load_pcx = Some(dest);
                            self.result.tfontgam = Some(ctrl.resolve(arg_cache.on_call(2)));
                            self.state = GameLoopAnalysisState::SyncData;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                        } else if self.inline_depth == 0 {
                            self.inline_limit = 3;
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            self.inline_limit = 0;
                            // If it wasn't found after first inline, assume it doesn't exist
                            self.state = GameLoopAnalysisState::SyncData;
                        } else {
                            if self.inline_limit == 0 {
                                ctrl.end_analysis();
                            } else {
                                self.inline_limit -= 1;
                            }
                        }
                    }
                }
            }
            GameLoopAnalysisState::SyncData => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if let Some(sync_active) = self.sync_active_candidate {
                            // Check memset(sync_data, 0, 0x10c0)
                            let ok = ctrl.resolve(arg_cache.on_call(1)) == ctx.const_0() &&
                                ctrl.resolve(arg_cache.on_call(2)).if_constant() == Some(0x10c0);
                            if ok {
                                self.result.sync_active = Some(sync_active);
                                self.result.sync_data = Some(ctrl.resolve(arg_cache.on_call(0)));
                                self.state = GameLoopAnalysisState::StepNetwork;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                                return;
                            }
                        }

                        if self.inline_depth != 0 {
                            if self.inline_limit == 0 {
                                ctrl.end_analysis();
                                return;
                            } else {
                                self.inline_limit -= 1;
                            }
                        }
                        let inline = self.sync_active_candidate.is_some() ||
                            (self.inline_depth == 0 &&
                                ctrl.resolve(self.arg_cache.on_call(0)) == ctx.const_1());
                        if inline {
                            if self.inline_depth == 0 {
                                self.inline_limit = 4;
                            }
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.inline_depth == 0 {
                                self.inline_limit = 0;
                            } else if self.state == GameLoopAnalysisState::StepNetwork {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if ctrl.resolve(value) == ctx.const_1() {
                        let address = ctrl.resolve(mem.address);
                        if address.if_constant().is_some() {
                            self.sync_active_candidate =
                                Some(ctx.mem_variable_rc(mem.size, address));
                        }
                    }
                }
            }
            GameLoopAnalysisState::StepNetwork => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let binary = ctrl.binary();
                        let mut analysis = FuncAnalysis::new(binary, ctx, dest);
                        let mut analyzer = IsStepNetwork::<E> {
                            menu_screen_id: None,
                            inlining: false,
                            phantom: Default::default(),
                        };
                        analysis.analyze(&mut analyzer);
                        if let Some(menu_screen_id) = analyzer.menu_screen_id {
                            self.result.step_network = Some(dest);
                            self.result.menu_screen_id = Some(menu_screen_id);
                            self.state = GameLoopAnalysisState::RenderScreen;
                        }
                    }
                }
            }
            GameLoopAnalysisState::RenderScreen => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if ctrl.resolve(arg_cache.on_call(1)) == ctx.const_1() {
                            let arg1 = ctrl.resolve(arg_cache.on_call(0));
                            let ok = ctrl.read_memory(arg1, E::WORD_SIZE)
                                .if_constant()
                                .filter(|&va| va >= ctrl.binary().base().as_u64())
                                .is_some();
                            if ok {
                                self.result.render_screen = Some(dest);
                                if let Some(continue_loop) = self.result.continue_game_loop {
                                    let state = ctrl.exec_state();
                                    state.move_resolved(
                                        &DestOperand::from_oper(continue_loop),
                                        ctx.custom(0),
                                    );
                                    self.state = GameLoopAnalysisState::StepGameLoop;
                                    ctrl.analyze_with_current_state(
                                        self,
                                        ctrl.current_instruction_end(),
                                    );
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            GameLoopAnalysisState::StepGameLoop => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if condition != ctx.const_1() && self.step_game_loop_first_cond_jump {
                        self.step_game_loop_first_cond_jump = false;
                        return;
                    }
                    if let Some(jump_if_zero) = if_arithmetic_eq_neq(condition)
                        .filter(|x| {
                            x.1 == ctx.const_0() &&
                                Operand::and_masked(x.0).0.if_custom() == Some(0)
                        })
                        .map(|x| x.2)
                    {
                        self.state = GameLoopAnalysisState::StepGameLoopAfterContinue;
                        let addr = match jump_if_zero {
                            true => ctrl.current_instruction_end(),
                            false => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => {
                                    ctrl.end_analysis();
                                    return;
                                }
                            },
                        };
                        self.inline_depth = 0;
                        ctrl.analyze_with_current_state(self, addr);
                        ctrl.end_analysis();
                    }
                }
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if Some(dest) == self.result.step_network {
                            ctrl.end_branch();
                            return;
                        }
                        // Only inline once
                        if !self.step_game_loop_inlined {
                            self.step_game_loop_inlined = true;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.process_events.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            GameLoopAnalysisState::StepGameLoopAfterContinue => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if ctrl.resolve(self.arg_cache.on_call(0)).if_constant() == Some(3) {
                            self.result.process_events = Some(dest);
                            if self.inline_depth != 0 {
                                self.result.step_game_loop = Some(self.current_entry);
                            }
                            self.step_game_loop_analysis_start =
                                Some(ctrl.current_instruction_end());
                            ctrl.end_analysis();
                        } else {
                            if self.inline_depth == 0 {
                                self.inline_depth = 1;
                                self.current_entry = dest;
                                ctrl.analyze_with_current_state(self, dest);
                                ctrl.end_analysis();
                            } else {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StepGameLoopAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepGameLoopAnalysisState::NextGameStepTick => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1 == ctx.const_0())
                        .and_then(|x| {
                            let (l, r) = x.0.if_arithmetic_and_const(0x8000_0000)?
                                .if_arithmetic_sub()?;
                            l.if_custom()?;
                            Some((r, x.2))
                        });
                    if let Some((next_tick, jump_to_do_step)) = result {
                        self.result.next_game_step_tick = Some(next_tick);
                        let continue_pos = match jump_to_do_step {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        self.state = StepGameLoopAnalysisState::StepGame;
                        ctrl.analyze_with_current_state(self, continue_pos);
                        ctrl.end_analysis();
                    }
                } else if let Operation::Call(..) = *op {
                    // Don't use default call retval for these, as undefined ends up
                    // being a poor choice due to its special handling value merging.
                    ctrl.do_call_with_result(ctx.custom(self.next_call_custom));
                    self.next_call_custom += 1;
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    // Skip stores that may be to next_game_step_tick
                    let value = ctrl.resolve(value);
                    if value.if_custom().is_some() && is_global(ctrl.resolve(mem.address)) {
                        ctrl.skip_operation();
                    }
                }
            }
            StepGameLoopAnalysisState::StepGame => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if !self.inlining {
                            self.inlining = true;
                            self.current_entry = Some(dest);
                            self.inline_limit = 10;
                            ctrl.inline(self, dest);
                            ctrl.skip_operation();
                            self.inline_limit = 0;
                            self.current_entry = None;
                            self.inlining = false;
                            if self.result.replay_seek_frame.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if self.result.anti_troll.is_none() {
                        let anti_troll = if_arithmetic_eq_neq(condition)
                            .filter(|x| x.1 == ctx.const_0())
                            .and_then(|x| x.0.if_mem8())
                            .map(|x| ctx.sub_const(x, 0x1a));
                        self.result.anti_troll = anti_troll;
                    }
                    // Check for game.frame_count >= replay_seek_frame
                    // (x >= y should be (x > y) | (x == y)
                    let replay_seek_frame = condition.if_arithmetic_or()
                        .and_either(|x| x.if_arithmetic_eq())
                        .map(|x| x.0)
                        .and_either_other(|x| {
                            x.if_mem32()
                                .and_then(|x| x.if_arithmetic_add_const(0x14c))
                                .filter(|&x| x == self.game)
                        });
                    if let Some(replay_seek_frame) = replay_seek_frame {
                        self.result.step_game_logic = self.current_entry;
                        self.result.replay_seek_frame = Some(replay_seek_frame);
                        self.state = StepGameLoopAnalysisState::StepGameFrames;
                        if let Some(to) = ctrl.resolve_va(to) {
                            ctrl.analyze_with_current_state(self, to);
                        }
                        ctrl.end_analysis();
                    } else if self.inlining {
                        if self.inline_limit == 0 {
                            ctrl.end_analysis();
                        } else {
                            self.inline_limit -= 1;
                        }
                    }
                }
            }
            StepGameLoopAnalysisState::StepGameFrames => {
                if let Operation::Move(_, value, None) = *op {
                    let value = ctrl.resolve(value);
                    if let Some(val) = value.if_arithmetic_sub_const(1) {
                        self.result.step_game_frames = Some(val);
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

/// Return true if all parts of operand are constants/arith
fn is_global(op: Operand<'_>) -> bool {
    if op.if_constant().is_some() {
        true
    } else if let OperandType::Arithmetic(arith) = op.ty() {
        // Nicer for tail calls to check right first as it doesn't recurse in operand chains
        is_global(arith.right) && is_global(arith.left)
    } else if let OperandType::Memory(ref mem) = op.ty() {
        is_global(mem.address)
    } else {
        false
    }
}

fn is_casei_cstring<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    address: Va,
    cmp: &[u8],
) -> bool {
    binary.slice_from_address(address, cmp.len() as u32 + 1).ok()
        .and_then(|x| {
            let (&zero, text) = x.split_last()?;
            if zero == 0 && text.eq_ignore_ascii_case(cmp) {
                Some(())
            } else {
                None
            }
        })
        .is_some()
}

struct IsStepNetwork<'e, E: ExecutionState<'e>> {
    menu_screen_id: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStepNetwork<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if !self.inlining {
                        self.inlining = true;
                        ctrl.inline(self, dest);
                        self.inlining = false;
                        ctrl.skip_operation();
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                // Recognize step_network from its first comparision being
                // menu_screen_id == MENU_SCREEN_EXIT (0x21 currently,
                // but allow matching higher constants, 1.16.1 had 0x19)
                let condition = ctrl.resolve(condition);
                let menu_screen_id = if_arithmetic_eq_neq(condition)
                    .map(|(l, r, _)| (l, r))
                    .and_either_other(|x| x.if_constant().filter(|&c| c > 0x20 && c < 0x80))
                    .filter(|x| {
                        x.iter().all(|op| !op.is_undefined() && op.if_register().is_none())
                    });
                if let Some(menu_screen_id) = menu_screen_id {
                    self.menu_screen_id = Some(menu_screen_id);
                }
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_process_events<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    process_events: E::VirtualAddress,
) -> ProcessEventsAnalysis<'e, E::VirtualAddress> {
    let mut result = ProcessEventsAnalysis {
        bnet_controller: None,
        step_bnet_controller: None,
        bnet_message_switch: None,
        message_vtable_type: 0,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut analyzer = ProcessEventsAnalyzer::<E> {
        result: &mut result,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, process_events);
    analysis.analyze(&mut analyzer);
    result
}

struct ProcessEventsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ProcessEventsAnalysis<'e, E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for ProcessEventsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let ctx = ctrl.ctx();
                let ecx = ctrl.resolve(ctx.register(1));
                if is_global(ecx) {
                    let binary = ctrl.binary();
                    let mut analyzer = IsStepBnetController::<E> {
                        result: self.result,
                        state: StepBnetControllerState::FindServiceStep,
                        inline_depth: 0,
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, dest);
                    analysis.analyze(&mut analyzer);
                    if analyzer.state != StepBnetControllerState::FindServiceStep {
                        self.result.bnet_controller = Some(ecx);
                        self.result.step_bnet_controller = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepBnetControllerState {
    FindServiceStep,
    FindEvents,
}

struct IsStepBnetController<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ProcessEventsAnalysis<'e, E::VirtualAddress>,
    state: StepBnetControllerState,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStepBnetController<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepBnetControllerState::FindServiceStep => {
                if let Operation::Call(dest) = *op {
                    let dest = ctrl.resolve(dest);
                    // Check for this.services[0].vtable.step()
                    let ok = ctrl.if_mem_word(dest)
                        .and_then(|x| {
                            let x = x.struct_offset().0;
                            let x = ctrl.if_mem_word(ctrl.if_mem_word(ctrl.if_mem_word(x)?)?)?;
                            let x = x.struct_offset().0;
                            match x == ctx.register(1) {
                                true => Some(()),
                                false => None,
                            }
                        })
                        .is_some();
                    if ok {
                        self.state = StepBnetControllerState::FindEvents;
                        ctrl.analyze_with_current_state(self, ctrl.address());
                        ctrl.end_analysis();
                    }
                }
            }
            StepBnetControllerState::FindEvents => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ctx.register(1));
                        let ok = ctrl.if_mem_word(this)
                            .and_then(|x| {
                                let x = ctrl.if_mem_word(x)?;
                                let x = x.struct_offset().0;
                                match x == ctx.register(1) {
                                    true => Some(()),
                                    false => None,
                                }
                            })
                            .is_some();
                        if ok && self.inline_depth < 3 {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.bnet_message_switch.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    } else {
                        if let Some(addr) = ctrl.if_mem_word(dest) {
                            let offset = addr.struct_offset().1;
                            ctrl.do_call_with_result(ctx.custom(offset));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    if ctrl.resolve(condition) == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        if let Some(to) = ctrl.if_mem_word(to) {
                            let exec_state = ctrl.exec_state();
                            if let Some(switch) = CompleteSwitch::new(to, exec_state) {
                                if let Some(idx) = switch.index_operand::<E::VirtualAddress>() {
                                    if let Some(vtable_offset) = idx.if_custom() {
                                        self.result.bnet_message_switch = Some(switch);
                                        self.result.message_vtable_type = vtable_offset as u16;
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Move(ref dest, value, None) = *op {
                    // Skips moves of val.x4 = val to prevent some the analysis
                    // from assuming that a binary tree stays empty
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == E::WORD_SIZE {
                            let addr = ctrl.resolve(mem.address);
                            let value = ctrl.resolve(value);
                            if addr == ctx.add_const(value, E::VirtualAddress::SIZE as u64) {
                                let state = ctrl.exec_state();
                                state.move_to(dest, ctx.new_undef());
                                ctrl.skip_operation();
                            }
                        }
                    }
                }
            }
        }
    }
}
