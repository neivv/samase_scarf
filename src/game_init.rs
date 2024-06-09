use std::collections::hash_map::Entry;

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use scarf::{DestOperand, MemAccess, Operand, OperandCtx, Operation, BinaryFile, BinarySection};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{OperandType, ArithOpType, MemAccessSize};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{
    entry_of_until, EntryOfResult, EntryOf, FunctionFinder, find_strings_casei, find_address_refs,
    find_bytes,
};
use crate::analysis_state::{
    AnalysisState, StateEnum, ScMainAnalyzerState, IsInitMapFromPathState, FindChooseSnpState,
    SinglePlayerStartState, MapEntryState, LoadImagesAnalysisState,
};
use crate::add_terms::collect_arith_add_terms;
use crate::call_tracker::{self, CallTracker};
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, ExecStateExt, OperandExt, OptionExt, MemAccessExt, is_global, is_stack_address,
    bumpvec_with_capacity, single_result_assign,
};
use crate::vtables::Vtables;

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
    pub shield_overlays: Option<Operand<'e>>,
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

pub(crate) struct SelectMapEntryAnalysis<Va: VirtualAddress> {
    pub create_game_multiplayer: Option<Va>,
    pub mde_load_map: Option<Va>,
    pub mde_load_replay: Option<Va>,
    pub mde_load_save: Option<Va>,
    pub create_game_dialog_vtbl_on_multiplayer_create: u16,
}

pub(crate) struct SinglePlayerMapEnd<'e, Va: VirtualAddress> {
    pub single_player_map_end: Option<Va>,
    pub local_game_result: Option<Operand<'e>>,
}

pub(crate) struct SinglePlayerMapEndAnalysis<'e, Va: VirtualAddress> {
    pub set_scmain_state: Option<Va>,
    pub unlock_mission: Option<Va>,
    pub is_custom_single_player: Option<Operand<'e>>,
    pub current_campaign_mission: Option<Operand<'e>>,
}

pub(crate) struct InitMapFromPathAnalysis<'e, Va: VirtualAddress> {
    pub read_whole_mpq_file: Option<Va>,
    pub read_whole_mpq_file2: Option<Va>,
    pub open_map_mpq: Option<Va>,
    pub sfile_close_archive: Option<Va>,
    pub load_replay_scenario_chk: Option<Va>,
    pub replay_scenario_chk: Option<Operand<'e>>,
    pub replay_scenario_chk_size: Option<Operand<'e>>,
    pub map_mpq: Option<Operand<'e>>,
    pub map_history: Option<Operand<'e>>,
}

pub(crate) struct JoinCustomGame<Va: VirtualAddress> {
    pub join_custom_game: Option<Va>,
    pub find_file_with_crc: Option<Va>,
}

pub(crate) struct FindFileWithCrc<Va: VirtualAddress> {
    pub for_files_in_dir: Option<Va>,
    pub simple_file_match_callback: Option<Va>,
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
    let arg_cache = &analysis.arg_cache;
    let funcs = functions.functions();

    // Find ref for char *smk_filenames[0x1c]; smk_filenames[0] == "smk\\blizzard.webm"
    let rdata = binary.section(b".rdata\0\0")?;
    let data = binary.section(b".data\0\0\0")?;
    let str_ref_addrs = find_strings_casei(bump, &rdata.data, b"smk\\blizzard.");

    let data_rvas = str_ref_addrs.iter().flat_map(|&str_rva| {
        find_address_refs(bump, &data.data, rdata.virtual_address + str_rva.0)
    });
    let data_rvas = BumpVec::from_iter_in(data_rvas, bump);
    let global_refs = data_rvas.iter().flat_map(|&rva| {
        let smk_names = data.virtual_address + rva.0;
        functions.find_functions_using_global(analysis, data.virtual_address + rva.0)
            .into_iter()
            .map(move |x| (x, smk_names))
    });
    let global_refs = BumpVec::from_iter_in(global_refs, bump);

    let mut result = None;
    for (global, smk_names) in global_refs {
        let new = entry_of_until(binary, funcs, global.use_address, |entry| {
            let mut analyzer = IsPlaySmk::<E> {
                result: EntryOf::Retry,
                arg_cache,
                smk_names,
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

struct IsPlaySmk<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    arg_cache: &'a ArgCache<'e, E>,
    smk_names: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsPlaySmk<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Move(_, value, None) = *op {
            let value = ctrl.resolve(value);
            let ok = ctrl.if_mem_word_offset(value, self.smk_names.as_u64())
                .and_then(|x| x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()))
                .filter(|&x| Operand::and_masked(x).0 == self.arg_cache.on_entry(0))
                .is_some();
            if ok {
                self.result = EntryOf::Ok(());
                ctrl.end_analysis();
            }
        }
    }
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
            phantom: Default::default(),
        };
        let state = StateEnum::ScMain(ScMainAnalyzerState::SearchingEntryHook);
        let state = AnalysisState::new(bump, state);
        let exec_state = E::initial_state(ctx, binary);
        let mut analysis = FuncAnalysis::custom_state(
            binary,
            ctx,
            sc_main,
            exec_state,
            state,
        );
        analysis.analyze(&mut analyzer);
    }
    result
}

fn collect_game_pointers<'e>(operand: Operand<'e>, out: &mut BumpVec<'_, (Operand<'e>, u64)>) {
    match operand.ty() {
        OperandType::Memory(mem) => out.push(mem.address()),
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
    game_pointers: &'a [(Operand<'e>, u64)],
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
                let mem = ctrl.resolve_mem(mem);
                let addr = mem.address();
                if self.game_pointers.iter().any(|&x| addr == x) {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

struct ScMainAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut GameInit<'e, E::VirtualAddress>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    ScMainAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let state = *ctrl.user_state().get::<ScMainAnalyzerState>();
        match *op {
            Operation::Jump { to, condition } => {
                if let ScMainAnalyzerState::SwitchJumped(..) = state {
                    // Expecting call immediately after switch jump
                    ctrl.end_analysis();
                    return;
                }
                let condition = ctrl.resolve(condition);
                if condition.if_constant().unwrap_or(0) != 0 {
                    let to = ctrl.resolve(to);
                    if to.if_constant().is_none() {
                        // Switch jump, follow cases 3 & 4 if searching for game loop,
                        // switch expression is also scmain_state then
                        if state == ScMainAnalyzerState::SearchingGameLoop {
                            let switch = CompleteSwitch::new(to, ctx, ctrl.exec_state());
                            if let Some(switch) = switch {
                                if let Some(index) = switch.index_operand(ctx) {
                                    self.result.scmain_state = Some(index);
                                }
                                for case_n in 3..5 {
                                    let binary = ctrl.binary();
                                    if let Some(addr) =
                                        switch.branch(binary, ctx, case_n as u32)
                                    {
                                        ctrl.user_state().set(
                                            ScMainAnalyzerState::SwitchJumped(case_n)
                                        );
                                        ctrl.analyze_with_current_state(self, addr);
                                    }
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else {
                    if state == ScMainAnalyzerState::SearchingEntryHook {
                        // BW does if options & 0x800 != 0 { play_smk(..); }
                        // at the hook point
                        let ok = condition.if_arithmetic_eq_neq()
                            .map(|(l, r, _)| (l, r))
                            .and_either(|x| x.if_arithmetic_and_const(8))
                            .and_then(|(val, _other)| val.if_memory())
                            .is_some();
                        if ok {
                            self.result.mainmenu_entry_hook = Some(ctrl.address());
                            ctrl.user_state().set(ScMainAnalyzerState::SearchingGameLoop);
                        }
                    }
                }
            }
            Operation::Call(to) => {
                if let ScMainAnalyzerState::SwitchJumped(case) = state {
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
            Operation::Move(DestOperand::Memory(ref mem), val, _) => {
                // Skip any moves of constant 4 to memory as it is likely scmain_state write
                if state == ScMainAnalyzerState::SearchingEntryHook {
                    if ctrl.resolve(val).if_constant() == Some(4) {
                        let dest = ctrl.resolve_mem(mem);
                        if !is_stack_address(dest.address().0) {
                            ctrl.skip_operation();
                        }
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
    let mut chk_data = find_bytes(bump, &rdata.data, &chk_validated_sections[0][..]);
    chk_data.retain(|&rva| {
        if rva.0 & 3 != 0 {
            return false;
        }
        for (i, other_section) in chk_validated_sections.iter().enumerate().skip(1) {
            let validator_size = match E::VirtualAddress::SIZE {
                4 => 0xc,
                _ => 0x10,
            };
            let index = rva.0 as usize + i * validator_size;
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
        find_address_refs(bump, &rdata.data, address)
            .into_iter()
            .map(move |x| (rva, x))
    });
    let section_refs = BumpVec::from_iter_in(section_refs, bump);
    let chk_validating_funcs = section_refs.iter().flat_map(|&(chk_funcs_rva, rva)| {
        let address = rdata.virtual_address + rva.0;
        let mut funcs = functions.find_functions_using_global(analysis, address);
        if funcs.is_empty() {
            // At least 64bit for some reason wants to refer to -8 offset..
            funcs = functions.find_functions_using_global(
                analysis,
                address - E::VirtualAddress::SIZE,
            );
        }
        funcs
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
            let state =
                AnalysisState::new(bump, StateEnum::InitMapFromPath(state));
            let mut analyzer = IsInitMapFromPath {
                result: EntryOf::Retry,
                arg_cache,
                phantom: Default::default(),
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

struct IsInitMapFromPath<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: EntryOf<()>,
    arg_cache: &'a ArgCache<'e, E>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    IsInitMapFromPath<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // init_map_from_path does
        // if (arg3 == 0) {
        //     game.campaign_mission = 0;
        // }
        // as its first operation (Unless assertions enabled)
        match *op {
            Operation::Move(ref to, val, None) => {
                let state = ctrl.user_state().get::<IsInitMapFromPathState>();
                if state.is_after_arg3_check {
                    let val = ctrl.resolve(val);
                    if val.if_constant() == Some(0) {
                        if let DestOperand::Memory(mem) = to {
                            let dest = ctrl.resolve_mem(mem);
                            if dest.address().1 == 0x154 {
                                self.result = EntryOf::Ok(());
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                let state = ctrl.user_state().get::<IsInitMapFromPathState>();
                if state.jump_count > 6 {
                    ctrl.end_branch();
                    return;
                }
                state.jump_count += 1;
                let cond = ctrl.resolve(condition);
                let mut arg3_check = false;
                let ctx = ctrl.ctx();
                if let Some((l, _)) = cond.if_arithmetic_eq_neq_zero(ctx) {
                    if self.arg_cache.on_entry(2) == Operand::and_masked(l).0 {
                        arg3_check = true;
                    }
                }
                let state = ctrl.user_state().get::<IsInitMapFromPathState>();
                state.is_after_arg3_check = arg3_check;
            }
            _ => (),
        }
    }
}

pub(crate) fn choose_snp<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
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
    let vtables = vtables.vtables_starting_with(b".?AVSelectConnectionScreen@glues@@\0")
        .map(|x| x.address);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
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
        let state = AnalysisState::new(bump, StateEnum::FindChooseSnp(state));
        let mut analyzer = FindChooseSnp {
            result: None,
            arg_cache,
            inlining: false,
            phantom: Default::default(),
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
                        let ctx = ctrl.ctx();
                        let esp_nonchanged =
                            ctrl.resolve(self.ctx.register(4)) == ctx.register(4);
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

struct FindChooseSnp<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inlining: bool,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    FindChooseSnp<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        const ID_BNAU: u32 = 0x424E4155;
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let state = ctrl.user_state().get::<FindChooseSnpState>();
                    if let Some(off) = state.provider_id_offset.clone() {
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
                let provider_id = cond.if_arithmetic_eq_neq()
                    .filter(|x| x.1.if_constant() == Some(ID_BNAU as u64))
                    .map(|x| x.0);
                let state = ctrl.user_state().get::<FindChooseSnpState>();
                state.provider_id_offset = provider_id;
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
    let bump = &analysis.bump;
    let funcs = functions.functions();
    let arg_cache = &analysis.arg_cache;
    for caller in callers {
        let ok = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = SinglePlayerStartAnalyzer {
                result: &mut result,
                arg_cache,
                local_player_id: &local_player_id,
                inlining: false,
                inline_limit: 0,
                first_call: true,
                phantom: Default::default(),
            };
            let exec = E::initial_state(ctx, binary);
            let state = SinglePlayerStartState::SearchingStorm101;
            let state = AnalysisState::new(bump, StateEnum::SpStart(state));
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

struct SinglePlayerStartAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut SinglePlayerStart<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    local_player_id: &'a Operand<'e>,
    inlining: bool,
    inline_limit: u8,
    first_call: bool,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SinglePlayerStartAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let state = *ctrl.user_state().get::<SinglePlayerStartState>();
        match state {
            SinglePlayerStartState::SearchingStorm101 => {
                if let Operation::Call(_) = op {
                    let was_first_call = self.first_call;
                    self.first_call = false;
                    let ctx = ctrl.ctx();
                    let zero = ctx.const_0();
                    let ok = Some(ctrl.resolve(self.arg_cache.on_call(3)))
                        .filter(|&x| x == zero)
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(4)))
                        .filter(|&x| x == zero)
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(5)))
                        .filter(|&x| ctx.and_const(x, 0xffff_ffff) == zero)
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(6)))
                        .filter(|&x| ctx.and_const(x, 0xffff_ffff).if_mem8().is_some())
                        .is_some();
                    if ok {
                        let arg10 = ctrl.resolve(self.arg_cache.on_call(9));
                        ctrl.user_state().set(SinglePlayerStartState::AssigningPlayerMappings);
                        self.result.local_storm_player_id = Some(ctx.mem32(arg10, 0));
                    } else if was_first_call {
                        ctrl.check_stack_probe();
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inlining = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inlining = false;
                        }
                    }
                } else if let Operation::Move(ref dest, val, None) = *op {
                    if let DestOperand::Memory(mem) = dest {
                        let val = ctrl.resolve(val);
                        let dest = ctrl.resolve_mem(mem);
                        let ctx = ctrl.ctx();
                        let is_move_to_u32_arr = dest.if_add_either(ctx, |x| {
                            x.if_arithmetic_mul_const(4)
                                .map(|x| x.unwrap_sext())
                        });
                        if let Some((index, base)) = is_move_to_u32_arr {
                            if let Some(storm_id) = self.result.local_storm_player_id {
                                if index == storm_id {
                                    if val == *self.local_player_id {
                                        self.result.net_player_to_game = Some(base);
                                    } else {
                                        self.result.net_player_to_unique = Some(base);
                                        self.result.local_unique_player_id = Some(val);
                                    }
                                }
                            }
                        }
                        // Check for copy through unrolled moves of u32 or larger;
                        // [game_data + x] = [arg1 + x], where x >= 0x80 && x < 0x8c
                        // (Inside game_data.got)
                        // to avoid catching just unintended other reads from game_data
                        let offset = val.if_memory()
                            .filter(|x| x.size.bits() >= 32 && x.size == mem.size)
                            .and_then(|x| {
                                let (base, offset) = x.address();
                                if base != self.arg_cache.on_entry(0) ||
                                    !(0x80..0x8c).contains(&offset)
                                {
                                    None
                                } else {
                                    Some(offset)
                                }
                            });
                        if let Some(offset) = offset {
                            let ctx = ctrl.ctx();
                            let game_data = ctx.mem_sub_const_op(&dest, offset);
                            if is_global(game_data) {
                                self.result.game_data = Some(game_data);
                            }
                        }
                    }
                } else if let Operation::Special(ref bytes) = op {
                    // (Rep) movs dword
                    if &bytes[..] == &[0xf3, 0xa5] {
                        let len = ctrl.resolve_register(1);
                        let from = ctrl.resolve_register(6);
                        let dest = ctrl.resolve_register(7);
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
                    ctrl.user_state().set(SinglePlayerStartState::FindingSkins);
                }
            }
            SinglePlayerStartState::FindingSkins => {
                ctrl.aliasing_memory_fix(op);
                if self.inline_limit != 0 {
                    if let Operation::Jump { .. } = *op {
                        self.inline_limit -= 1;
                    }
                    if let Operation::Call(..) = *op {
                        self.inline_limit = 0;
                    }
                    if self.inline_limit == 0 {
                        ctrl.end_analysis();
                        return;
                    }
                }
                let result = &mut self.result;
                let ctx = ctrl.ctx();
                if let Operation::Call(dest) = *op {
                    if !self.inlining {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inlining = true;
                            self.inline_limit = 15;
                            ctrl.inline(self, dest);
                            if self.inline_limit != 0 {
                                ctrl.skip_operation();
                                self.inline_limit = 0;
                            }
                            self.inlining = false;
                        }
                    }
                } else {
                    let dest_from = match *op {
                        Operation::Move(ref dest, val, None) => match dest {
                            DestOperand::Memory(mem) => {
                                let dest = ctrl.resolve_mem(mem);
                                let val = ctrl.resolve(val);
                                if let Some(mem) = val.if_memory() {
                                    Some((dest, *mem))
                                } else {
                                    None
                                }
                            },
                            _ => None,
                        }
                        Operation::Special(ref bytes) => {
                            // (Rep) movs dword
                            if &bytes[..] == &[0xf3, 0xa5] {
                                let from = ctrl.resolve_register(6);
                                let dest = ctrl.resolve_register(7);
                                let from = ctx.mem_access(from, 0, MemAccessSize::Mem32);
                                let dest = ctx.mem_access(dest, 0, MemAccessSize::Mem32);
                                Some((dest, from))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };

                    if let Some((dest, addr)) = dest_from {
                        let index_base = dest.if_add_either(ctx, |x| x.if_mul_with_const());
                        if let Some((index, base)) = index_base {
                            let size = index.1;
                            if Some(index.0.unwrap_sext()) == result.local_storm_player_id {
                                let offset = E::struct_layouts().local_skin_unit_skins();
                                let addr = ctx.mem_sub_const_op(&addr, offset);
                                if size > 16 {
                                    single_result_assign(Some(addr), &mut result.skins);
                                    single_result_assign(Some(base), &mut result.player_skins);
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
                    .map(|x| ctx.mem8(x, 0));
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
                    let ctx = ctrl.ctx();
                    let mem_byte = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|x| x.0.if_mem8());
                    if let Some(mem) = mem_byte {
                        self.mem_byte_conds.push((ctrl.address(), mem.address_op(ctx)));
                    }
                }
            }
            Operation::Call(_) => {
                let seems_large_stack_alloc = self.first_branch &&
                    ctrl.resolve_register(0)
                        .if_constant()
                        .filter(|&c| c > 0x1000 && c < 0x10000)
                        .is_some();
                if seems_large_stack_alloc {
                    // Skip to avoid clobbering registers
                    ctrl.skip_operation();
                }
            }
            Operation::Move(ref dest, _, _) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem8 {
                        let ctx = ctrl.ctx();
                        let dest = ctrl.resolve_mem(mem);
                        if self.first_branch {
                            let (base, offset) = dest.address();
                            // Older versions of the function had arg1 as
                            // map entry (and used 5 args total instead of 3)
                            if offset > 0x20 &&
                                (base == self.arg_cache.on_entry(2) ||
                                 base == self.arg_cache.on_entry(0))
                            {
                                self.arg3_write_seen = true;
                            }
                        }
                        self.mem_bytes_written.push(dest.address_op(ctx));
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
                        let idx = self.func_returns.len() as u32;
                        let custom = ctx.custom(idx);
                        self.func_returns.push(dest);
                        ctrl.set_register(0, custom);
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
                    let asset_scale = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(4))
                        .map(|x| x.0);
                    if let Some(scale) = asset_scale {
                        let funcs = &self.func_returns;
                        let ctx = ctrl.ctx();
                        let binary = ctrl.binary();
                        let scale = ctx.transform(scale, 8, |op| {
                            if let Some(idx) = op.if_custom() {
                                let func = funcs[idx as usize];
                                call_tracker::analyze_func_return::<E>(func, ctx, binary)
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
                            let ctx = ctrl.ctx();
                            let cond = cond.if_arithmetic_eq_neq_zero(ctx)
                                .map(|x| x.0)
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
                if let Some(to) = ctrl.resolve_va(to) {
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
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> Option<Operand<'e>> {
    #[allow(bad_style)]
    let VA_SIZE: u32 = E::VirtualAddress::SIZE;

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let vtables = vtables.vtables_starting_with(b".?AVCreateGameScreen@glues@@\0")
        .map(|x| x.address);
    let mut vtables = BumpVec::from_iter_in(vtables, bump);
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
                let ctx = ctrl.ctx();
                let mem = cond.if_arithmetic_eq_neq_zero(ctx)
                    .and_then(|x| x.0.if_mem8());
                if let Some(mem) = mem {
                    let ctx = ctrl.ctx();
                    self.result = Some(mem.address_op(ctx));
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
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> Option<E::VirtualAddress> {
    let vtables = vtables.vtables_starting_with(b".?AVGameLobbyScreen@glues@@\0")
        .map(|x| x.address);
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
                    if let Some(dest) = ctrl.resolve_va(dest) {
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
                    let ctx = ctrl.ctx();
                    let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| x.0 == self.local_storm_player)
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
    let branch = process_lobby_commands_switch.branch(binary, ctx, 0x48)?;
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
                    if let Some(dest) = ctrl.resolve_va(dest) {
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
                    let lobby_state = cond.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(8))
                        .map(|x| x.0);
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
    // Find caller of init_units that compares a ptr against 0xffff_ffff constant
    // thrice before init_units call. This handle will be loaded_save handle.
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
                        r.if_constant().filter(|&c| c as u32 == u32::MAX)?;
                        Some(l)
                    })
                    .filter(|&x| is_global(x))
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
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if dest == self.init_units {
                        self.result = EntryOf::Stop;
                    }
                }
            }
            _ => (),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SelectMapEntryState {
    // Find map/save/replay load functions by updating branch state
    // based on jumps with map_dir_entry.flags
    // Keep map load function state and afterwards continue from that with
    // setting map_dir_entry.flags = 0x2 (Map)
    LoadMapDirEntry,
    CreateGameMultiplayer,
    OnMultiplayerCreate,
}

pub(crate) fn analyze_select_map_entry<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    select_map_entry: E::VirtualAddress,
) -> SelectMapEntryAnalysis<E::VirtualAddress> {
    struct Analyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
        arg_cache: &'a ArgCache<'e, E>,
        result: &'a mut SelectMapEntryAnalysis<E::VirtualAddress>,
        state: SelectMapEntryState,
        call_tracker: CallTracker<'acx, 'e, E>,
        load_map_entry_state: Option<(E, E::VirtualAddress)>,
        map_entry_flags_offset: Option<u32>,
        ctx: OperandCtx<'e>,
        first_call: bool,
        bump: &'acx Bump,
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
        Analyzer<'a, 'acx, 'e, E>
    {
        type State = AnalysisState<'acx, 'e>;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            let ctx = ctrl.ctx();
            let arg_cache = self.arg_cache;
            match self.state {
                SelectMapEntryState::LoadMapDirEntry => match *op {
                    Operation::Call(dest) => {
                        if self.first_call {
                            self.first_call = false;
                            let seems_large_stack_alloc = ctrl.resolve_register(0)
                                    .if_constant()
                                    .filter(|&c| c > 0x1000 && c < 0x10000)
                                    .is_some();
                            if seems_large_stack_alloc {
                                // Skip to avoid clobbering registers
                                ctrl.skip_operation();
                                return;
                            }
                        }
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let state = *ctrl.user_state().get::<MapEntryState>();
                            if state != MapEntryState::Unknown {
                                let arg1 = ctrl.resolve(arg_cache.on_call(0));
                                if self.is_map_entry(arg1) {
                                    let result = &mut self.result;
                                    let result_fn = match state {
                                        MapEntryState::Map => &mut result.mde_load_map,
                                        MapEntryState::Save => &mut result.mde_load_save,
                                        MapEntryState::Replay => &mut result.mde_load_replay,
                                        MapEntryState::Unknown => return,
                                    };
                                    single_result_assign(Some(dest), result_fn);
                                    if state == MapEntryState::Map {
                                        let address = ctrl.address();
                                        let state = ctrl.exec_state().clone();
                                        self.load_map_entry_state = Some((state, address));
                                    }
                                    let done = result.mde_load_map.is_some() &&
                                        result.mde_load_save.is_some() &&
                                        result.mde_load_replay.is_some();
                                    if done {
                                        if let Some((mut state, address)) =
                                            self.load_map_entry_state.take()
                                        {
                                            self.state =
                                                SelectMapEntryState::CreateGameMultiplayer;
                                            let dest = ctx.mem32(
                                                arg_cache.on_entry(2),
                                                self.map_entry_flags_offset.unwrap_or(0) as u64,
                                            );
                                            state.move_resolved(
                                                &DestOperand::from_oper(dest),
                                                ctx.constant(2),
                                            );
                                            let binary = ctrl.binary();
                                            let user_state = MapEntryState::Unknown;
                                            let user_state = AnalysisState::new(
                                                self.bump,
                                                StateEnum::SelectMapEntry(user_state),
                                            );
                                            let mut analysis = FuncAnalysis::custom_state(
                                                binary,
                                                ctx,
                                                address,
                                                state,
                                                user_state,
                                            );
                                            analysis.analyze(self);
                                        }
                                        ctrl.end_analysis();
                                    } else {
                                        ctrl.end_branch();
                                    }
                                    return;
                                }
                            }
                            let this = ctrl.resolve_register(1);
                            if self.is_map_entry(this) {
                                self.call_tracker.add_call_resolve(ctrl, dest);
                            }
                        }
                    }
                    Operation::Jump { condition, to } => {
                        let state = *ctrl.user_state().get::<MapEntryState>();
                        if state != MapEntryState::Unknown {
                            ctrl.end_branch();
                            return;
                        }
                        let to = match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        };
                        let condition = ctrl.resolve(condition);
                        let flag_bits = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| {
                                let (l, r) = x.0.if_arithmetic_and()?;
                                let bits = r.if_constant()? as u8;
                                let (base, offset) = l.if_mem8()?.address();
                                let offset = u32::try_from(offset).ok()?;
                                if !self.is_map_entry(base) {
                                    return None;
                                }
                                Some((bits, offset, x.1))
                            });
                        if let Some((flag_bits, offset, jump_if_clear)) = flag_bits {
                            match self.map_entry_flags_offset {
                                Some(s) => {
                                    if s != offset {
                                        return;
                                    }
                                }
                                None => {
                                    self.map_entry_flags_offset = Some(offset);
                                }
                            }
                            let state = match flag_bits {
                                1 => MapEntryState::Save,
                                2 => MapEntryState::Map,
                                4 => MapEntryState::Replay,
                                _ => return,
                            };
                            let (set_addr, unset_addr) = match jump_if_clear {
                                false => (to, ctrl.current_instruction_end()),
                                true => (ctrl.current_instruction_end(), to),
                            };
                            ctrl.end_branch();
                            ctrl.add_branch_with_current_state(unset_addr);
                            ctrl.user_state().set(state);
                            ctrl.add_branch_with_current_state(set_addr);
                        }
                    }
                    _ => (),
                }
                SelectMapEntryState::CreateGameMultiplayer => match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            // Check for arg1 = stack var,
                            // arg2 = a1.x0_string.pointer,
                            // arg6 = arg1.turn_rate
                            // Arg5~8 is a 16byte struct passed by value,
                            // on 64-bit check arg5.x4 = arg1.turn_rate (It is passed by pointer)
                            let ok = Some(ctrl.resolve(arg_cache.on_call(0)))
                                .filter(|&x| is_stack_address(x))
                                .map(|_| ctrl.resolve(arg_cache.on_call(1)))
                                .and_then(|x| ctrl.if_mem_word_offset(x, 0))
                                .filter(|&x| self.is_game_name(x))
                                .filter(|_| {
                                    // Some older versions only have 8byte by-value struct,
                                    // to support those too also check arg5 instead of arg6.
                                    if E::VirtualAddress::SIZE == 4 {
                                        [1u8, 0].iter().any(|&i| {
                                            let op = ctrl.resolve(arg_cache.on_call(4 + i));
                                            self.is_game_input_turn_rate(op)
                                        })
                                    } else {
                                        let op = ctrl.resolve(arg_cache.on_call(4));
                                        // The old versions that had 8-byte may not even
                                        // have 64-bit builds, but supporting it instead
                                        // of checking that.
                                        [4u8, 0u8].iter().any(|&off| {
                                            let address = ctx.mem_access(
                                                op,
                                                off as u64,
                                                MemAccessSize::Mem32,
                                            );
                                            let val = ctrl.read_memory(&address);
                                            self.is_game_input_turn_rate(val)
                                        })
                                    }
                                })
                                .is_some();
                            if ok {
                                self.result.create_game_multiplayer = Some(dest);
                                self.state = SelectMapEntryState::OnMultiplayerCreate;
                            }
                        }
                    }
                    _ => (),
                },
                SelectMapEntryState::OnMultiplayerCreate => match *op {
                    Operation::Call(dest) => {
                        let dest = ctrl.resolve(dest);
                        let offset = ctrl.if_mem_word(dest)
                            .and_then(|mem| {
                                let (base, offset) = mem.address();
                                if offset <= 0x40 {
                                    return None;
                                }
                                if !self.is_create_dialog(ctrl.if_mem_word_offset(base, 0)?) {
                                    return None;
                                }
                                Some(offset)
                            });
                        if let Some(offset) = offset {
                            self.result.create_game_dialog_vtbl_on_multiplayer_create =
                                offset as u16;
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                },
            }
        }
    }

    impl<'a, 'acx, 'e, E: ExecutionState<'e>> Analyzer<'a, 'acx, 'e, E> {
        // Note: Support two different func arg orders:
        // Older: select_map_entry(this = create_game_dlg, a1 = map_entry, a2 = game_name)
        //      with game_input being part of create_game_dlg
        // Newer: select_map_entry(a1 = game_input, a2 = create_game_dlg, a3 = map_entry)
        //      with game_name being part of game_input
        fn is_map_entry(&self, op: Operand<'e>) -> bool {
            op == self.arg_cache.on_entry(2) || op == self.arg_cache.on_thiscall_entry(0)
        }

        fn is_game_input(&self, op: Operand<'e>) -> bool {
            op == self.arg_cache.on_entry(0) || op == self.ctx.register(1)
        }

        fn is_game_input_turn_rate(&self, op: Operand<'e>) -> bool {
            op.if_mem32()
                .filter(|&x| self.is_game_input(x.address().0))
                .is_some()
        }

        fn is_game_name(&self, op: Operand<'e>) -> bool {
            op == self.arg_cache.on_entry(0) || op == self.arg_cache.on_thiscall_entry(1)
        }

        fn is_create_dialog(&self, op: Operand<'e>) -> bool {
            op == self.arg_cache.on_entry(1) || op == self.ctx.register(1)
        }
    }

    // select_map_entry arg2 is CreateGameScreen; and it calls this relevant function
    // For some older versions it also has been arg ecx
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let mut result = SelectMapEntryAnalysis {
        mde_load_map: None,
        mde_load_replay: None,
        mde_load_save: None,
        create_game_multiplayer: None,
        create_game_dialog_vtbl_on_multiplayer_create: 0,
    };
    let mut analyzer = Analyzer::<E> {
        first_call: true,
        result: &mut result,
        arg_cache: &analysis.arg_cache,
        state: SelectMapEntryState::LoadMapDirEntry,
        call_tracker: CallTracker::with_capacity(analysis, 0, 0x20),
        load_map_entry_state: None,
        map_entry_flags_offset: None,
        ctx,
        bump,
    };
    let exec = E::initial_state(ctx, binary);
    let state = MapEntryState::Unknown;
    let state = AnalysisState::new(bump, StateEnum::SelectMapEntry(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, select_map_entry, exec, state);
    analysis.analyze(&mut analyzer);
    result
}

pub(crate) fn join_game<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    local_storm_id: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let local_storm_id = local_storm_id.if_memory()
        .and_then(|x| x.if_constant_address())
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
                let ok = ctrl.if_mem_word_offset(arg1, 0)
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
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    let arg5 = ctrl.resolve(self.arg_cache.on_call(4));
                    let ctx = ctrl.ctx();
                    let ok = Some(())
                        .filter(|()| {
                            ctx.and_const(arg1, 0xffff_ffff) ==
                                ctx.and_const(self.arg_cache.on_entry(0), 0xffff_ffff)
                        })
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
            Operation::Move(DestOperand::Memory(ref dest), val, None) => {
                if !self.inlining && dest.size == MemAccessSize::Mem8 {
                    let val = ctrl.resolve(val);
                    if val.if_mem8().is_some() {
                        let mem = ctrl.resolve_mem(dest);
                        let ctx = ctrl.ctx();
                        let result = mem.if_constant_address()
                            .and_then(|x| Some(ctx.constant(x.checked_sub(0x24 * 11 + 8)?)));
                        if single_result_assign(result, &mut self.result) {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve_va(dest) {
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
            Operation::Move(DestOperand::Memory(ref dest), val, None) => {
                let val = ctrl.resolve(val);
                let input_ok = val.if_memory()
                    .filter(|x| {
                        let (base, offset) = x.address();
                        x.size == dest.size &&
                            offset == 0x1f &&
                            base == self.arg_cache.on_entry(0)
                    })
                    .is_some();
                if input_ok {
                    let dest = ctrl.resolve_mem(dest);
                    let ctx = ctrl.ctx();
                    self.result = EntryOf::Ok(dest.address_op(ctx));
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
        shield_overlays: None,
        fire_overlay_max: None,
        anim_struct_size: 0,
    };
    let binary = actx.binary;
    let ctx = actx.ctx;
    let images_dat_grp = match binary.read_address(images_dat.0 + images_dat.1 * 0x0) {
        Ok(o) => ctx.constant(o.as_u64()),
        Err(_) => return result,
    };
    let images_dat_shield_overlay = match binary.read_address(images_dat.0 + images_dat.1 * 0x8) {
        Ok(o) => ctx.constant(o.as_u64()),
        Err(_) => return result,
    };
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
        images_dat_shield_overlay,
        rdata: actx.binary_sections.rdata,
        text: actx.binary_sections.text,
        min_state: LoadImagesAnalysisState::BeforeLoadDat,
    };
    let exec = E::initial_state(ctx, binary);
    let state = LoadImagesAnalysisState::BeforeLoadDat;
    let state = AnalysisState::new(&actx.bump, StateEnum::LoadImages(state));
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
    images_dat_shield_overlay: Operand<'e>,
    func_addr_to_return_custom: FxHashMap<E::VirtualAddress, u32>,
    // Operand is this arg, set when open_anim_single_file candidate
    custom_to_func_addr: BumpVec<'acx, (E::VirtualAddress, Option<Operand<'e>>)>,
    rdata: &'a BinarySection<E::VirtualAddress>,
    text: &'a BinarySection<E::VirtualAddress>,
    min_state: LoadImagesAnalysisState,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    LoadImagesAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let state = *ctrl.user_state().get::<LoadImagesAnalysisState>();
        match state {
            LoadImagesAnalysisState::BeforeLoadDat => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if dest == self.load_dat {
                            ctrl.user_state().set(LoadImagesAnalysisState::FindOpenAnims);
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
                            ctrl.user_state().set(LoadImagesAnalysisState::FindInitSkins);
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
                                ctrl.user_state()
                                    .set(LoadImagesAnalysisState::FindFireOverlayMax);
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
                            mem.if_constant_address()
                        } else {
                            val.if_constant()
                        };
                        let binary = ctrl.binary();
                        let ok = addr.map(E::VirtualAddress::from_u64)
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
                                ctrl.user_state().set(LoadImagesAnalysisState::FindAssetChangeCb);
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
                // load_lo_set(&shield_overlays, images_dat_shield_overlay, &mut out, 999)
                if let Operation::Call(_) = *op {
                    let is_find_grps = state == LoadImagesAnalysisState::FindImageGrps;
                    let arg_cache = self.arg_cache;
                    let out = &mut self.result;
                    let result = Some(()).and_then(|()| {
                        ctrl.resolve(arg_cache.on_call(3))
                            .if_constant().filter(|&c| c == 999)?;
                        let arg2 = ctrl.resolve(arg_cache.on_call(1));
                        let out = if is_find_grps {
                            if arg2 == self.images_dat_grp {
                                &mut out.image_grps
                            } else {
                                return None;
                            }
                        } else {
                            if arg2 == self.images_dat_attack_overlay {
                                &mut out.image_overlays
                            } else if arg2 == self.images_dat_shield_overlay {
                                &mut out.shield_overlays
                            } else {
                                return None;
                            }
                        };
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        Some((out, arg1))
                    });
                    if let Some((out_var, result)) = result {
                        single_result_assign(Some(result), out_var);
                        if is_find_grps {
                            ctrl.user_state().set(LoadImagesAnalysisState::FindImageOverlays);
                            self.min_state = LoadImagesAnalysisState::FindImageOverlays;
                        } else {
                            if out.image_overlays.is_some() &&
                                out.shield_overlays.is_some()
                            {
                                ctrl.user_state().set(LoadImagesAnalysisState::FindFireOverlayMax);
                                self.min_state = LoadImagesAnalysisState::FindFireOverlayMax;
                                if self.inline_depth != 0 {
                                    // Go back to outer load_images
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            LoadImagesAnalysisState::FindFireOverlayMax => {
                let ctx = ctrl.ctx();
                if let Operation::Move(ref dest, value, None) = *op {
                    let value = ctrl.resolve(value);
                    if value.if_constant() == Some(999) {
                        ctrl.skip_operation();
                        ctrl.move_unresolved(dest, ctx.custom(0));
                        return;
                    }
                    // End on loop rerun i = 999 - 2
                    let end_branch = Operand::and_masked(ctx.and_const(value, 0xffff_ffff)).0
                        .if_arithmetic_sub_const(2)
                        .and_then(|x| x.if_custom())
                        .is_some();
                    if end_branch {
                        ctrl.end_branch();
                        return;
                    }
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == MemAccessSize::Mem8 {
                            let ok = value.if_arithmetic_and_const(0xfe)
                                .or_else(|| Some(value))
                                .and_then(|x| x.if_arithmetic_mul_const(0x2))
                                .is_some();
                            if ok {
                                let dest = ctrl.resolve_mem(mem);
                                let ctx = ctrl.ctx();
                                let base = dest.if_add_either_other(ctx, |x| {
                                    Operand::and_masked(x).0
                                        .if_arithmetic_sub_const(1)?
                                        .if_custom()
                                }).or_else(|| {
                                    dest.if_add_either_other(ctx, |x| {
                                        Operand::and_masked(x).0.if_custom()
                                    }).map(|x| ctx.add_const(x, 1))
                                });
                                if let Some(base) = base {
                                    self.result.fire_overlay_max = Some(base);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if *ctrl.user_state().get::<LoadImagesAnalysisState>() < self.min_state {
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
        // open_anim_single_file(this = &base_anim_set[1], 0, 1, 1*)
        // open_anim_multi_file(this = &base_anim_set[0], 0, 999, 1, 2*, 1)
        //      * These last args seem to be unused and not set in 64bit at all;
        //      32bit has to set them due to callee-restores-stack cc
        let ctx = ctrl.ctx();
        let arg1 = ctx.and_const(ctrl.resolve(self.arg_cache.on_thiscall_call(0)), 0xffff_ffff);
        let arg2 = ctx.and_const(ctrl.resolve(self.arg_cache.on_thiscall_call(1)), 0xffff_ffff);
        let this = ctrl.resolve_register(1);
        let is_single_file = arg1 == ctx.const_0() &&
            arg2 == ctx.const_1() &&
            this.if_arithmetic_add().and_then(|x| x.1.if_constant()).is_some();
        if is_single_file {
            self.custom_to_func_addr.push((func, Some(this)));
            return (true, false);
        }
        self.custom_to_func_addr.push((func, None));
        let is_multi_file_1 = arg1 == ctx.const_0() &&
            arg2.if_constant() == Some(999);
        if is_multi_file_1 {
            let arg3 =
                ctx.and_const(ctrl.resolve(self.arg_cache.on_thiscall_call(2)), 0xffff_ffff);
            let arg4 =
                ctx.and_const(ctrl.resolve(self.arg_cache.on_thiscall_call(3)), 0xffff_ffff);
            let is_multi_file = arg3 == ctx.const_1() &&
                matches!(arg4.if_constant(), Some(1) | Some(2));
            if is_multi_file {
                let (base, off) = this.struct_offset();
                let single_file = self.custom_to_func_addr.iter().rev()
                    .find_map(|&(addr, single_this)| {
                        let (base2, off2) = single_this?.struct_offset();
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
        let this_address = ctx.mem_access(this, 0, E::WORD_SIZE);
        let is_copy = ctrl.read_memory(&this_address)
            .if_constant()
            .filter(|&c| c <= 1)
            .is_some();
        if is_copy {
            let arg1_address = ctx.mem_access(arg1, 0, E::WORD_SIZE);
            let arg1_field1 = ctx.mem_access(arg1, E::VirtualAddress::SIZE.into(), E::WORD_SIZE);
            let vtbl = ctrl.read_memory(&arg1_address)
                .if_constant()
                .map(E::VirtualAddress::from_u64);
            let param = ctrl.read_memory(&arg1_field1)
                .if_constant()
                .map(E::VirtualAddress::from_u64);
            if let (Some(vtbl), Some(param)) = (vtbl, param) {
                // Copy vtbl and param to this
                let dest = ctrl.mem_word(this,0 );
                let dest2 = ctrl.mem_word(this, E::VirtualAddress::SIZE as u64);
                let state = ctrl.exec_state();
                let vtbl = ctx.constant(vtbl.as_u64());
                let param = ctx.constant(param.as_u64());
                state.move_resolved(&DestOperand::from_oper(dest), vtbl);
                state.move_resolved(&DestOperand::from_oper(dest2), param);
                if E::VirtualAddress::SIZE == 4 {
                    // Also assuming that func copy is stdcall
                    let esp = ctrl.resolve_register(4);
                    ctrl.set_register(4, ctx.add_const(esp, 4));
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
            let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
            if let Some(dest) = dest.if_constant() {
                let dest = E::VirtualAddress::from_u64(dest);
                let this = ctrl.resolve_register(1);
                let asset_change_cb = if E::VirtualAddress::SIZE == 4 {
                    let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                    let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                    // Check for add_asset_change_cb(&local, func_vtbl, func_cb, ...)
                    arg2.if_constant()
                        .map(E::VirtualAddress::from_u64)
                        .filter(|&x| is_in_section(self.rdata, x))
                        .and_then(|_| arg3.if_constant())
                        .map(E::VirtualAddress::from_u64)
                        .filter(|&x| is_in_section(self.text, x))
                        .or_else(|| {
                            // Alt function struct, 32bit only since the check
                            // assumes that a2 points to a3 which cannot be done with
                            // reg args:
                            // a2 - vtable *func_impl
                            // a3 - vtable
                            // a4 - param
                            if E::VirtualAddress::SIZE != 4 {
                                return None;
                            }
                            arg3.if_constant()
                                .map(E::VirtualAddress::from_u64)
                                .filter(|&x| is_in_section(self.rdata, x))?;
                            let param = ctrl.resolve(self.arg_cache.on_call(3))
                                .if_constant()
                                .map(E::VirtualAddress::from_u64)
                                .filter(|&x| is_in_section(self.text, x))?;
                            let arg3_loc = self.arg_cache.on_call(2).if_memory()?.address_op(ctx);
                            if arg2 != ctrl.resolve(arg3_loc) {
                                None
                            } else {
                                Some(param)
                            }
                        })
                } else {
                    // Check for add_asset_change_cb(&local, func *)
                    // Check vtbl and cb, and that *local != 1
                    // Local = 1 implies it being copy_func call instead,
                    // which looks similar as it's this=dest, a1=val
                    let address = ctx.mem_access(arg1, 0, MemAccessSize::Mem64);
                    ctrl.read_memory(&address).if_constant()
                        .map(E::VirtualAddress::from_u64)
                        .filter(|&x| is_in_section(self.rdata, x))
                        .map(|_| {
                            let address = ctx.mem_access(this, 0, MemAccessSize::Mem64);
                            ctrl.read_memory(&address)
                        })
                        .filter(|&x| x != ctx.const_1())
                        .map(|_| {
                            let address = ctx.mem_access(arg1, 8, MemAccessSize::Mem64);
                            ctrl.read_memory(&address)
                        })
                        .and_then(Operand::if_constant)
                        .map(E::VirtualAddress::from_u64)
                        .filter(|&x| is_in_section(self.text, x))
                };
                if let Some(cb) = asset_change_cb {
                    self.result.add_asset_change_cb = Some(dest);
                    self.result.anim_asset_change_cb = Some(cb);
                    ctrl.user_state().set(LoadImagesAnalysisState::FindImageGrps);
                    self.min_state = LoadImagesAnalysisState::FindImageGrps;
                    return;
                }
                self.check_simulate_func_copy(ctrl, this, arg1);
            } else if E::VirtualAddress::SIZE == 4 {
                let is_vtable_fn = ctrl.if_mem_word(dest)
                    .and_then(|x| x.if_constant_address())
                    .map(E::VirtualAddress::from_u64)
                    .filter(|&x| is_in_section(self.rdata, x))
                    .is_some();
                if is_vtable_fn && arg1 == ctx.const_0() {
                    // Assuming to be func.vtable.delete(0), add 4 to esp to
                    // simulate stdcall
                    let esp = ctrl.resolve_register(4);
                    ctrl.set_register(4, ctx.add_const(esp, 4));
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
                        call_tracker::analyze_func_return::<E>(func, ctx, binary)
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
                    if ctx.register(1) == ctrl.resolve_register(1) {
                        // one arg is split to 2 slots on 32bit, 1 on 64bit
                        let argc = match E::VirtualAddress::SIZE == 4 {
                            true => 5,
                            false => 4,
                        };
                        if (0..argc).all(|i| {
                            let on_entry = self.arg_cache.on_thiscall_entry(i);
                            let arg = ctrl.resolve(self.arg_cache.on_thiscall_call(i));
                            on_entry == arg || ctx.and_const(on_entry, 0xffff_ffff) ==
                                ctx.and_const(arg, 0xffff_ffff)
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
        entry_esp: ctx.register(4),
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
    // Also worth noting that this call is slightly different from analysis's set_briefing_music,
    // which has does call something else first (Briefing fades music out first).
    SetMusic,
    // Move of 1 to Mem8. Hopefully no conflicts.
    ContinueGameLoop,
    // Search for memcpy(palette_set[0], main_palette, 0x400)
    // Inline once if a1 == 0 and word(a2) == 0x100 set_palette(idx, entry_count, source)
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
    entry_esp: Operand<'e>,
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
                        let ok = arg1.if_mem16_offset(0xee)
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
                        self.result.continue_game_loop = Some(ctx.memory(&ctrl.resolve_mem(mem)));
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
                            if arg1 == ctx.const_0() &&
                                ctx.and_const(arg2, 0xffff).if_constant() == Some(0x100)
                            {
                                self.inline_limit = 3;
                                self.inline_depth = 1;
                                self.entry_esp = ctx.sub_const(
                                    ctrl.resolve_register(4),
                                    E::VirtualAddress::SIZE.into(),
                                );
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
                } else if let Operation::Jump { condition, .. } = *op {
                    if self.inline_depth != 0 && condition == ctx.const_1() {
                        // Check for tail call memcpy
                        if ctrl.resolve_register(4) == self.entry_esp {
                            let arg3 = ctrl.resolve(arg_cache.on_call(2));
                            if arg3.if_constant() == Some(0x400) {
                                let arg1 = ctrl.resolve(arg_cache.on_call(0));
                                let arg2 = ctrl.resolve(arg_cache.on_call(1));
                                self.result.palette_set = Some(arg1);
                                self.result.main_palette = Some(arg2);
                                self.state = GameLoopAnalysisState::TfontGam;
                                ctrl.end_analysis();
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
                        let mem = ctrl.resolve_mem(mem);
                        if mem.if_constant_address().is_some() {
                            self.sync_active_candidate = Some(ctx.memory(&mem));
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
                            let arg1_mem = ctx.mem_access(arg1, 0, E::WORD_SIZE);
                            let ok = ctrl.read_memory(&arg1_mem)
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
                    if let Some(jump_if_zero) = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| Operand::and_masked(x.0).0.if_custom() == Some(0))
                        .map(|x| x.1)
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
                    let result = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|x| {
                            let (l, r) = x.0.if_arithmetic_and_const(0x8000_0000)?
                                .if_arithmetic_sub()?;
                            l.if_custom()?;
                            Some((r, x.1))
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
                    if Operand::and_masked(value).0.if_custom().is_some() &&
                        ctrl.resolve_mem(mem).is_global()
                    {
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
                        let anti_troll = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| x.0.if_mem8())
                            .map(|x| ctx.mem_sub_const_op(x, 0x1a));
                        self.result.anti_troll = anti_troll;
                    }
                    // Check for game.frame_count >= replay_seek_frame
                    // (x >= y) should be (y > x) == 0
                    let replay_seek_frame = condition.if_arithmetic_eq_const(0)
                        .and_then(|x| {
                            let (y, x) = x.if_arithmetic_gt()?;
                            x.if_mem32_offset(0x14c)
                                .filter(|&x| x == self.game)?;
                            Some(y)
                        });
                    if let Some(replay_seek_frame) = replay_seek_frame {
                        self.result.step_game_logic = self.current_entry;
                        self.result.replay_seek_frame = Some(replay_seek_frame);
                        self.state = StepGameLoopAnalysisState::StepGameFrames;
                        if let Some(to) = ctrl.resolve_va(to) {
                            let binary = ctrl.binary();
                            let exec_state = ctrl.exec_state().clone();
                            let mut analysis = FuncAnalysis::custom_state(
                                binary,
                                ctx,
                                to,
                                exec_state,
                                Default::default(),
                            );
                            analysis.analyze(self);
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
                if let Some(dest) = ctrl.resolve_va(dest) {
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
                let menu_screen_id = condition.if_arithmetic_eq_neq()
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
                let ecx = ctrl.resolve_register(1);
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
                            let x = x.address().0;
                            let x = ctrl.if_mem_word(
                                ctrl.if_mem_word_offset(
                                    ctrl.if_mem_word_offset(x, 0)?,
                                    0,
                                )?
                            )?;
                            let x = x.address().0;
                            match x == ctx.register(1) {
                                true => Some(()),
                                false => None,
                            }
                        })
                        .is_some();
                    if ok {
                        self.state = StepBnetControllerState::FindEvents;
                        ctrl.clear_all_branches();
                    }
                }
            }
            StepBnetControllerState::FindEvents => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        let ok = ctrl.if_mem_word_offset(this, 0)
                            .and_then(|x| {
                                let x = ctrl.if_mem_word(x)?;
                                let x = x.address().0;
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
                        if let Some(mem) = ctrl.if_mem_word(dest) {
                            let offset = mem.address().1;
                            ctrl.do_call_with_result(ctx.custom(offset as u32));
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    if ctrl.resolve(condition) == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        if to.if_constant().is_none() {
                            let exec_state = ctrl.exec_state();
                            if let Some(switch) = CompleteSwitch::new(to, ctx, exec_state) {
                                if let Some(idx) = switch.index_operand(ctx) {
                                    let idx = Operand::and_masked(idx.unwrap_sext()).0;
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
                            let dest_resolved = ctrl.resolve_mem(mem);
                            let value = ctrl.resolve(value);
                            if value == ctx.mem_sub_const_op(
                                &dest_resolved,
                                E::VirtualAddress::SIZE as u64,
                            ) {
                                ctrl.move_unresolved(dest, ctx.new_undef());
                                ctrl.skip_operation();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn join_param_variant_type_offset<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    join_game: E::VirtualAddress,
) -> Option<u16> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut analyzer = JoinParamVariantTypeOffset::<E> {
        result: None,
        arg_cache: &actx.arg_cache,
        inline_depth: 0,
        state: JoinParamState::FindGetSaveGameId,
        custom_pos: 0,
        first_branch: false,
        current_variant: ctx.const_0(),
        current_arg1: actx.arg_cache.on_entry(0),
        bump: &actx.bump,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, join_game);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct JoinParamVariantTypeOffset<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: Option<u16>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    state: JoinParamState,
    custom_pos: u32,
    first_branch: bool,
    current_variant: Operand<'e>,
    current_arg1: Operand<'e>,
    bump: &'acx Bump,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum JoinParamState {
    // Inline the first call when this = arg1,
    // stop analysis there.
    // Inline second time if the first call at depth1 also has this = arg1,
    // otherwise assume current function as get_save_game_id
    FindGetSaveGameId,
    // Go forward until a call where this = arg1, arg1 = local, inline there
    BeforeVariantGet,
    // Find more calls where this = arg1, arg1 = local,
    // set [arg1] value to Custom.
    // Whenever a call with this or arg1 = `Custom + x` (x nonzero, 4-aligned) happens,
    // analyze it with FindVariantType
    FindVariant,
    // Check for comparision of x == 4 or jump/call with x where x is Mem[custom + y]
    FindVariantType,
}


impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    JoinParamVariantTypeOffset<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            JoinParamState::FindGetSaveGameId | JoinParamState::BeforeVariantGet => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if self.state == JoinParamState::FindGetSaveGameId {
                            if self.inline_depth != 0 {
                                self.state = JoinParamState::BeforeVariantGet;
                            }
                            if this == self.current_arg1 {
                                self.inline_depth += 1;
                                if self.state == JoinParamState::BeforeVariantGet {
                                    self.current_arg1 = ctx.register(1);
                                    let mut analysis =
                                        FuncAnalysis::new(ctrl.binary(), ctx, dest);
                                    analysis.analyze(self);
                                } else {
                                    ctrl.analyze_with_current_state(self, dest);
                                }
                                ctrl.end_analysis();
                            }
                        } else if self.state == JoinParamState::BeforeVariantGet {
                            if this == self.current_arg1 && is_stack_address(arg1) {
                                self.state = JoinParamState::FindVariant;
                                let mut analysis = FuncAnalysis::new(ctrl.binary(), ctx, dest);
                                analysis.analyze(self);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            JoinParamState::FindVariant => {
                self.check_variant_type(ctrl, op);
                if self.result.is_some() {
                    return;
                }
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if this == ctx.register(1) && is_stack_address(arg1) {
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.is_some() {
                                ctrl.end_analysis();
                                return;
                            }
                            let dest = DestOperand::from_oper(ctrl.mem_word(arg1, 0));
                            let state = ctrl.exec_state();
                            state.move_resolved(&dest, ctx.custom(self.custom_pos));
                            self.custom_pos += 1;
                        } else {
                            let custom_off = [this, arg1].iter().find_map(|&op| {
                                let (l, r) = op.if_arithmetic_add()?;
                                l.if_custom()?;
                                r.if_constant().filter(|&c| c & 3 == 0)?;
                                Some(op)
                            });
                            if let Some(custom) = custom_off {
                                self.state = JoinParamState::FindVariantType;
                                self.current_variant = custom;
                                self.first_branch = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.first_branch = false;
                                self.state = JoinParamState::FindVariant;
                                if self.result.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                    ctrl.skip_call_preserve_esp();
                }
            }
            JoinParamState::FindVariantType => {
                self.check_variant_type(ctrl, op);
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> JoinParamVariantTypeOffset<'a, 'acx, 'e, E> {
    fn check_variant_type(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if let Operation::Call(dest) = *op {
            let dest = ctrl.resolve(dest);
            if let Some(mem) = ctrl.if_mem_word(dest) {
                if let Some(index_addr) = self.extract_index_from_call(mem) {
                    let offset = ctx.mem_sub_op(&index_addr, self.current_variant).if_constant()
                        .or_else(|| {
                            (0..3).find_map(|i| {
                                let arg = ctrl.resolve(self.arg_cache.on_call(i));
                                ctx.mem_sub_op(&index_addr, arg).if_constant()
                            })
                        });
                    if let Some(c) = offset {
                        if let Ok(c) = u16::try_from(c) {
                            self.result = Some(c);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
            }
            if self.first_branch {
                self.first_branch = false;
                if let Some(dest) = dest.if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    ctrl.analyze_with_current_state(self, dest);
                    if self.result.is_some() {
                        ctrl.end_analysis();
                    }
                }
            }
        } else if let Operation::Jump { condition, to } = *op {
            if self.state == JoinParamState::FindVariantType {
                self.first_branch = false;
                let condition = ctrl.resolve(condition);
                let compare = condition.if_arithmetic_eq_neq()
                    .filter(|x| x.1.if_constant() == Some(4))
                    .map(|x| x.0)
                    .and_then(|x| ctrl.if_mem_word(x));
                if let Some(op) = compare {
                    if let Some(c) = ctx.mem_sub_op(op, self.current_variant).if_constant() {
                        if let Ok(c) = u16::try_from(c) {
                            self.result = Some(c);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
                let to = ctrl.resolve(to);
                if to.if_constant().is_none() {
                    if let Some(switch) = CompleteSwitch::new(to, ctx, ctrl.exec_state()) {
                        if let Some(index) = switch.index_operand(ctx) {
                            if let Some(mem) = index.unwrap_sext().if_memory()
                                .filter(|mem| mem.address().0.if_custom().is_some())
                            {
                                if let Some(c) =
                                    ctx.mem_sub_op(mem, self.current_variant).if_constant()
                                {
                                    if let Ok(c) = u16::try_from(c) {
                                        self.result = Some(c);
                                        ctrl.end_analysis();
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn extract_index_from_call(&self, op: &MemAccess<'e>) -> Option<MemAccess<'e>> {
        let (base, _) = op.address();
        let mut ops = collect_arith_add_terms(base, self.bump);
        let op = ops.remove_get(|x, is_sub| {
            !is_sub && x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()).is_some()
        })?;
        op.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
            .and_then(|x| {
                let mem = x.if_memory()?;
                let (base, offset) = mem.address();
                if offset != 0 && base.if_custom().is_some() {
                    Some(*mem)
                } else {
                    None
                }
            })
    }
}

pub(crate) fn single_player_map_end<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    is_multiplayer: Operand<'e>,
    run_dialog: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> SinglePlayerMapEnd<'e, E::VirtualAddress> {
    let mut result = SinglePlayerMapEnd {
        single_player_map_end: None,
        local_game_result: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let funcs = functions.functions();
    let mut str_refs = functions.string_refs(actx, b"rez\\gluscore");
    if str_refs.is_empty() {
        str_refs = functions.string_refs(actx, b"gluscore.ui");
    }
    let arg_cache = &actx.arg_cache;
    for str_ref in &str_refs {
        entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = FindSpMapEnd::<E> {
                run_dialog,
                is_multiplayer,
                arg_cache,
                result: &mut result,
                state: FindSpMapEndState::Init,
                call_limit: 0,
                inline_depth: 0,
                inline_limit: 0,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if result.single_player_map_end.is_some() {
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        });
        if result.single_player_map_end.is_some() {
            break;
        }
    }
    result
}

struct FindSpMapEnd<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SinglePlayerMapEnd<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    is_multiplayer: Operand<'e>,
    run_dialog: E::VirtualAddress,
    state: FindSpMapEndState,
    call_limit: u8,
    inline_depth: u8,
    inline_limit: u8,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum FindSpMapEndState {
    /// Run until run_dialog(gluScore)
    Init,
    /// Run until is_multiplayer == 0 check, take only that branch.
    /// May inline to depth 1, which will contain both is_multiplayer check
    /// and single_player_map_end call then.
    RunDialogSeen,
    /// Search for single_player_map_end(local_game_result == 1)
    IsMultiplayerSeen,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSpMapEnd<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            FindSpMapEndState::Init => {
                if let Operation::Call(dest) = *op {
                    if ctrl.resolve_va(dest) == Some(self.run_dialog) {
                        ctrl.clear_unchecked_branches();
                        self.state = FindSpMapEndState::RunDialogSeen;
                        ctrl.do_call_with_result(ctx.constant(0xffff_fffd));
                    }
                } else if let Operation::Move(DestOperand::Memory(ref dest), _, None) = *op {
                    // Skip moves to globals, some versions write initial value to
                    // local_game_result here.
                    let dest = ctrl.resolve_mem(dest);
                    if dest.is_global() {
                        ctrl.skip_operation();
                    }
                }
            }
            FindSpMapEndState::RunDialogSeen => {
                if self.inline_limit != 0 {
                    match *op {
                        Operation::Jump { .. } | Operation::Call(..) => {
                            self.inline_limit -= 1;
                            if self.inline_limit == 0 {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        _ => (),
                    }
                }
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let eq_neq_zero = condition.if_arithmetic_eq_neq_zero(ctx);
                    let result = eq_neq_zero
                        .filter(|x| x.0 == self.is_multiplayer)
                        .map(|x| x.1);
                    let to = match ctrl.resolve_va(to) {
                        Some(s) => s,
                        None => return,
                    };
                    if let Some(jump_if_zero) = result {
                        ctrl.clear_unchecked_branches();
                        ctrl.end_branch();
                        let zero_addr = match jump_if_zero {
                            true => to,
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.add_branch_with_current_state(zero_addr);
                        self.state = FindSpMapEndState::IsMultiplayerSeen;
                        self.call_limit = 5;
                    } else {
                        // The codegen here may do `al == 0` check and
                        // from there on assume that al is 0.
                        if let Some((val, is_eq)) = eq_neq_zero {
                            let eax = ctrl.resolve_register(0);
                            let eax_update = if val == eax {
                                Some(ctx.const_0())
                            } else if ctx.and_const(eax, 0xff) == val {
                                Some(ctx.and_const(eax, !0xff))
                            } else {
                                None
                            };
                            if let Some(eax_update) = eax_update {
                                let end = ctrl.current_instruction_end();
                                let (zero_addr, nonzero_addr) = match is_eq {
                                    true => (to, end),
                                    false => (end, to),
                                };
                                ctrl.end_branch();
                                ctrl.add_branch_with_current_state(nonzero_addr);
                                ctrl.set_register(0, eax_update);
                                ctrl.add_branch_with_current_state(zero_addr);
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_depth = 1;
                            self.inline_limit = 10;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            if self.state != FindSpMapEndState::RunDialogSeen {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            FindSpMapEndState::IsMultiplayerSeen => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let result = arg1.if_arithmetic_eq_const(1)
                            .filter(|&x| is_global(x));
                        if let Some(result) = result {
                            self.result.single_player_map_end = Some(dest);
                            self.result.local_game_result = Some(result);
                            ctrl.end_analysis();
                        }
                    }
                    if self.call_limit == 0 {
                        ctrl.end_analysis();
                    } else {
                        self.call_limit -= 1;
                    }
                }
            }
        }
    }
}

pub(crate) fn single_player_map_end_analysis<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    sp_map_end: E::VirtualAddress,
) -> SinglePlayerMapEndAnalysis<'e, E::VirtualAddress> {
    let mut result = SinglePlayerMapEndAnalysis {
        set_scmain_state: None,
        unlock_mission: None,
        is_custom_single_player: None,
        current_campaign_mission: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;
    let mut analyzer = AnalyzeSpMapEnd::<E> {
        arg_cache,
        result: &mut result,
        state: SpMapEndState::SetScmainState,
        last_global_store: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, sp_map_end);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeSpMapEnd<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut SinglePlayerMapEndAnalysis<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: SpMapEndState,
    last_global_store: Option<(MemAccess<'e>, Operand<'e>)>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SpMapEndState {
    /// Find call for set_scmain_state(4)
    SetScmainState,
    /// Next comparision against 0 should be is_custom_single_player
    IsCustomSinglePlayer,
    /// Find call for unlock_mission(mission)
    /// where the mission should have just been stored to current_campaign_mission as well
    UnlockMission,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AnalyzeSpMapEnd<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            SpMapEndState::SetScmainState => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1.if_constant() == Some(4) {
                            self.result.set_scmain_state = Some(dest);
                            ctrl.clear_unchecked_branches();
                            self.state = SpMapEndState::IsCustomSinglePlayer;
                        }
                    }
                }
            }
            SpMapEndState::IsCustomSinglePlayer => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| is_global(x.0))
                        .map(|x| x.0);
                    if let Some(val) = result {
                        self.result.is_custom_single_player = Some(val);
                        self.state = SpMapEndState::UnlockMission;
                    }
                }
            }
            SpMapEndState::UnlockMission => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if let Some((addr, val)) = self.last_global_store.take() {
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            if arg1 == val {
                                self.result.current_campaign_mission = Some(ctx.memory(&addr));
                                self.result.unlock_mission = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref dest), val, None) = *op {
                    if dest.size == E::WORD_SIZE {
                        let dest = ctrl.resolve_mem(dest);
                        if dest.is_global() {
                            self.last_global_store = Some((dest, ctrl.resolve(val)));
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn init_map_from_path_analysis<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    init_map_from_path: E::VirtualAddress,
    is_replay: Operand<'e>,
    game: Operand<'e>,
) -> InitMapFromPathAnalysis<'e, E::VirtualAddress> {
    let mut result = InitMapFromPathAnalysis {
        read_whole_mpq_file: None,
        read_whole_mpq_file2: None,
        open_map_mpq: None,
        sfile_close_archive: None,
        load_replay_scenario_chk: None,
        replay_scenario_chk: None,
        replay_scenario_chk_size: None,
        map_mpq: None,
        map_history: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;
    let mut analyzer = AnalyzeInitMapFromPath::<E> {
        arg_cache,
        result: &mut result,
        is_replay,
        game,
        ctx,
        state: InitMapFromPathState::ReplayCheck,
        non_replay_branch: E::VirtualAddress::from_u64(0),
        non_replay_state: None,
        map_mpq_candidate: None,
        sfile_close_archive_candidate: E::VirtualAddress::from_u64(0),
        inlining_open_map_unk: false,
        inlining_read_map_file: false,
        inlining_open_global_map_mpq: false,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        inline_return: None,
        current_branch: init_map_from_path,
        cmp_zero_branches: bumpvec_with_capacity(32, &actx.bump),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_map_from_path);
    analysis.analyze(&mut analyzer);
    result
}

struct AnalyzeInitMapFromPath<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitMapFromPathAnalysis<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    is_replay: Operand<'e>,
    game: Operand<'e>,
    ctx: OperandCtx<'e>,
    state: InitMapFromPathState,
    non_replay_branch: E::VirtualAddress,
    non_replay_state: Option<E>,
    map_mpq_candidate: Option<Operand<'e>>,
    sfile_close_archive_candidate: E::VirtualAddress,
    inlining_open_map_unk: bool,
    inlining_read_map_file: bool,
    inlining_open_global_map_mpq: bool,
    call_tracker: CallTracker<'acx, 'e, E>,
    inline_return: Option<Operand<'e>>,
    current_branch: E::VirtualAddress,
    cmp_zero_branches: BumpVec<'acx, (E::VirtualAddress, Operand<'e>)>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum InitMapFromPathState {
    /// Find is_replay check
    ReplayCheck,
    /// On is_replay branch:
    /// load_replay_scenario_chk(replay_scenario_chk, replay_scenario_chk_size, 1, arg2)
    LoadReplayScenarioChk,
    /// On non-replay branch:
    /// Inline once if call is open_map_unk(arg1, arg2)
    /// Inline another time if calling open_global_map_mpq(_, _, _, is_campaign)
    /// (Which contains SfileCloseArchive and OpenMapMpq)
    /// Find sfile_close_archive(map_mpq), which is followed by map_mpq = 0
    SfileCloseArchive,
    /// open_map_mpq(arg1, _, _, is_campaign, _, _, &map_mpq)
    OpenMapMpq,
    /// Inline once if arg2 != constant to read_map_file,
    /// assume game.campaign_mission == 0 on jumps,
    /// find read_whole_mpq_file(map_mpq, _, _, _, 0, 0, 0)
    ReadWholeMpqFile,
    /// Write Custom(0) to arg 3 ptr of read_whole_mpq_file; have read_whole_mpq_file return 1.
    /// Then check for
    /// map_history_set_first_map_chk_hash(this = map_history, Custom(0), _)
    /// Since map_history is likely a lazily mallocated pointer, have also handling for that.
    /// But try to support non-pointer global if it ever is refactored to use that.
    MapHistory,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AnalyzeInitMapFromPath<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = self.ctx;
        let arg_cache = self.arg_cache;
        match self.state {
            InitMapFromPathState::ReplayCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| x.0 == self.is_replay)
                        .map(|x| x.1);
                    if let Some(jump_if_not_replay) = result {
                        let jump_dest = match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        };
                        let no_jump_dest = ctrl.current_instruction_end();
                        self.non_replay_state = Some(ctrl.exec_state().clone());
                        let (other_branch, replay_branch) = match jump_if_not_replay {
                            true => (jump_dest, no_jump_dest),
                            false => (no_jump_dest, jump_dest),
                        };
                        self.non_replay_branch = other_branch;
                        ctrl.clear_all_branches();
                        ctrl.end_branch();
                        ctrl.add_branch_with_current_state(replay_branch);
                        self.state = InitMapFromPathState::LoadReplayScenarioChk;
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), _, _) = *op {
                    // Skip writes to game.campaign_mission since it'll be checked later
                    let mem = ctrl.resolve_mem(mem);
                    let (base, offset) = mem.address();
                    if offset == 0x154 && base == self.game {
                        ctrl.skip_operation();
                    }
                }
            }
            InitMapFromPathState::LoadReplayScenarioChk => {
                if let Operation::Call(dest) = *op {
                    let ok = ctrl.resolve(arg_cache.on_call(2)) == ctx.const_1() &&
                        ctrl.resolve(arg_cache.on_call(3)) == arg_cache.on_entry(1);
                    if ok {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let arg1 = ctrl.resolve(arg_cache.on_call(0));
                            let arg2 = ctrl.resolve(arg_cache.on_call(1));
                            self.result.load_replay_scenario_chk = Some(dest);
                            self.result.replay_scenario_chk = Some(arg1);
                            self.result.replay_scenario_chk_size = Some(arg2);
                            self.state = InitMapFromPathState::SfileCloseArchive;
                            ctrl.clear_all_branches();
                            ctrl.end_branch();
                            if let Some(state) = self.non_replay_state.take() {
                                *ctrl.exec_state() = state;
                                ctrl.add_branch_with_current_state(self.non_replay_branch);
                            }
                        }
                    }
                }
            }
            InitMapFromPathState::SfileCloseArchive => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(arg_cache.on_call(0));
                        if !self.inlining_open_map_unk {
                            let inline = arg1 == arg_cache.on_entry(0) &&
                                ctrl.resolve(arg_cache.on_call(1)) == arg_cache.on_entry(1);
                            if inline {
                                self.inlining_open_map_unk = true;
                                ctrl.analyze_with_current_state(self, dest);
                                if self.result.sfile_close_archive.is_some() {
                                    ctrl.end_analysis();
                                    return;
                                }
                                self.inlining_open_map_unk = false;
                            }
                        }
                        if !self.inlining_open_global_map_mpq {
                            let arg3 = ctx.and_const(
                                ctrl.resolve(arg_cache.on_call(2)),
                                0xff,
                            );
                            let arg3_campaign_mission =
                                self.check_campaign_mission_cmp(arg3).is_some();
                            if arg3_campaign_mission {
                                self.inlining_open_global_map_mpq = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inlining_open_global_map_mpq = false;
                                if self.state != InitMapFromPathState::SfileCloseArchive {
                                    ctrl.clear_unchecked_branches();
                                }
                            }
                        }
                        if is_global(arg1) {
                            self.map_mpq_candidate = Some(arg1);
                            self.sfile_close_archive_candidate = dest;
                        } else {
                            self.map_mpq_candidate = None;
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value, None) = *op {
                    if let Some(cand) = self.map_mpq_candidate {
                        if ctrl.resolve(value) == ctx.const_0() {
                            if let Some(cand_mem) = cand.if_memory() {
                                let mem = ctrl.resolve_mem(mem);
                                if *cand_mem == mem {
                                    self.result.map_mpq = Some(cand);
                                    self.result.sfile_close_archive =
                                        Some(self.sfile_close_archive_candidate);
                                    self.state = InitMapFromPathState::OpenMapMpq;
                                    ctrl.clear_unchecked_branches();
                                    // Keep map_mpq as unknown, not-zero
                                    ctrl.skip_operation();
                                }
                            }
                        }
                    }
                }
            }
            InitMapFromPathState::OpenMapMpq => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg3 = ctx.and_const(
                            ctrl.resolve(arg_cache.on_call(2)),
                            0xff,
                        );
                        let arg3_campaign_mission =
                            self.check_campaign_mission_cmp(arg3).is_some();
                        let ok = ctrl.resolve(arg_cache.on_call(0)) == arg_cache.on_entry(0) &&
                            arg3_campaign_mission &&
                            self.check_map_mpq_addr(ctrl.resolve(arg_cache.on_call(6)));
                        if ok {
                            self.result.open_map_mpq = Some(dest);
                            self.state = InitMapFromPathState::ReadWholeMpqFile;
                            if self.inlining_open_global_map_mpq {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            InitMapFromPathState::ReadWholeMpqFile => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = Some(ctrl.resolve(arg_cache.on_call(0))) ==
                                self.result.map_mpq &&
                            (4..7).all(|i| {
                                ctx.and_const(
                                    ctrl.resolve(arg_cache.on_call(i)),
                                    0xffff_ffff,
                                ) == ctx.const_0()
                            });
                        if ok {
                            self.check_read_whole_mpq_file(ctrl, dest);
                            self.state = InitMapFromPathState::MapHistory;
                            let arg = ctrl.resolve(arg_cache.on_call(2));
                            ctrl.move_resolved(
                                &DestOperand::Memory(ctx.mem_access(arg, 0, E::WORD_SIZE)),
                                ctx.custom(0),
                            );
                            ctrl.do_call_with_result(ctx.const_1());
                            return;
                        }
                        if !self.inlining_read_map_file {
                            let arg2 = ctrl.resolve(arg_cache.on_call(1));
                            if arg2.if_constant().is_none() {
                                self.inlining_read_map_file = true;
                                ctrl.inline(self, dest);
                                ctrl.skip_operation();
                                if self.state != InitMapFromPathState::ReadWholeMpqFile {
                                    ctrl.clear_unchecked_branches();
                                }
                                self.inlining_read_map_file = false;
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some(jump_if_not_campaign) =
                        self.check_campaign_mission_cmp(condition)
                    {
                        let not_campaign_addr = match jump_if_not_campaign {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.end_branch();
                        ctrl.add_branch_with_current_state(not_campaign_addr);
                    }
                }
            }
            InitMapFromPathState::MapHistory => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let tc_arg1 = ctrl.resolve(arg_cache.on_thiscall_call(0));
                        if tc_arg1.if_custom() == Some(0) {
                            let tc_arg2 = ctrl.resolve(arg_cache.on_thiscall_call(1));
                            // Arg2 should be map data length; so not global
                            if !is_global(tc_arg2) {
                                let this = ctrl.resolve_register(1);
                                let this = if let Some(c) = this.if_custom() {
                                    if let Some(func) = self.call_tracker.custom_id_to_func(c) {
                                        self.map_history_from_get_fn(ctrl, func)
                                    } else {
                                        this
                                    }
                                } else {
                                    this
                                };
                                if is_global(this) {
                                    self.result.map_history = Some(this);
                                    ctrl.end_analysis();
                                    return;
                                }
                            }
                        } else {
                            let arg1 = ctrl.resolve(arg_cache.on_call(0));
                            let constant = arg1.if_constant()
                                .or_else(|| {
                                    // 64bit does `lea rcx, [rax + C]` in branch
                                    // where rax was just known to be zero.
                                    let zero_op = self.cmp_zero_branches
                                        .iter()
                                        .find(|x| x.0 == self.current_branch)
                                        .map(|x| x.1)?;
                                    ctx.substitute(arg1, zero_op, ctx.const_0(), 8)
                                        .if_constant()
                                });
                            if let Some(c) = constant {
                                if c > 8 && c < 0x100 {
                                    // Assume malloc initilziation call that is on
                                    // branch that can be skipped
                                    ctrl.end_branch();
                                    return;
                                }
                            }
                        }
                        self.call_tracker.add_call_preserve_esp(ctrl, dest);
                    }
                } else if let Operation::Return(..) = *op {
                    let ret = ctrl.resolve_register(0);
                    if let Some(old) = self.inline_return {
                        if !old.is_undefined() && old != ret {
                            self.inline_return = Some(ctx.new_undef());
                        }
                    } else {
                        self.inline_return = Some(ret);
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((op, jump_if_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        let zero_addr = match jump_if_zero {
                            true => match ctrl.resolve_va(to) {
                                Some(s) => s,
                                None => return,
                            },
                            false => ctrl.current_instruction_end(),
                        };
                        self.cmp_zero_branches.push((zero_addr, op));
                    }
                }
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.current_branch = ctrl.address();
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> AnalyzeInitMapFromPath<'a, 'acx, 'e, E> {
    fn check_campaign_mission_cmp(&mut self, op: Operand<'e>) -> Option<bool> {
       op.if_arithmetic_eq_neq_zero(self.ctx)
            .filter(|x| x.0.if_mem16_offset(0x154) == Some(self.game))
            .map(|x| x.1)
    }

    /// Only returns valid value once map_mpq is in result
    fn check_map_mpq_addr(&mut self, op: Operand<'e>) -> bool {
        if let Some(map_mpq) = self.result.map_mpq.and_then(|x| x.if_memory()) {
            self.ctx.mem_access(op, 0, E::WORD_SIZE) == *map_mpq
        } else {
            false
        }
    }

    /// Checks if func is read_whole_mpq_file (7 args) or read_whole_mpq_file2 (8 args)
    /// If the function immediately calls another function with same arg 1-7 and 0 for arg8,
    /// assume func to be 7 arg one and callee be 8 arg one.
    ///
    /// Otherwise:
    ///     - On 32bit return stack pop is used to determine arg count
    ///     - On 64bit the entire function would have to be scanned for arg8 access,
    ///         but since the calling convention is nicer we just guess it is
    ///         read_whole_mpq_file2 if arg 8 is 0
    fn check_read_whole_mpq_file(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        func: E::VirtualAddress,
    ) {
        let ctx = self.ctx;
        let binary = ctrl.binary();
        let mut analyzer = CheckReadWholeMpqFile::<E> {
            arg_cache: self.arg_cache,
            func,
            result: &mut self.result,
            first_call: true,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if E::VirtualAddress::SIZE == 8 && self.result.read_whole_mpq_file.is_none() {
            // Didn't get result where both of them are something; assume
            // 8 args if value in arg8 place is currently 0.
            let arg8 = ctx.and_const(ctrl.resolve(self.arg_cache.on_call(7)), 0xffff_ffff);
            if arg8 == ctx.const_0() {
                self.result.read_whole_mpq_file2 = Some(func);
            } else {
                self.result.read_whole_mpq_file = Some(func);
            }
        }
    }

    fn map_history_from_get_fn(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        func: E::VirtualAddress,
    ) -> Operand<'e> {
        let ctx = ctrl.ctx();
        let binary = ctrl.binary();
        self.inline_return = None;
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(self);
        self.inline_return.unwrap_or_else(|| ctx.new_undef())
    }
}

struct CheckReadWholeMpqFile<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitMapFromPathAnalysis<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    first_call: bool,
    func: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CheckReadWholeMpqFile<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if self.first_call {
                self.first_call = false;
                let ctx = ctrl.ctx();
                if (0..7).all(|i| {
                    let arg = ctrl.resolve(self.arg_cache.on_call(i));
                    let entry_arg = self.arg_cache.on_entry(i);
                    // u32 args are likely just moved as u32, so mask both sides when
                    // checking if they're equal
                    if i == 4 || i == 5 {
                        ctx.and_const(arg, 0xffff_ffff) == ctx.and_const(entry_arg, 0xffff_ffff)
                    } else {
                        arg == entry_arg
                    }
                }) {
                    let arg8 =
                        ctx.and_const(ctrl.resolve(self.arg_cache.on_call(7)), 0xffff_ffff);
                    if arg8 == ctx.const_0() {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.result.read_whole_mpq_file = Some(self.func);
                            self.result.read_whole_mpq_file2 = Some(dest);
                            ctrl.end_analysis();
                            return;
                        }
                    }
                }
                if E::VirtualAddress::SIZE == 8 {
                    // fn check_read_whole_mpq_file handles rest if this didn't result in
                    // anything.
                    ctrl.end_analysis();
                    return;
                }
            }
        }
        if E::VirtualAddress::SIZE == 4 {
            if let Operation::Return(stack_pop) = *op {
                if stack_pop == 0x1c {
                    self.result.read_whole_mpq_file = Some(self.func);
                } else if stack_pop == 0x20 {
                    self.result.read_whole_mpq_file2 = Some(self.func);
                }
                ctrl.end_analysis();
            }
        }
    }
}

pub(crate) fn join_custom_game<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    join_game: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> JoinCustomGame<E::VirtualAddress> {
    let mut result = JoinCustomGame {
        join_custom_game: None,
        find_file_with_crc: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;

    let callers = functions.find_callers(actx, join_game);
    let funcs = functions.functions();
    for caller in callers {
        let new = entry_of_until(binary, funcs, caller, |entry| {
            let mut analyzer = JoinCustomGameAnalyzer::<E> {
                arg_cache,
                result: &mut result,
                entry_of: EntryOf::Retry,
                inline_depth: 0,
                join_game,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);

        if single_result_assign(new, &mut result.join_custom_game) {
            break;
        }
    }

    result
}

struct JoinCustomGameAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut JoinCustomGame<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    entry_of: EntryOf<()>,
    inline_depth: u8,
    join_game: E::VirtualAddress,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for JoinCustomGameAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // join_custom_game should start with call
        // to find_map_with_crc(_, size, crc, &stack_string) (Maybe inlined)
        //      - size and crc are from arg2, will be replaced with custom
        //      which calls find_file_with_crc(_, size, crc, &dirs, 3, &stack_string)
        let ctx = ctrl.ctx();
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                if matches!(self.entry_of, EntryOf::Retry) {
                    if dest == self.join_game {
                        self.entry_of = EntryOf::Stop;
                        ctrl.end_analysis();
                        return;
                    }
                }
                let this = ctrl.resolve_register(1);
                if this == self.arg_cache.on_entry(1) {
                    ctrl.do_call_with_result(ctx.custom(0));
                    return;
                }
                let is_crc_call = ctrl.resolve(self.arg_cache.on_call(1))
                        .unwrap_and_mask().if_custom() == Some(0) &&
                    ctrl.resolve(self.arg_cache.on_call(2))
                        .unwrap_and_mask().if_custom() == Some(0);
                if is_crc_call {
                    if ctrl.resolve(self.arg_cache.on_call_u32(4)).if_constant() == Some(3) {
                        self.entry_of = EntryOf::Ok(());
                        single_result_assign(Some(dest), &mut self.result.find_file_with_crc);
                        ctrl.end_analysis();
                    } else {
                        // find_map_with_crc
                        if self.inline_depth == 0 {
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
        if matches!(self.entry_of, EntryOf::Retry) {
            if let Operation::Jump { condition, to } = *op {
                if condition == ctx.const_1() &&
                    ctrl.resolve_register(4) == ctx.register(4) &&
                    ctrl.resolve_va(to) == Some(self.join_game)
                {
                    // Tail call
                    self.entry_of = EntryOf::Stop;
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) fn analyze_find_file_with_crc<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    find_file_with_crc: E::VirtualAddress,
) -> FindFileWithCrc<E::VirtualAddress> {
    let mut result = FindFileWithCrc {
        for_files_in_dir: None,
        simple_file_match_callback: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;

    let mut analyzer = FindFileWithCrcAnalyzer::<E> {
        arg_cache,
        result: &mut result,
        inline_depth: 0,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, find_file_with_crc);
    analysis.analyze(&mut analyzer);

    result
}

struct FindFileWithCrcAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut FindFileWithCrc<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindFileWithCrcAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // find_file_with_crc calls
        // find_files_simple(a1 = a1, in_out_dir, 0x104, file_crc_equals, ctx) which calls
        // for_files_in_dir(in_out_dir, "*", simple_file_match_callback, 0, 1, &ctx)
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let a2 = ctrl.resolve(self.arg_cache.on_call(1));
                let a3 = ctrl.resolve(self.arg_cache.on_call(2));
                let a4 = ctrl.resolve(self.arg_cache.on_call(3));
                let a5 = ctrl.resolve(self.arg_cache.on_call(4));
                let binary = ctrl.binary();
                let ctx = ctrl.ctx();
                let is_for_files_in_dir = a2.if_constant()
                        .and_then(|c| binary.read_u16(E::VirtualAddress::from_u64(c)).ok())
                        .is_some_and(|x| x == 0x2a) &&
                    ctx.and_const(a4, 0xff) == ctx.const_0() &&
                    ctx.and_const(a5, 0xff) == ctx.const_1();
                if is_for_files_in_dir {
                    if let Some(cb) = a3.if_constant() {
                        let cb = E::VirtualAddress::from_u64(cb);
                        self.result.for_files_in_dir = Some(dest);
                        self.result.simple_file_match_callback = Some(cb);
                        ctrl.end_analysis();
                    }
                    return;
                }
                let is_find_files_simple =
                    self.inline_depth == 0 &&
                    ctx.and_const(a3, 0xffff_ffff).if_constant() == Some(0x104) &&
                    a4.if_constant().is_some();
                if is_find_files_simple {
                    self.inline_depth = 1;
                    ctrl.analyze_with_current_state(self, dest);
                    self.inline_depth = 0;
                    ctrl.end_analysis();
                }
            }
        }
    }
}
