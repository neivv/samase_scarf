#![allow(clippy::style, clippy::filter_next, clippy::identity_op,
    clippy::trivially_copy_pass_by_ref, clippy::nonminimal_bool)]

#[macro_use] extern crate log;

#[cfg(not(feature = "test_assertions"))]
macro_rules! test_assert_eq {
    ($($toks:tt)*) => {}
}

#[cfg(feature = "test_assertions")]
macro_rules! test_assert_eq {
    ($($toks:tt)*) => {
        assert_eq!($($toks)*)
    }
}

mod add_terms;
mod ai;
mod bullets;
mod campaign;
mod clientside;
mod commands;
mod crt;
mod dialog;
mod eud;
mod file;
mod firegraft;
mod game;
mod game_init;
mod hash_map;
mod iscript;
mod map;
mod minimap;
mod network;
mod pathing;
mod players;
mod range_list;
mod renderer;
mod requirements;
mod rng;
mod save;
mod sound;
mod step_order;
mod sprites;
mod switch;
mod text;
mod units;
mod vtables;

pub mod dat;

use std::rc::Rc;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;
use byteorder::{ReadBytesExt, LE};

use scarf::{BinaryFile, Operand, Rva};
use scarf::analysis::{self, Control, FuncCallPair, RelocValues};
use scarf::operand::{MemAccessSize, OperandCtx};

pub use scarf;
pub use scarf::{BinarySection, VirtualAddress};
pub use crate::ai::AiScriptHook;
pub use crate::bullets::BulletCreation;
pub use crate::clientside::{GameScreenRClick, GameCoordConversion, MiscClientSide};
pub use crate::commands::{ProcessCommands, Selections, StepNetwork};
pub use crate::dat::{
    DatTablePtr, DatPatch, DatPatches, DatArrayPatch, DatEntryCountPatch, DatReplaceFunc
};
pub use crate::dialog::{MouseXy, TooltipRelated};
pub use crate::eud::{Eud, EudTable};
pub use crate::firegraft::RequirementTables;
pub use crate::game::{Limits};
pub use crate::game_init::{GameInit, InitGame, ImagesLoaded, SinglePlayerStart, SelectMapEntry};
pub use crate::iscript::StepIscript;
pub use crate::map::MapTileFlags;
pub use crate::network::{InitStormNetworking, SnpDefinitions};
pub use crate::pathing::RegionRelated;
pub use crate::players::NetPlayers;
pub use crate::renderer::{PrismShaders};
pub use crate::rng::Rng;
pub use crate::save::{SpriteSerialization};
pub use crate::step_order::{SecondaryOrderHook, StepOrderHiddenHook};
pub use crate::sprites::{FowSprites, InitSprites, Sprites};
pub use crate::text::{FontRender};
pub use crate::units::{ActiveHiddenUnits, InitUnits, OrderIssuing, UnitCreation};

use crate::dialog::{MultiWireframes};
use crate::game_init::{InitMapFromPath};
use crate::map::{RunTriggers, TriggerUnitCountCaches};
use crate::network::{SnetHandlePackets};
use crate::switch::{CompleteSwitch, full_switch_info};

use scarf::exec_state::ExecutionState as ExecutionStateTrait;
use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

pub fn test_assertions() -> bool {
    cfg!(feature = "test_assertions")
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FiregraftAddresses<Va: VirtualAddressTrait> {
    pub buttonsets: Vec<Va>,
    pub requirement_table_refs: RequirementTables<Va>,
    pub unit_status_funcs: Vec<Va>,
}

#[derive(Clone, Debug)]
pub struct Patch<Va: VirtualAddressTrait> {
    pub address: Va,
    pub data: Vec<u8>,
}

// Just since option spam for caches is a bit hard to keep track of
struct Cached<T: Clone>(Option<T>);

impl<T: Clone> Cached<T> {
    pub fn get_or_insert_with<F: FnOnce() -> T>(&mut self, fun: F) -> &mut T {
        self.0.get_or_insert_with(fun)
    }

    pub fn cached(&self) -> Option<T> {
        self.0.clone()
    }

    pub fn cached_ref(&self) -> Option<&T> {
        self.0.as_ref()
    }

    pub fn cache(&mut self, val: &T) {
        self.0 = Some(val.clone());
    }

    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }
}

impl<T: Clone> Default for Cached<T> {
    fn default() -> Cached<T> {
        Cached(None)
    }
}

#[cfg(feature = "x86")]
pub struct AnalysisX86<'e>(pub Analysis<'e, scarf::ExecutionStateX86<'e>>);

// Using repr(C) to make sure that the large, less accessed cache is placed last
// in this struct's layout
#[repr(C)]
pub struct Analysis<'e, E: ExecutionStateTrait<'e>> {
    shareable: AnalysisCtx<'e, E>,
    cache: AnalysisCache<'e, E>,
}

pub(crate) struct AnalysisCtx<'e, E: ExecutionStateTrait<'e>> {
    binary: &'e BinaryFile<E::VirtualAddress>,
    binary_sections: BinarySections<'e, E>,
    ctx: scarf::OperandCtx<'e>,
    arg_cache: ArgCache<'e, E>,
    bump: Bump,
}

struct BinarySections<'e, E: ExecutionStateTrait<'e>> {
    text: &'e BinarySection<E::VirtualAddress>,
    data: &'e BinarySection<E::VirtualAddress>,
    rdata: &'e BinarySection<E::VirtualAddress>,
}

macro_rules! results {
    (enum $name:ident {
        $($variant:ident => $variant_name:expr,)*
    }) => {
        #[derive(Copy, Clone, Debug)]
        pub enum $name {
            $($variant,)*
            _Last,
        }

        impl $name {
            pub fn name(self) -> &'static str {
                match self {
                    $($name::$variant => $variant_name,)*
                    $name::_Last => "",
                }
            }

            pub fn iter() -> impl Iterator<Item = $name> {
                static ITEMS: [$name; $name::_Last as usize] = [
                    $($name::$variant,)*
                ];
                ITEMS.iter().copied()
            }
        }
    };
}

results! {
    enum AddressAnalysis {
        StepObjects => "step_objects",
        SendCommand => "send_command",
        PrintText => "print_text",
        StepOrder => "step_order",
        DrawImage => "draw_image",
        PlaySmk => "play_smk",
        AddOverlayIscript => "add_overlay_iscript",
        RunDialog => "run_dialog",
        AiUpdateAttackTarget => "ai_update_attack_target",
        IsOutsideGameScreen => "is_outside_game_screen",
        ChooseSnp => "choose_snp",
        LoadImages => "load_images",
        InitGameNetwork => "init_game_network",
        SpawnDialog => "spawn_dialog",
        TtfMalloc => "ttf_malloc",
        DrawGraphicLayers => "draw_graphic_layers",
        AiAttackPrepare => "ai_attack_prepare",
        JoinGame => "join_game",
        SnetInitializeProvider => "snet_initialize_provider",
        CheckDatRequirements => "check_dat_requirements",
        GiveAi => "give_ai",
        PlaySound => "play_sound",
        AiPrepareMovingTo => "ai_prepare_moving_to",
        StepReplayCommands => "step_replay_commands",
        AiTrainMilitary => "ai_train_military",
        AiAddMilitaryToRegion => "ai_add_military_to_region",
    }
}

results! {
    enum OperandAnalysis {
        Game => "game",
        Pathing => "pathing",
        CommandUser => "command_user",
        IsReplay => "is_replay",
        LocalPlayerId => "local_player_id",
        LocalPlayerName => "local_player_name",
        LobbyState => "lobby_state",
        DrawCursorMarker => "draw_cursor_marker",
        Units => "units",
        FirstAiScript => "first_ai_script",
        FirstGuardAi => "first_guard_ai",
        PlayerAiTowns => "player_ai_towns",
        PlayerAi => "player_ai",
        Players => "players",
        Campaigns => "campaigns",
        Fonts => "fonts",
        StatusScreenMode => "status_screen_mode",
        CheatFlags => "cheat_flags",
        UnitStrength => "unit_strength",
        WireframDdsgrp => "wirefram_ddsgrp",
        ChkInitPlayers => "chk_init_players",
        OriginalChkPlayerTypes => "original_chk_player_types",
        AiTransportReachabilityCachedRegion => "ai_transport_reachability_cached_region",
        PlayerUnitSkins => "player_unit_skins",
        ReplayData => "replay_data",
        VertexBuffer => "vertex_buffer",
    }
}

struct AnalysisCache<'e, E: ExecutionStateTrait<'e>> {
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    relocs: Cached<Rc<Vec<E::VirtualAddress>>>,
    relocs_with_values: Cached<Rc<Vec<RelocValues<E::VirtualAddress>>>>,
    functions: Cached<Rc<Vec<E::VirtualAddress>>>,
    functions_with_callers: Cached<Rc<Vec<FuncCallPair<E::VirtualAddress>>>>,
    switch_tables: Cached<Rc<Vec<SwitchTable<E::VirtualAddress>>>>,
    open_file: Cached<Rc<Vec<E::VirtualAddress>>>,
    firegraft_addresses: Cached<Rc<FiregraftAddresses<E::VirtualAddress>>>,
    aiscript_hook: Cached<Rc<Option<AiScriptHook<'e, E::VirtualAddress>>>>,
    rng: Cached<Rc<Rng<'e>>>,
    // 0 = Not calculated, 1 = Not found
    address_results: [E::VirtualAddress; AddressAnalysis::_Last as usize],
    // None = Not calculated, Custom(1234578) = Not found
    operand_results: [Option<Operand<'e>>; OperandAnalysis::_Last as usize],
    operand_not_found: Operand<'e>,
    regions: Cached<Rc<RegionRelated<'e, E::VirtualAddress>>>,
    active_hidden_units: Cached<Rc<ActiveHiddenUnits<'e>>>,
    order_issuing: Cached<Rc<OrderIssuing<E::VirtualAddress>>>,
    process_commands: Cached<Rc<ProcessCommands<'e, E::VirtualAddress>>>,
    command_lengths: Cached<Rc<Vec<u32>>>,
    selections: Cached<Rc<Selections<'e>>>,
    process_lobby_commands: Cached<Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)>>,
    step_order_hidden: Cached<Rc<Vec<StepOrderHiddenHook<'e, E::VirtualAddress>>>>,
    init_units: Cached<InitUnits<E::VirtualAddress>>,
    step_secondary_order: Cached<Rc<Vec<SecondaryOrderHook<'e, E::VirtualAddress>>>>,
    init_game: Cached<Rc<InitGame<'e, E::VirtualAddress>>>,
    game_screen_rclick: Cached<Rc<GameScreenRClick<'e, E::VirtualAddress>>>,
    step_iscript: Cached<Rc<StepIscript<'e, E::VirtualAddress>>>,
    sprites: Cached<Rc<Sprites<'e, E::VirtualAddress>>>,
    eud: Cached<Rc<EudTable<'e>>>,
    map_tile_flags: Cached<Rc<MapTileFlags<'e, E::VirtualAddress>>>,
    renderer_vtables: Cached<Rc<Vec<E::VirtualAddress>>>,
    bullet_creation: Cached<Rc<BulletCreation<'e, E::VirtualAddress>>>,
    net_players: Cached<Rc<NetPlayers<'e, E::VirtualAddress>>>,
    game_init: Cached<Rc<GameInit<'e, E::VirtualAddress>>>,
    game_coord_conversion: Cached<Rc<GameCoordConversion<'e>>>,
    fow_sprites: Cached<Rc<FowSprites<'e>>>,
    init_map_from_path: Cached<Option<InitMapFromPath<E::VirtualAddress>>>,
    single_player_start: Cached<Rc<SinglePlayerStart<'e, E::VirtualAddress>>>,
    select_map_entry: Cached<Rc<SelectMapEntry<'e, E::VirtualAddress>>>,
    images_loaded: Cached<ImagesLoaded<'e, E::VirtualAddress>>,
    step_network: Cached<Rc<StepNetwork<'e, E::VirtualAddress>>>,
    snp_definitions: Cached<Option<SnpDefinitions<'e>>>,
    init_storm_networking: Cached<Rc<InitStormNetworking<E::VirtualAddress>>>,
    misc_clientside: Cached<Rc<MiscClientSide<'e>>>,
    unit_creation: Cached<Rc<UnitCreation<E::VirtualAddress>>>,
    init_sprites: Cached<InitSprites<'e, E::VirtualAddress>>,
    sprite_serialization: Cached<SpriteSerialization<E::VirtualAddress>>,
    limits: Cached<Rc<Limits<'e, E::VirtualAddress>>>,
    font_render: Cached<FontRender<E::VirtualAddress>>,
    create_game_dialog_vtbl_on_multiplayer_create: Cached<Option<usize>>,
    tooltip_related: Cached<TooltipRelated<'e, E::VirtualAddress>>,
    prism_shaders: Cached<PrismShaders<E::VirtualAddress>>,
    ai_step_frame_funcs: Cached<ai::AiStepFrameFuncs<E::VirtualAddress>>,
    do_attack: Cached<Option<step_order::DoAttack<'e, E::VirtualAddress>>>,
    dat_patches: Cached<Option<Rc<DatPatches<'e, E::VirtualAddress>>>>,
    button_ddsgrps: Cached<dialog::ButtonDdsgrps<'e>>,
    mouse_xy: Cached<dialog::MouseXy<'e, E::VirtualAddress>>,
    check_unit_requirements:
        Cached<Option<requirements::CheckUnitRequirements<'e, E::VirtualAddress>>>,
    multi_wireframes: Cached<MultiWireframes<'e, E::VirtualAddress>>,
    run_triggers: Cached<RunTriggers<E::VirtualAddress>>,
    trigger_unit_count_caches: Cached<TriggerUnitCountCaches<'e>>,
    snet_handle_packets: Cached<SnetHandlePackets<E::VirtualAddress>>,
    replay_minimap_unexplored_fog_patch: Cached<Option<Rc<Patch<E::VirtualAddress>>>>,
    crt_fastfail: Cached<Rc<Vec<E::VirtualAddress>>>,
    dat_tables: DatTables<'e>,
}

struct ArgCache<'e, E: ExecutionStateTrait<'e>> {
    args: Vec<Operand<'e>>,
    ctx: scarf::OperandCtx<'e>,
    phantom: std::marker::PhantomData<E>,
}

impl<'e, E: ExecutionStateTrait<'e>> ArgCache<'e, E> {
    fn new(ctx: OperandCtx<'e>) -> ArgCache<'e, E> {
        let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
        let stack_pointer = ctx.register(4);
        let args = (0..8).map(|i| {
            if is_x64 {
                match i {
                    0 => ctx.register(1),
                    1 => ctx.register(2),
                    2 => ctx.register(8),
                    3 => ctx.register(9),
                    _ => ctx.mem64(ctx.add(
                        stack_pointer,
                        ctx.constant(i * 8),
                    )),
                }
            } else {
                ctx.mem32(ctx.add(
                    stack_pointer,
                    ctx.constant(i * 4),
                ))
            }
        }).collect();
        ArgCache {
            args,
            ctx,
            phantom: std::marker::PhantomData,
        }
    }

    /// Returns operand corresponding to location of argument *before* call instruction
    /// is executed.
    pub fn on_call(&self, index: u8) -> Operand<'e> {
        if (index as usize) < self.args.len() {
            self.args[index as usize]
        } else {
            let size = <E::VirtualAddress as VirtualAddressTrait>::SIZE as u64;
            let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
            let stack_pointer = self.ctx.register(4);
            let mem_size = match is_x64 {
                true => MemAccessSize::Mem64,
                false => MemAccessSize::Mem32,
            };
            self.ctx.mem_variable_rc(mem_size, self.ctx.add(
                stack_pointer,
                self.ctx.constant(index as u64 * size),
            ))
        }
    }

    /// Returns operand corresponding to location of argument *on function entry*.
    pub fn on_entry(&self, index: u8) -> Operand<'e> {
        let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
        let ctx = self.ctx;
        let stack_pointer = ctx.register(4);
        if !is_x64 {
            if index as usize + 1 < self.args.len() {
                self.args[index as usize + 1]
            } else {
                ctx.mem32(ctx.add(
                    stack_pointer,
                    ctx.constant((index as u64 + 1) * 4),
                ))
            }
        } else {
            if index < 4 {
                self.args[index as usize]
            } else {
                ctx.mem64(ctx.add(
                    stack_pointer,
                    ctx.constant((index as u64 + 1) * 8),
                ))
            }
        }
    }
}

macro_rules! declare_dat {
    ($($struct_field:ident, $filename:expr, $enum_variant:ident,)*) => {
        struct DatTables<'e> {
            $($struct_field: Option<Option<DatTablePtr<'e>>>,)*
        }

        impl<'e> DatTables<'e> {
            fn new() -> DatTables<'e> {
                DatTables {
                    $($struct_field: None,)*
                }
            }

            fn field(&mut self, field: DatType) ->
                (&mut Option<Option<DatTablePtr<'e>>>, &'static str)
            {
                match field {
                    $(DatType::$enum_variant =>
                      (&mut self.$struct_field, concat!("arr\\", $filename)),)*
                }
            }
        }

        #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
        pub enum DatType {
            $($enum_variant,)*
        }
    }
}

declare_dat! {
    units, "units.dat", Units,
    weapons, "weapons.dat", Weapons,
    flingy, "flingy.dat", Flingy,
    upgrades, "upgrades.dat", Upgrades,
    techdata, "techdata.dat", TechData,
    sprites, "sprites.dat", Sprites,
    images, "images.dat", Images,
    orders, "orders.dat", Orders,
    sfxdata, "sfxdata.dat", SfxData,
    portdata, "portdata.dat", PortData,
    mapdata, "mapdata.dat", MapData,
}

#[derive(Clone, Debug)]
pub struct SwitchTable<Va: VirtualAddressTrait> {
    address: Va,
    cases: Vec<Va>,
}

// When not testing, immediatly end once a value is found, for tests require all values
// to be same.
#[cfg(not(feature = "test_assertions"))]
fn single_result_assign<T: Eq>(new: Option<T>, old: &mut Option<T>) -> bool
where T: std::fmt::Debug + PartialEq,
{
    if new.is_some() {
        *old = new;
        true
    } else {
        false
    }
}

#[cfg(feature = "test_assertions")]
fn single_result_assign<T>(new: Option<T>, old: &mut Option<T>) -> bool
where T: std::fmt::Debug + PartialEq,
{
    if let Some(new) = new {
        if let Some(ref old) = *old {
            assert_eq!(*old, new, "Received different results:\nOLD: {:#?}\nNEW: {:#?}", old, new);
        }
        *old = Some(new);
    }
    false
}

impl<'e, E: ExecutionStateTrait<'e>> Analysis<'e, E> {
    pub fn new(
        binary: &'e BinaryFile<E::VirtualAddress>,
        ctx: scarf::OperandCtx<'e>,
    ) -> Analysis<'e, E> {
        let text = binary.section(b".text\0\0\0").unwrap();
        Analysis {
            cache: AnalysisCache {
                binary,
                text,
                relocs: Default::default(),
                relocs_with_values: Default::default(),
                functions: Default::default(),
                functions_with_callers: Default::default(),
                switch_tables: Default::default(),
                open_file: Default::default(),
                firegraft_addresses: Default::default(),
                aiscript_hook: Default::default(),
                rng: Default::default(),
                address_results:
                    [E::VirtualAddress::from_u64(0); AddressAnalysis::_Last as usize],
                operand_results: [None; OperandAnalysis::_Last as usize],
                operand_not_found: ctx.custom(0x12345678),
                regions: Default::default(),
                active_hidden_units: Default::default(),
                order_issuing: Default::default(),
                process_commands: Default::default(),
                command_lengths: Default::default(),
                selections: Default::default(),
                process_lobby_commands: Default::default(),
                step_order_hidden: Default::default(),
                step_secondary_order: Default::default(),
                init_units: Default::default(),
                game_screen_rclick: Default::default(),
                init_game: Default::default(),
                step_iscript: Default::default(),
                sprites: Default::default(),
                eud: Default::default(),
                map_tile_flags: Default::default(),
                renderer_vtables: Default::default(),
                bullet_creation: Default::default(),
                net_players: Default::default(),
                game_init: Default::default(),
                game_coord_conversion: Default::default(),
                fow_sprites: Default::default(),
                init_map_from_path: Default::default(),
                single_player_start: Default::default(),
                select_map_entry: Default::default(),
                images_loaded: Default::default(),
                step_network: Default::default(),
                snp_definitions: Default::default(),
                init_storm_networking: Default::default(),
                misc_clientside: Default::default(),
                unit_creation: Default::default(),
                init_sprites: Default::default(),
                sprite_serialization: Default::default(),
                limits: Default::default(),
                font_render: Default::default(),
                create_game_dialog_vtbl_on_multiplayer_create: Default::default(),
                tooltip_related: Default::default(),
                prism_shaders: Default::default(),
                ai_step_frame_funcs: Default::default(),
                dat_patches: Default::default(),
                do_attack: Default::default(),
                button_ddsgrps: Default::default(),
                mouse_xy: Default::default(),
                check_unit_requirements: Default::default(),
                multi_wireframes: Default::default(),
                run_triggers: Default::default(),
                trigger_unit_count_caches: Default::default(),
                snet_handle_packets: Default::default(),
                replay_minimap_unexplored_fog_patch: Default::default(),
                crt_fastfail: Default::default(),
                dat_tables: DatTables::new(),
            },
            shareable: AnalysisCtx {
                binary,
                binary_sections: BinarySections {
                    rdata: binary.section(b".rdata\0\0").unwrap(),
                    data: binary.section(b".data\0\0\0").unwrap(),
                    text,
                },
                ctx,
                bump: Bump::new(),
                arg_cache: ArgCache::new(ctx),
            },
        }
    }

    fn is_valid_function(address: E::VirtualAddress) -> bool {
        address.as_u64() & 0xf == 0
    }

    /// Entry point for any analysis calls.
    /// Creates AnalysisCtx from self that is used across actual analysis functions.
    fn enter<F: for<'b> FnOnce(&mut AnalysisCache<'e, E>, &AnalysisCtx<'e, E>) -> R, R>(
        &mut self,
        func: F,
    ) -> R {
        let ret = func(&mut self.cache, &self.shareable);
        self.shareable.bump.reset();
        ret
    }

    pub fn firegraft_addresses(&mut self) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        self.enter(|x, s| x.firegraft_addresses(s))
    }

    pub fn dat(&mut self, ty: DatType) -> Option<DatTablePtr<'e>> {
        self.enter(|x, s| x.dat(ty, s))
    }

    pub fn file_hook(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.file_hook(s))
    }

    pub fn rng(&mut self) -> Rc<Rng<'e>> {
        self.enter(|x, s| x.rng(s))
    }

    pub fn step_objects(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_objects(s))
    }

    pub fn game(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.game(s))
    }

    pub fn aiscript_hook(&mut self) -> Rc<Option<AiScriptHook<'e, E::VirtualAddress>>> {
        self.enter(|x, s| x.aiscript_hook(s))
    }

    pub fn regions(&mut self) -> Rc<RegionRelated<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.regions(s))
    }

    pub fn pathing(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.pathing(s))
    }

    pub fn active_hidden_units(&mut self) -> Rc<ActiveHiddenUnits<'e>> {
        self.enter(|x, s| x.active_hidden_units(s))
    }

    pub fn order_issuing(&mut self) -> Rc<OrderIssuing<E::VirtualAddress>> {
        self.enter(|x, s| x.order_issuing(s))
    }

    pub fn process_commands(&mut self) -> Rc<ProcessCommands<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.process_commands(s))
    }

    pub fn command_user(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.command_user(s))
    }

    /// May return an overly long array
    pub fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        self.enter(|x, s| x.command_lengths(s))
    }

    pub fn selections(&mut self) -> Rc<Selections<'e>> {
        self.enter(|x, s| x.selections(s))
    }

    pub fn is_replay(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.is_replay(s))
    }

    pub fn process_lobby_commands(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.process_lobby_commands(s))
    }

    pub fn send_command(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.send_command(s))
    }

    pub fn print_text(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.print_text(s))
    }

    pub fn init_map_from_path(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_map_from_path(s))
    }

    pub fn choose_snp(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.choose_snp(s))
    }

    pub fn renderer_vtables(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.renderer_vtables(s))
    }

    pub fn vtables(&mut self) -> Vec<E::VirtualAddress> {
        self.enter(|x, s| x.vtables(s))
    }

    pub fn vtables_for_class(&mut self, name: &[u8]) -> Vec<E::VirtualAddress> {
        self.enter(|x, s| x.vtables_for_class(name, s))
    }

    pub fn single_player_start(&mut self) -> Rc<SinglePlayerStart<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.single_player_start(s))
    }

    pub fn local_player_id(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.local_player_id(s))
    }

    pub fn game_screen_rclick(&mut self) -> Rc<GameScreenRClick<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.game_screen_rclick(s))
    }

    pub fn select_map_entry(&mut self) -> Rc<SelectMapEntry<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.select_map_entry(s))
    }

    pub fn load_images(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.load_images(s))
    }

    pub fn images_loaded(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.images_loaded(s))
    }

    pub fn init_real_time_lighting(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_real_time_lighting(s))
    }

    pub fn local_player_name(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.local_player_name(s))
    }

    pub fn step_network(&mut self) -> Rc<StepNetwork<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.step_network(s))
    }

    pub fn init_game_network(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_game_network(s))
    }

    pub fn snp_definitions(&mut self) -> Option<SnpDefinitions<'e>> {
        self.enter(|x, s| x.snp_definitions(s))
    }

    pub fn lobby_state(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.lobby_state(s))
    }

    pub fn init_storm_networking(&mut self) -> Rc<InitStormNetworking<E::VirtualAddress>> {
        self.enter(|x, s| x.init_storm_networking(s))
    }

    pub fn step_order(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_order(s))
    }

    pub fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x, s| x.step_order_hidden(s))
    }

    pub fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x, s| x.step_secondary_order(s))
    }

    pub fn step_iscript(&mut self) -> Rc<StepIscript<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.step_iscript(s))
    }

    pub fn add_overlay_iscript(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.add_overlay_iscript(s))
    }

    pub fn draw_cursor_marker(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.draw_cursor_marker(s))
    }

    pub fn play_smk(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.play_smk(s))
    }

    pub fn game_init(&mut self) -> Rc<GameInit<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.game_init(s))
    }

    pub fn misc_clientside(&mut self) -> Rc<MiscClientSide<'e>> {
        self.enter(|x, s| x.misc_clientside(s))
    }

    pub fn init_units(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_units_related(s).init_units)
    }

    pub fn load_dat(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.load_dat(s))
    }

    pub fn units(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.units(s))
    }

    pub fn first_ai_script(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.first_ai_script(s))
    }

    pub fn first_guard_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.first_guard_ai(s))
    }

    pub fn player_ai_towns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_ai_towns(s))
    }

    pub fn player_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_ai(s))
    }

    pub fn init_game(&mut self) -> Rc<InitGame<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.init_game(s))
    }

    pub fn sprites(&mut self) -> Rc<Sprites<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.sprites(s))
    }

    pub fn eud_table(&mut self) -> Rc<EudTable<'e>> {
        self.enter(|x, s| x.eud_table(s))
    }

    pub fn map_tile_flags(&mut self) -> Rc<MapTileFlags<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.map_tile_flags(s))
    }

    pub fn players(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.players(s))
    }

    pub fn draw_image(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_image(s))
    }

    pub fn bullet_creation(&mut self) -> Rc<BulletCreation<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.bullet_creation(s))
    }

    pub fn net_players(&mut self) -> Rc<NetPlayers<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.net_players(s))
    }

    pub fn campaigns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.campaigns(s))
    }

    pub fn run_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.run_dialog(s))
    }

    pub fn ai_update_attack_target(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_update_attack_target(s))
    }

    pub fn is_outside_game_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.is_outside_game_screen(s))
    }

    pub fn game_coord_conversion(&mut self) -> Rc<GameCoordConversion<'e>> {
        self.enter(|x, s| x.game_coord_conversion(s))
    }

    pub fn fow_sprites(&mut self) -> Rc<FowSprites<'e>> {
        self.enter(|x, s| x.fow_sprites(s))
    }

    pub fn spawn_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.spawn_dialog(s))
    }

    pub fn unit_creation(&mut self) -> Rc<UnitCreation<E::VirtualAddress>> {
        self.enter(|x, s| x.unit_creation(s))
    }

    pub fn fonts(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.fonts(s))
    }

    pub fn init_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_sprites(s))
    }

    pub fn sprite_array(&mut self) -> Option<(Operand<'e>, u32)> {
        self.enter(|x, s| x.sprite_array(s))
    }

    pub fn serialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.serialize_sprites(s))
    }

    pub fn deserialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.deserialize_sprites(s))
    }

    pub fn limits(&mut self) -> Rc<Limits<'e, E::VirtualAddress>> {
        self.enter(|x, s| x.limits(s))
    }

    pub fn font_cache_render_ascii(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.font_cache_render_ascii(s))
    }

    pub fn ttf_cache_character(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ttf_cache_character(s))
    }

    pub fn ttf_render_sdf(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ttf_render_sdf(s))
    }

    /// Memory allocation function that at least TTF code uses.
    ///
    /// (Should be Win32 HeapAlloc with a specific heap)
    pub fn ttf_malloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ttf_malloc(s))
    }

    /// Offset to CreateGameScreen.OnMultiplayerGameCreate in the dialog's vtable
    pub fn create_game_dialog_vtbl_on_multiplayer_create(&mut self) -> Option<usize> {
        self.enter(|x, s| x.create_game_dialog_vtbl_on_multiplayer_create(s))
    }

    pub fn tooltip_draw_func(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.tooltip_draw_func(s))
    }

    pub fn current_tooltip_ctrl(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.current_tooltip_ctrl(s))
    }

    pub fn layout_draw_text(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.layout_draw_text(s))
    }

    pub fn graphic_layers(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.graphic_layers(s))
    }

    pub fn draw_f10_menu_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_f10_menu_tooltip(s))
    }

    pub fn draw_tooltip_layer(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_tooltip_layer(s))
    }

    pub fn draw_graphic_layers(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.draw_graphic_layers(s))
    }

    pub fn prism_vertex_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.prism_vertex_shaders(s))
    }

    pub fn prism_pixel_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.prism_pixel_shaders(s))
    }

    pub fn ai_attack_prepare(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_attack_prepare(s))
    }

    pub fn ai_step_region(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_step_region(s))
    }

    pub fn ai_spend_money(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_spend_money(s))
    }

    pub fn join_game(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.join_game(s))
    }

    pub fn snet_initialize_provider(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.snet_initialize_provider(s))
    }

    pub fn set_status_screen_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.set_status_screen_tooltip(s))
    }

    pub fn dat_patches(&mut self) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        self.enter(|x, s| x.dat_patches(s))
    }

    pub fn do_attack(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.do_attack(s))
    }

    pub fn do_attack_main(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.do_attack_main(s))
    }

    pub fn last_bullet_spawner(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.last_bullet_spawner(s))
    }

    pub fn smem_alloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.smem_alloc(s))
    }

    pub fn smem_free(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.smem_free(s))
    }

    pub fn cmdicons_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.cmdicons_ddsgrp(s))
    }

    pub fn cmdbtns_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.cmdbtns_ddsgrp(s))
    }

    pub fn mouse_xy(&mut self) -> MouseXy<'e, E::VirtualAddress> {
        self.enter(|x, s| x.mouse_xy(s))
    }

    pub fn status_screen_mode(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.status_screen_mode(s))
    }

    pub fn check_unit_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.check_unit_requirements(s))
    }

    pub fn check_dat_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.check_dat_requirements(s))
    }

    pub fn dat_requirement_error(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.dat_requirement_error(s))
    }

    pub fn cheat_flags(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.cheat_flags(s))
    }

    pub fn unit_strength(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.unit_strength(s))
    }

    pub fn grpwire_grp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.grpwire_grp(s))
    }

    pub fn grpwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.grpwire_ddsgrp(s))
    }

    pub fn tranwire_grp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.tranwire_grp(s))
    }

    pub fn tranwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.tranwire_ddsgrp(s))
    }

    pub fn status_screen(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.status_screen(s))
    }

    pub fn status_screen_event_handler(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.status_screen_event_handler(s))
    }

    /// Note: Struct that contains { grp, sd_ddsgrp, hd_ddsgrp }
    pub fn wirefram_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.wirefram_ddsgrp(s))
    }

    pub fn init_status_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.init_status_screen(s))
    }

    pub fn trigger_conditions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.trigger_conditions(s))
    }

    pub fn trigger_actions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.trigger_actions(s))
    }

    pub fn trigger_completed_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.trigger_completed_units_cache(s))
    }

    pub fn trigger_all_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.trigger_all_units_cache(s))
    }

    pub fn snet_send_packets(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.snet_send_packets(s))
    }

    pub fn snet_recv_packets(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.snet_recv_packets(s))
    }

    pub fn chk_init_players(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.chk_init_players(s))
    }

    pub fn original_chk_player_types(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.original_chk_player_types(s))
    }

    pub fn give_ai(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.give_ai(s))
    }

    pub fn play_sound(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.play_sound(s))
    }

    pub fn ai_prepare_moving_to(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_prepare_moving_to(s))
    }

    pub fn ai_transport_reachability_cached_region(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.ai_transport_reachability_cached_region(s))
    }

    pub fn player_unit_skins(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.player_unit_skins(s))
    }

    /// A patch to show resource fog sprites on minimap in replays even if they're
    /// in unexplored fog.
    pub fn replay_minimap_unexplored_fog_patch(
        &mut self,
    ) -> Option<Rc<Patch<E::VirtualAddress>>> {
        self.enter(|x, s| x.replay_minimap_unexplored_fog_patch(s))
    }

    pub fn step_replay_commands(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.step_replay_commands(s))
    }

    pub fn replay_data(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.replay_data(s))
    }

    pub fn ai_train_military(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_train_military(s))
    }

    pub fn ai_add_military_to_region(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x, s| x.ai_add_military_to_region(s))
    }

    /// Renderer's vertex (and index) buffer
    pub fn vertex_buffer(&mut self) -> Option<Operand<'e>> {
        self.enter(|x, s| x.vertex_buffer(s))
    }

    pub fn crt_fastfail(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x, s| x.crt_fastfail(s))
    }

    /// Mainly for tests/dump
    pub fn dat_patches_debug_data(
        &mut self,
    ) -> Option<DatPatchesDebug<'e, E::VirtualAddress>> {
        let patches = self.dat_patches()?;
        let mut map = fxhash::FxHashMap::default();
        let mut replaces = Vec::new();
        let mut func_replaces = Vec::new();
        let mut hooks = Vec::new();
        let mut two_step_hooks = Vec::new();
        let mut ext_array_patches = Vec::new();
        let mut ext_array_args = Vec::new();
        let mut grp_index_hooks = Vec::new();
        let mut grp_texture_hooks = Vec::new();
        for patch in &patches.patches {
            match *patch {
                DatPatch::Array(ref a) => {
                    let vec = &mut map.entry(a.dat)
                        .or_insert_with(DatTablePatchesDebug::default)
                        .array_patches;
                    while vec.len() <= a.field_id as usize {
                        vec.push(Vec::new());
                    }
                    vec[a.field_id as usize].push((a.address, a.entry, a.byte_offset));
                    vec[a.field_id as usize].sort_unstable();
                }
                DatPatch::EntryCount(ref a) => {
                    let entry_counts = &mut map.entry(a.dat)
                        .or_insert_with(DatTablePatchesDebug::default)
                        .entry_counts;
                    entry_counts.push(a.address);
                    entry_counts.sort_unstable();
                }
                DatPatch::Replace(addr, offset, len) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    replaces.push((addr, data.into()));
                }
                DatPatch::Hook(addr, offset, len, skip) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    hooks.push((addr, skip, data.into()));
                }
                DatPatch::TwoStepHook(addr, free_space, offset, len, skip) => {
                    let data = &patches.code_bytes[offset as usize..][..len as usize];
                    two_step_hooks.push((addr, free_space, skip, data.into()));
                }
                DatPatch::ReplaceFunc(addr, ty) => {
                    func_replaces.push((addr, ty));
                }
                DatPatch::ExtendedArray(ref a) => {
                    ext_array_patches.push(
                        (a.address, a.two_step, a.instruction_len, a.ext_array_id, a.index)
                    );
                }
                DatPatch::ExtendedArrayArg(addr, args) => {
                    let args = args.iter().enumerate()
                        .filter_map(|x| Some((x.0, x.1.checked_sub(1)?)))
                        .collect();
                    ext_array_args.push((addr, args));
                }
                DatPatch::GrpIndexHook(addr) => {
                    grp_index_hooks.push(addr);
                }
                DatPatch::GrpTextureHook(ref a) => {
                    grp_texture_hooks.push(
                        (a.address, a.instruction_len, a.dest, a.base, a.index_bytes)
                    );
                }
            }
        }
        replaces.sort_unstable_by_key(|x| x.0);
        func_replaces.sort_unstable_by_key(|x| x.0);
        hooks.sort_unstable_by_key(|x| x.0);
        two_step_hooks.sort_unstable_by_key(|x| x.0);
        ext_array_patches.sort_unstable_by_key(|x| (x.3, x.0));
        ext_array_args.sort_unstable_by_key(|x| x.0);
        grp_index_hooks.sort_unstable_by_key(|x| *x);
        grp_texture_hooks.sort_unstable_by_key(|x| x.0);
        Some(DatPatchesDebug {
            tables: map,
            replaces,
            func_replaces,
            hooks,
            two_step_hooks,
            ext_array_patches,
            ext_array_args,
            grp_index_hooks,
            grp_texture_hooks,
        })
    }
}

impl<'e, E: ExecutionStateTrait<'e>> AnalysisCache<'e, E> {
    fn functions(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let binary = self.binary;
        let text = self.text;
        let relocs = self.relocs();
        self.functions.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions::<E>(binary, &relocs);
            functions.retain(|&fun| Analysis::<E>::is_valid_function(fun));

            // Add functions which immediately jump to another
            let text_end = text.virtual_address + text.virtual_size;
            let mut extra_funcs = Vec::with_capacity(64);
            for &func in &functions {
                let relative = func.as_u64().wrapping_sub(text.virtual_address.as_u64()) as usize;
                if let Some(&byte) = text.data.get(relative) {
                    if byte == 0xe9 {
                        if let Some(offset) = (&text.data[relative + 1..]).read_u32::<LE>().ok() {
                            let dest = func.as_u64()
                                .wrapping_add(5)
                                .wrapping_add(offset as i32 as i64 as u64);
                            let dest = E::VirtualAddress::from_u64(dest);
                            if dest >= text.virtual_address && dest <= text_end {
                                if let Err(index) = functions.binary_search(&dest) {
                                    extra_funcs.push((dest, index));
                                }
                            }
                        }
                    }
                }
            }
            // Insert functions without having to memmove every entry more than once
            extra_funcs.sort_unstable_by_key(|x| x.0);
            extra_funcs.dedup_by_key(|x| x.0);
            let mut end_pos = functions.len();
            functions.resize_with(
                functions.len() + extra_funcs.len(),
                || E::VirtualAddress::from_u64(0),
            );
            for (i, &(val, index)) in extra_funcs.iter().enumerate().rev() {
                functions.copy_within(index..end_pos, index + i + 1);
                functions[index + i] = val;
                end_pos = index;
            }
            Rc::new(functions)
        }).clone()
    }

    fn relocs_with_values(&mut self) -> Rc<Vec<RelocValues<E::VirtualAddress>>> {
        let result = match self.relocs_with_values.is_none() {
            true => {
                let relocs = self.relocs();
                match scarf::analysis::relocs_with_values(self.binary, &relocs) {
                    Ok(o) => o,
                    Err(e) => {
                        debug!("Error getting relocs with values: {}", e);
                        Vec::new()
                    }
                }
            }
            false => Vec::new(),
        };
        self.relocs_with_values.get_or_insert_with(|| {
            Rc::new(result)
        }).clone()
    }

    fn relocs(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let relocs = match self.relocs.is_none() {
            true => match scarf::analysis::find_relocs::<E>(self.binary) {
                Ok(s) => s,
                Err(e) => {
                    debug!("Error getting relocs: {}", e);
                    Vec::new()
                }
            },
            false => Vec::new(),
        };
        self.relocs.get_or_insert_with(|| {
            Rc::new(relocs)
        }).clone()
    }

    // TODO Should share search w/ self.functions
    fn functions_with_callers(&mut self) -> Rc<Vec<FuncCallPair<E::VirtualAddress>>> {
        let binary = self.binary;
        self.functions_with_callers.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions_with_callers::<E>(binary);
            functions.retain(|fun| Analysis::<E>::is_valid_function(fun.callee));
            Rc::new(functions)
        }).clone()
    }

    fn function_finder<'s>(&'s mut self) -> FunctionFinder<'s, 'e, E> {
        if self.functions.is_none() {
            self.functions();
        }
        if self.relocs_with_values.is_none() {
            self.relocs_with_values();
        }
        if self.functions_with_callers.is_none() {
            self.functions_with_callers();
        }
        let functions = self.functions.0.as_deref().unwrap();
        let relocs_with_values = self.relocs_with_values.0.as_deref().unwrap();
        let functions_with_callers = self.functions_with_callers.0.as_deref().unwrap();
        FunctionFinder {
            functions,
            relocs_with_values,
            functions_with_callers,
        }
    }

    fn cache_single_address<F>(
        &mut self,
        addr: AddressAnalysis,
        cb: F,
    ) -> Option<E::VirtualAddress>
    where F: FnOnce(&mut Self) -> Option<E::VirtualAddress>
    {
        let result = self.address_results[addr as usize];
        if result != E::VirtualAddress::from_u64(0) {
            if result == E::VirtualAddress::from_u64(1) {
                return None;
            } else {
                return Some(result);
            }
        }
        self.address_results[addr as usize] = E::VirtualAddress::from_u64(1);
        let result = cb(self);
        if let Some(result) = result {
            self.address_results[addr as usize] = result;
        }
        result
    }

    fn cache_single_operand<F>(&mut self, op: OperandAnalysis, cb: F) -> Option<Operand<'e>>
    where F: FnOnce(&mut Self) -> Option<Operand<'e>>
    {
        if let Some(result) = self.operand_results[op as usize] {
            if result == self.operand_not_found {
                return None;
            } else {
                return Some(result);
            }
        }
        self.operand_results[op as usize] = Some(self.operand_not_found);
        let result = cb(self);
        if result.is_some() {
            self.operand_results[op as usize] = result;
        }
        result
    }

    fn firegraft_addresses(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        if let Some(cached) = self.firegraft_addresses.cached() {
            return cached;
        }
        let functions = &self.function_finder();
        let relocs = functions.relocs_with_values();
        let buttonsets = firegraft::find_buttonsets(actx);
        let status_funcs = firegraft::find_unit_status_funcs(actx, &functions);
        let reqs = firegraft::find_requirement_tables(actx, relocs);
        let result = Rc::new(FiregraftAddresses {
            buttonsets,
            requirement_table_refs: reqs,
            unit_status_funcs: status_funcs,
        });
        self.firegraft_addresses.cache(&result);
        result
    }

    // Sorted by switch address
    fn switch_tables(&mut self) -> Rc<Vec<SwitchTable<E::VirtualAddress>>> {
        let binary = self.binary;
        let text = self.text;
        let relocs = self.relocs();
        self.switch_tables.get_or_insert_with(|| {
            let switches = scarf::analysis::find_switch_tables(binary, &relocs);
            let mut table_start_index = 0;
            let mut previous_address = E::VirtualAddress::from_u64(!0);
            let mut result = Vec::new();
            for i in 0..switches.len() {
                let jump = &switches[i];
                if jump.address != previous_address + 4 {
                    if i - table_start_index > 2 {
                        let cases =
                            switches[table_start_index..i].iter().map(|x| x.callee).collect();
                        result.push(SwitchTable {
                            address: switches[table_start_index].address,
                            cases,
                        });
                    }
                    table_start_index = i;
                }
                previous_address = jump.address;
            }

            result.retain(|s| {
                // There's microsoft directx libraries embedded with large switches for
                // displaying error etc names, luckily their compiler produces optimized ones
                // which are just
                //  mov eax, text
                //  jmp ret
                // Why they couldn't just use a string array is beyond me :l
                // There are some BW ones that this catches as well, but they aren't relevant
                // at least atm. Hopefully I'll remember this filter if things change.
                !s.cases.iter().take(6).all(|&case| {
                    let case_relative = (case.as_u64() - text.virtual_address.as_u64()) as usize;
                    text.data.get(case_relative..).and_then(|case_ins| {
                        let first = *case_ins.get(0)?;
                        let second = *case_ins.get(5)?;
                        Some(first == 0xb8 && (second == 0xe9 || second == 0xeb))
                    }).unwrap_or(false)
                })
            });
            result.sort_unstable_by_key(|x| x.address);
            Rc::new(result)
        }).clone()
    }

    /// Returns address and dat table struct size
    fn dat_virtual_address(
        &mut self,
        ty: DatType,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<(E::VirtualAddress, u32)> {
        let dat = self.dat(ty, actx);
        let result = dat.iter()
            .filter_map(|x| x.address.if_constant().map(|y| (y, x.entry_size)))
            .next()
            .map(|(addr, size)| (E::VirtualAddress::from_u64(addr), size));
        result
    }

    fn dat(&mut self, ty: DatType, actx: &AnalysisCtx<'e, E>) -> Option<DatTablePtr<'e>> {
        let filename = {
            let (field, filename) = self.dat_tables.field(ty);
            if let Some(ref f) = *field {
                return f.clone();
            }
            filename
        };
        let result = dat::dat_table(actx, filename, &self.function_finder());
        let (field, _) = self.dat_tables.field(ty);
        *field = Some(result.clone());
        result
    }

    fn file_hook(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.open_file.cached() {
            return cached;
        }
        let result = Rc::new(file::open_file(actx, &self.function_finder()));
        self.open_file.cache(&result);
        result
    }

    fn rng(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Rng<'e>> {
        if let Some(cached) = self.rng.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let units_dat = self.dat_virtual_address(DatType::Units, actx)?;
            Some(rng::rng(actx, units_dat, &self.function_finder()))
        }).unwrap_or_else(|| Rng {
            seed: None,
            enable: None,
        });
        let result = Rc::new(result);
        self.rng.cache(&result);
        result
    }

    fn step_objects(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepObjects, |s| {
            game::step_objects(actx, s.rng(actx).enable?, &s.function_finder())
        })
    }

    fn game(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Game, |s| {
            game::game(actx, s.step_objects(actx)?)
        })
    }

    fn aiscript_hook(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<Option<AiScriptHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.aiscript_hook.cached() {
            return cached;
        }
        let result = Rc::new(ai::aiscript_hook(self, actx));
        self.aiscript_hook.cache(&result);
        result
    }

    fn regions(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<RegionRelated<'e, E::VirtualAddress>> {
        if let Some(cached) = self.regions.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let aiscript_hook = self.aiscript_hook(actx);
            let aiscript_hook = aiscript_hook.as_ref().as_ref()?;
            Some(pathing::regions(actx, aiscript_hook))
        }).unwrap_or_else(|| {
            RegionRelated {
                get_region: None,
                ai_regions: None,
                change_ai_region_state: None,
            }
        });
        let result = Rc::new(result);
        self.regions.cache(&result);
        result
    }

    fn pathing(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Pathing, |s| {
            pathing::pathing(actx, s.regions(actx).get_region?)
        })
    }

    fn active_hidden_units(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<ActiveHiddenUnits<'e>> {
        if let Some(cached) = self.active_hidden_units.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let orders_dat = self.dat_virtual_address(DatType::Orders, actx)?;
            let functions = self.function_finder();
            Some(units::active_hidden_units(actx, orders_dat, &functions))
        }).unwrap_or_else(|| {
            ActiveHiddenUnits {
                first_active_unit: None,
                first_hidden_unit: None,
            }
        });
        let result = Rc::new(result);
        self.active_hidden_units.cache(&result);
        result
    }

    fn order_issuing(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<OrderIssuing<E::VirtualAddress>> {
        if let Some(cached) = self.order_issuing.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let units_dat = self.dat_virtual_address(DatType::Units, actx)?;
            let functions = self.function_finder();
            Some(units::order_issuing(actx, units_dat, &functions))
        }).unwrap_or_else(|| {
            OrderIssuing {
                order_init_arbiter: None,
                prepare_issue_order: None,
                do_next_queued_order: None,
            }
        });
        let result = Rc::new(result);
        self.order_issuing.cache(&result);
        result
    }

    fn process_commands(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<ProcessCommands<'e, E::VirtualAddress>> {
        if let Some(cached) = self.process_commands.cached() {
            return cached;
        }
        let switches = self.switch_tables();
        let result = commands::process_commands(actx, &switches, &self.function_finder());
        let result = Rc::new(result);
        self.process_commands.cache(&result);
        result
    }

    fn command_user(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::CommandUser, |s| {
            commands::command_user(actx, s.game(actx)?, &s.process_commands(actx))
        })
    }

    fn command_lengths(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<u32>> {
        if let Some(cached) = self.command_lengths.cached() {
            return cached;
        }

        let result = commands::command_lengths(actx);
        let result = Rc::new(result);
        self.command_lengths.cache(&result);
        result
    }

    fn selections(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Selections<'e>> {
        if let Some(cached) = self.selections.cached() {
            return cached;
        }

        let result = commands::selections(actx, &self.process_commands(actx));
        let result = Rc::new(result);
        self.selections.cache(&result);
        result
    }

    fn is_replay(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::IsReplay, |s| {
            commands::is_replay(actx, &s.process_commands(actx))
        })
    }

    fn process_lobby_commands_switch(&mut self, actx: &AnalysisCtx<'e, E>) ->
        Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)>
    {
        if let Some(cached) = self.process_lobby_commands.cached() {
            return cached;
        }
        let mut result = None;
        let switch_tables = self.switch_tables();
        let switches = switch_tables.iter().filter(|switch| {
            switch.cases.len() >= 0x10 && switch.cases.len() < 0x20
        });
        let funcs = self.function_finder();
        for switch in switches {
            let val = full_switch_info(actx, &funcs, switch)
                .and_then(|(switch, entry)| {
                    let ok = switch.cases.windows(0x34).enumerate().any(|(_, win)| {
                        let first = win[0];
                        let default = win[1];
                        let last = win[0x33];
                        first != last && last != default && first != default &&
                            (&win[2..0x33]).iter().all(|&x| x == default)
                    });
                    if ok {
                        Some((switch, entry))
                    } else {
                        None
                    }
                });
            if single_result_assign(val, &mut result) {
                break;
            }
        }
        self.process_lobby_commands.cache(&result);
        result
    }

    fn process_lobby_commands(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.process_lobby_commands_switch(actx).map(|x| x.1)
    }

    fn send_command(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SendCommand, |s| {
            commands::send_command(actx, &s.firegraft_addresses(actx))
        })
    }

    fn print_text(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::PrintText, |s| {
            commands::print_text(actx, &s.process_commands(actx))
        })
    }

    fn init_map_from_path_vars(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<InitMapFromPath<E::VirtualAddress>> {
        if let Some(cached) = self.init_map_from_path.cached() {
            return cached;
        }
        let result = game_init::init_map_from_path(actx, &self.function_finder());
        self.init_map_from_path.cache(&result);
        result
    }

    fn init_map_from_path(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.init_map_from_path_vars(actx).map(|x| x.init_map_from_path)
    }

    fn choose_snp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::ChooseSnp, |s| {
            game_init::choose_snp(actx, &s.function_finder())
        })
    }

    fn renderer_vtables(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.renderer_vtables.cached() {
            return cached;
        }
        let result = Rc::new(renderer::renderer_vtables(actx, &self.function_finder()));
        self.renderer_vtables.cache(&result);
        result
    }

    fn vtables(&mut self, actx: &AnalysisCtx<'e, E>) -> Vec<E::VirtualAddress> {
        self.vtables_for_class(b".?AV", actx)
    }

    fn vtables_for_class(
        &mut self,
        name: &[u8],
        actx: &AnalysisCtx<'e, E>,
    ) -> Vec<E::VirtualAddress> {
        let mut vtables = vtables::vtables(actx, &self.function_finder(), name);
        vtables.sort_unstable();
        vtables.dedup();
        vtables
    }

    fn single_player_start(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<SinglePlayerStart<'e, E::VirtualAddress>> {
        if let Some(cached) = self.single_player_start.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let choose_snp = self.choose_snp(actx)?;
            let local_player_id = self.local_player_id(actx)?;
            let functions = self.function_finder();
            Some(game_init::single_player_start(actx, &functions, choose_snp, local_player_id))
        }).unwrap_or_else(|| SinglePlayerStart::default());
        let result = Rc::new(result);
        self.single_player_start.cache(&result);
        result
    }

    fn local_player_id(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LocalPlayerId, |s| {
            players::local_player_id(actx, s.game_screen_rclick(actx).game_screen_rclick?)
        })
    }

    fn game_screen_rclick(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<GameScreenRClick<'e, E::VirtualAddress>> {
        if let Some(cached) = self.game_screen_rclick.cached() {
            return cached;
        }

        let result = Some(()).and_then(|()| {
            let units_dat = self.dat_virtual_address(DatType::Units, actx)?;
            let functions = self.function_finder();
            Some(clientside::game_screen_rclick(actx, units_dat, &functions))
        }).unwrap_or_else(|| {
            GameScreenRClick {
                game_screen_rclick: None,
                client_selection: None,
            }
        });
        let result = Rc::new(result);
        self.game_screen_rclick.cache(&result);
        result
    }

    fn select_map_entry(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<SelectMapEntry<'e, E::VirtualAddress>> {
        if let Some(cached) = self.select_map_entry.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let single_player_start = self.single_player_start(actx).single_player_start?;
            let functions = self.function_finder();
            Some(game_init::select_map_entry(actx, single_player_start, &functions))
        }).unwrap_or_else(|| SelectMapEntry::default());
        let result = Rc::new(result);
        self.select_map_entry.cache(&result);
        result
    }

    fn load_images(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::LoadImages, |s| {
            game_init::load_images(actx, &s.function_finder())
        })
    }

    fn images_loaded_struct(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> ImagesLoaded<'e, E::VirtualAddress> {
        if let Some(cached) = self.images_loaded.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(game_init::images_loaded(actx, self.load_images(actx)?, &self.function_finder()))
        }).unwrap_or_else(|| {
            ImagesLoaded {
                images_loaded: None,
                init_real_time_lighting: None,
            }
        });
        self.images_loaded.cache(&result);
        result
    }

    fn images_loaded(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.images_loaded_struct(actx).images_loaded
    }

    fn init_real_time_lighting(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.images_loaded_struct(actx).init_real_time_lighting
    }

    fn local_player_name(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LocalPlayerName, |s| {
            let relocs = s.relocs();
            game_init::local_player_name(actx, &relocs, &s.function_finder())
        })
    }

    fn step_network(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<StepNetwork<'e, E::VirtualAddress>> {
        if let Some(cached) = self.step_network.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let process_lobby_commands = self.process_lobby_commands(actx)?;
            Some(commands::step_network(actx, process_lobby_commands, &self.function_finder()))
        }).unwrap_or_else(|| {
            StepNetwork {
                step_network: None,
                receive_storm_turns: None,
                menu_screen_id: None,
                net_player_flags: None,
                player_turns: None,
                player_turns_size: None,
                network_ready: None,
            }
        });
        let result = Rc::new(result);
        self.step_network.cache(&result);
        result
    }

    fn init_game_network(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::InitGameNetwork, |s| {
            let local_storm_player_id = s.single_player_start(actx).local_storm_player_id?;
            let functions = s.function_finder();
            game_init::init_game_network(actx, local_storm_player_id, &functions)
        })
    }

    fn snp_definitions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<SnpDefinitions<'e>> {
        if let Some(cached) = self.snp_definitions.cached() {
            return cached;
        }
        let result = network::snp_definitions(actx);
        self.snp_definitions.cache(&result);
        result
    }

    fn lobby_state(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::LobbyState, |s| {
            let (switch, _) = s.process_lobby_commands_switch(actx)?;
            game_init::lobby_state(actx, &switch)
        })
    }

    fn init_storm_networking(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<InitStormNetworking<E::VirtualAddress>> {
        if let Some(cached) = self.init_storm_networking.cached() {
            return cached;
        }
        let result = network::init_storm_networking(actx, &self.function_finder());
        let result = Rc::new(result);
        self.init_storm_networking.cache(&result);
        result
    }

    fn step_order(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepOrder, |s| {
            let order_init_arbiter = s.order_issuing(actx).order_init_arbiter?;
            let switches = s.switch_tables();
            let funcs = s.function_finder();
            step_order::step_order(actx, order_init_arbiter, &switches, &funcs)
        })
    }

    fn step_order_hidden(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.step_order_hidden.cached() {
            return cached;
        }
        let switches = self.switch_tables();
        let result = step_order::step_order_hidden(actx, &switches, &self.function_finder());
        let result = Rc::new(result);
        self.step_order_hidden.cache(&result);
        result
    }

    fn step_secondary_order(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.step_secondary_order.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            Some(step_order::step_secondary_order(actx, step_order, &self.function_finder()))
        }).unwrap_or_else(|| Vec::new());
        let result = Rc::new(result);
        self.step_secondary_order.cache(&result);
        result
    }

    fn step_iscript(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<StepIscript<'e, E::VirtualAddress>> {
        if let Some(cached) = self.step_iscript.cached() {
            return cached;
        }
        let switches = self.switch_tables();
        let result = iscript::step_iscript(actx, &switches, &self.function_finder());
        let result = Rc::new(result);
        self.step_iscript.cache(&result);
        result
    }

    fn add_overlay_iscript(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AddOverlayIscript, |s| {
            iscript::add_overlay_iscript(actx, s.step_iscript(actx).switch_table?)
        })
    }

    fn draw_cursor_marker(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::DrawCursorMarker, |s| {
            iscript::draw_cursor_marker(actx, s.step_iscript(actx).switch_table?)
        })
    }

    fn play_smk(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::PlaySmk, |s| {
            game_init::play_smk(actx, &s.function_finder())
        })
    }

    fn game_init(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<GameInit<'e, E::VirtualAddress>> {
        if let Some(cached) = self.game_init.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let play_smk = self.play_smk(actx)?;
            let game = self.game(actx)?;
            Some(game_init::game_init(actx, play_smk, game, &self.function_finder()))
        }).unwrap_or_else(|| {
            GameInit {
                sc_main: None,
                mainmenu_entry_hook: None,
                game_loop: None,
                scmain_state: None,
            }
        });
        let result = Rc::new(result);
        self.game_init.cache(&result);
        result
    }

    fn misc_clientside(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<MiscClientSide<'e>> {
        if let Some(cached) = self.misc_clientside.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let is_multiplayer = self.select_map_entry(actx).is_multiplayer?;
            let scmain_state = self.game_init(actx).scmain_state?;
            let funcs = self.function_finder();
            Some(clientside::misc_clientside(actx, is_multiplayer, scmain_state, &funcs))
        }).unwrap_or_else(|| {
            MiscClientSide {
                is_paused: None,
                is_placing_building: None,
                is_targeting: None,
            }
        });
        let result = Rc::new(result);
        self.misc_clientside.cache(&result);
        result
    }

    fn init_units_related(&mut self, actx: &AnalysisCtx<'e, E>) -> InitUnits<E::VirtualAddress> {
        if let Some(cached) = self.init_units.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let units_dat = self.dat_virtual_address(DatType::Units, actx)?;
            let orders_dat = self.dat_virtual_address(DatType::Orders, actx)?;
            let funcs = self.function_finder();
            Some(units::init_units(actx, units_dat, orders_dat, &funcs))
        }).unwrap_or_else(|| {
            InitUnits {
                init_units: None,
                load_dat: None,
            }
        });
        self.init_units.cache(&result);
        result
    }

    fn init_units(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.init_units_related(actx).init_units
    }

    fn load_dat(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.init_units_related(actx).load_dat
    }

    fn units(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Units, |s| {
            units::units(actx, s.init_units(actx)?)
        })
    }

    fn first_ai_script(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::FirstAiScript, |s| {
            let aiscript = s.aiscript_hook(actx);
            let aiscript = aiscript.as_ref().as_ref()?;
            ai::first_ai_script(actx, aiscript, &s.function_finder())
        })
    }

    fn first_guard_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::FirstGuardAi, |s| {
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            ai::first_guard_ai(actx, units_dat, &s.function_finder())
        })
    }

    fn player_ai_towns(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerAiTowns, |s| {
            ai::player_ai_towns(actx, s.aiscript_hook(actx).as_ref().as_ref()?)
        })
    }

    fn player_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerAi, |s| {
            ai::player_ai(actx, s.aiscript_hook(actx).as_ref().as_ref()?)
        })
    }

    fn init_game(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<InitGame<'e, E::VirtualAddress>> {
        if let Some(cached) = self.init_game.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(game_init::init_game(actx, self.init_units(actx)?, &self.function_finder()))
        }).unwrap_or_else(|| {
            InitGame {
                loaded_save: None,
                init_game: None,
            }
        });
        let result = Rc::new(result);
        self.init_game.cache(&result);
        result
    }

    fn sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Sprites<'e, E::VirtualAddress>> {
        if let Some(cached) = self.sprites.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            let order_nuke_track = step_order::find_order_nuke_track(actx, step_order)?;
            Some(sprites::sprites(actx, order_nuke_track))
        }).unwrap_or_else(|| {
            Sprites {
                sprite_hlines: None,
                sprite_hlines_end: None,
                first_free_sprite: None,
                last_free_sprite: None,
                first_lone: None,
                last_lone: None,
                first_free_lone: None,
                last_free_lone: None,
                sprite_x_position: None,
                sprite_y_position: None,
                create_lone_sprite: None,
            }
        });
        let result = Rc::new(result);
        self.sprites.cache(&result);
        result
    }

    fn eud_table(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<EudTable<'e>> {
        if let Some(cached) = self.eud.cached() {
            return cached;
        }
        let result = eud::eud_table(actx, &self.function_finder());
        let result = Rc::new(result);
        self.eud.cache(&result);
        result
    }

    fn map_tile_flags(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<MapTileFlags<'e, E::VirtualAddress>> {
        if let Some(cached) = self.map_tile_flags.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            let order_nuke_track = step_order::find_order_nuke_track(actx, step_order)?;
            Some(map::map_tile_flags(actx, order_nuke_track))
        }).unwrap_or_else(|| {
            MapTileFlags {
                map_tile_flags: None,
                update_visibility_point: None,
            }
        });
        let result = Rc::new(result);
        self.map_tile_flags.cache(&result);
        result
    }

    fn players(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Players, |s| {
            players::players(actx, s.aiscript_hook(actx).as_ref().as_ref()?)
        })
    }

    fn draw_image(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::DrawImage, |s| {
            let switches = s.switch_tables();
            renderer::draw_image(actx, &switches, &s.function_finder())
        })
    }

    fn bullet_creation(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<BulletCreation<'e, E::VirtualAddress>> {
        if let Some(cached) = self.bullet_creation.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(bullets::bullet_creation(actx, self.step_iscript(actx).switch_table?))
        }).unwrap_or_else(|| {
            BulletCreation {
                first_active_bullet: None,
                last_active_bullet: None,
                first_free_bullet: None,
                last_free_bullet: None,
                create_bullet: None,
                active_iscript_unit: None,
            }
        });
        let result = Rc::new(result);
        self.bullet_creation.cache(&result);
        result
    }

    fn net_players(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<NetPlayers<'e, E::VirtualAddress>> {
        if let Some(cached) = self.net_players.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let (switch, _) = self.process_lobby_commands_switch(actx)?;
            Some(players::net_players(actx, &switch))
        }).unwrap_or_else(|| {
            NetPlayers {
                net_players: None,
                init_net_player: None,
            }
        });
        let result = Rc::new(result);
        self.net_players.cache(&result);
        result
    }

    fn campaigns(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Campaigns, |_| {
            campaign::campaigns(actx)
        })
    }

    fn run_dialog(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::RunDialog, |s| {
            dialog::run_dialog(actx, &s.function_finder())
        })
    }

    fn ai_update_attack_target(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiUpdateAttackTarget, |s| {
            let step_order = s.step_order(actx)?;
            let order_computer_return = step_order::find_order_function(actx, step_order, 0xa3)?;
            ai::ai_update_attack_target(actx, order_computer_return)
        })
    }

    fn is_outside_game_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::IsOutsideGameScreen, |s| {
            let game_screen_rclick = s.game_screen_rclick(actx).game_screen_rclick?;
            clientside::is_outside_game_screen(actx, game_screen_rclick)
        })
    }

    fn game_coord_conversion(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<GameCoordConversion<'e>> {
        if let Some(cached) = self.game_coord_conversion.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let game_screen_rclick = self.game_screen_rclick(actx).game_screen_rclick?;
            let is_outside_game_screen = self.is_outside_game_screen(actx)?;
            Some(clientside::game_coord_conversion(
                actx,
                game_screen_rclick,
                is_outside_game_screen
            ))
        }).unwrap_or_else(|| GameCoordConversion::default());
        let result = Rc::new(result);
        self.game_coord_conversion.cache(&result);
        result
    }

    fn fow_sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<FowSprites<'e>> {
        if let Some(cached) = self.fow_sprites.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_objects = self.step_objects(actx)?;
            Some(sprites::fow_sprites(actx, step_objects, self.sprites(actx).first_lone?))
        }).unwrap_or_else(|| FowSprites::default());
        let result = Rc::new(result);
        self.fow_sprites.cache(&result);
        result
    }

    fn spawn_dialog(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SpawnDialog, |s| {
            dialog::spawn_dialog(actx, &s.function_finder())
        })
    }

    fn unit_creation(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Rc<UnitCreation<E::VirtualAddress>> {
        if let Some(cached) = self.unit_creation.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            let order_scan = step_order::find_order_function(actx, step_order, 0x8b)?;
            Some(units::unit_creation(actx, order_scan))
        }).unwrap_or_else(|| {
            UnitCreation {
                create_unit: None,
                finish_unit_pre: None,
                finish_unit_post: None,
            }
        });
        let result = Rc::new(result);
        self.unit_creation.cache(&result);
        result
    }

    fn fonts(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::Fonts, |s| {
            text::fonts(actx, &s.function_finder())
        })
    }

    fn init_sprites_etc(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> InitSprites<'e, E::VirtualAddress> {
        if let Some(cached) = self.init_sprites.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let sprites = self.sprites(actx);
            let first_free = sprites.first_free_sprite?;
            let last_free = sprites.last_free_sprite?;
            let functions = self.function_finder();
            Some(sprites::init_sprites(actx, first_free, last_free, &functions))
        }).unwrap_or_else(|| {
            InitSprites {
                init_sprites: None,
                sprites: None,
            }
        });
        self.init_sprites.cache(&result);
        result
    }

    fn init_sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.init_sprites_etc(actx).init_sprites
    }

    fn sprite_array(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<(Operand<'e>, u32)> {
        self.init_sprites_etc(actx).sprites
    }

    fn sprite_serialization(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> SpriteSerialization<E::VirtualAddress> {
        if let Some(cached) = self.sprite_serialization.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let sprites = self.sprites(actx);
            let hlines_end = sprites.sprite_hlines_end?;
            let sprite_array = self.sprite_array(actx)?;
            let init_sprites = self.init_sprites(actx)?;
            let game = self.game(actx)?;
            let funcs = self.function_finder();
            Some(save::sprite_serialization(
                actx,
                hlines_end,
                sprite_array,
                init_sprites,
                game,
                &funcs,
            ))
        }).unwrap_or_else(|| {
            SpriteSerialization {
                serialize_sprites: None,
                deserialize_sprites: None,
            }
        });
        self.sprite_serialization.cache(&result);
        result
    }

    fn serialize_sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.sprite_serialization(actx).serialize_sprites
    }

    fn deserialize_sprites(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.sprite_serialization(actx).deserialize_sprites
    }

    fn limits(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Limits<'e, E::VirtualAddress>> {
        if let Some(cached) = self.limits.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(game::limits(actx, self.game_init(actx).game_loop?))
        }).unwrap_or_else(|| {
            Limits {
                set_limits: None,
                arrays: Vec::new(),
                smem_alloc: None,
                smem_free: None,
            }
        });
        let result = Rc::new(result);
        self.limits.cache(&result);
        result
    }

    fn font_render(&mut self, actx: &AnalysisCtx<'e, E>) -> FontRender<E::VirtualAddress> {
        if let Some(cached) = self.font_render.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(text::font_render(actx, self.fonts(actx)?, &self.function_finder()))
        }).unwrap_or_else(|| {
            FontRender {
                font_cache_render_ascii: None,
                ttf_cache_character: None,
                ttf_render_sdf: None,
            }
        });
        self.font_render.cache(&result);
        result
    }

    fn font_cache_render_ascii(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.font_render(actx).font_cache_render_ascii
    }

    fn ttf_cache_character(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.font_render(actx).ttf_cache_character
    }

    fn ttf_render_sdf(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.font_render(actx).ttf_render_sdf
    }

    fn ttf_malloc(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::TtfMalloc, |s| {
            text::ttf_malloc(actx, s.ttf_render_sdf(actx)?)
        })
    }

    fn create_game_dialog_vtbl_on_multiplayer_create(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<usize> {
        if let Some(cached) = self.create_game_dialog_vtbl_on_multiplayer_create.cached() {
            return cached;
        }
        let result = self.select_map_entry(actx).select_map_entry
            .and_then(|x| game_init::create_game_dialog_vtbl_on_multiplayer_create(actx, x));
        self.create_game_dialog_vtbl_on_multiplayer_create.cache(&result);
        result
    }

    fn tooltip_related(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> TooltipRelated<'e, E::VirtualAddress> {
        if let Some(cached) = self.tooltip_related.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let spawn_dialog = self.spawn_dialog(actx)?;
            Some(dialog::tooltip_related(actx, spawn_dialog, &self.function_finder()))
        }).unwrap_or_else(|| {
            TooltipRelated {
                tooltip_draw_func: None,
                current_tooltip_ctrl: None,
                graphic_layers: None,
                layout_draw_text: None,
                draw_tooltip_layer: None,
                draw_f10_menu_tooltip: None,
            }
        });
        self.tooltip_related.cache(&result);
        result
    }

    fn tooltip_draw_func(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.tooltip_related(actx).tooltip_draw_func
    }

    fn current_tooltip_ctrl(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.tooltip_related(actx).current_tooltip_ctrl
    }

    fn layout_draw_text(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.tooltip_related(actx).layout_draw_text
    }

    fn graphic_layers(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.tooltip_related(actx).graphic_layers
    }

    fn draw_f10_menu_tooltip(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.tooltip_related(actx).draw_f10_menu_tooltip
    }

    fn draw_tooltip_layer(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.tooltip_related(actx).draw_tooltip_layer
    }

    fn draw_graphic_layers(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::DrawGraphicLayers, |s| {
            dialog::draw_graphic_layers(actx, s.graphic_layers(actx)?, &s.function_finder())
        })
    }

    fn prism_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> PrismShaders<E::VirtualAddress> {
        if let Some(cached) = self.prism_shaders.cached() {
            return cached;
        }
        let result = renderer::prism_shaders(actx, &self.renderer_vtables(actx));
        self.prism_shaders.cache(&result);
        result
    }

    fn prism_vertex_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders(actx).vertex_shaders
    }

    fn prism_pixel_shaders(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders(actx).pixel_shaders
    }

    fn ai_attack_prepare(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiAttackPrepare, |s| {
            ai::attack_prepare(actx, s.aiscript_hook(actx).as_ref().as_ref()?)
        })
    }

    fn ai_step_region(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.ai_step_frame_funcs(actx).ai_step_region
    }

    fn ai_spend_money(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.ai_step_frame_funcs(actx).ai_spend_money
    }

    fn ai_step_frame_funcs(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> &ai::AiStepFrameFuncs<E::VirtualAddress> {
        if self.ai_step_frame_funcs.cached_ref().is_some() {
            return self.ai_step_frame_funcs.cached_ref().unwrap();
        }
        let result = Some(()).and_then(|()| {
            let step_objects = self.step_objects(actx)?;
            let ai_regions = self.regions(actx).ai_regions?;
            let game = self.game(actx)?;
            Some(ai::step_frame_funcs(actx, step_objects, ai_regions, game))
        }).unwrap_or_else(|| {
            ai::AiStepFrameFuncs {
                ai_step_region: None,
                ai_spend_money: None,
            }
        });
        self.ai_step_frame_funcs.get_or_insert_with(|| result)
    }

    fn join_game(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::JoinGame, |s| {
            let local_storm_id = s.single_player_start(actx).local_storm_player_id?;
            game_init::join_game(actx, local_storm_id, &s.function_finder())
        })
    }

    fn snet_initialize_provider(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::SnetInitializeProvider, |s| {
            game_init::snet_initialize_provider(actx, s.choose_snp(actx)?)
        })
    }

    fn set_status_screen_tooltip(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.dat_patches(actx)?.set_status_screen_tooltip
    }

    fn dat_patches(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.dat_patches.cached() {
            return cached;
        }
        let result = dat::dat_patches(self, actx).map(|x| Rc::new(x));
        self.dat_patches.cache(&result);
        result
    }

    fn do_attack_struct(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<step_order::DoAttack<'e, E::VirtualAddress>> {
        if let Some(cached) = self.do_attack.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let step_order = self.step_order(actx)?;
            let attack_order = step_order::find_order_function(actx, step_order, 0xa)?;
            step_order::do_attack(actx, attack_order)
        });
        self.do_attack.cache(&result);
        result
    }

    fn do_attack(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.do_attack_struct(actx).map(|x| x.do_attack)
    }

    fn do_attack_main(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.do_attack_struct(actx).map(|x| x.do_attack_main)
    }

    fn last_bullet_spawner(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.do_attack_struct(actx).map(|x| x.last_bullet_spawner)
    }

    fn smem_alloc(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.limits(actx).smem_alloc
    }

    fn smem_free(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.limits(actx).smem_free
    }

    fn button_ddsgrps(&mut self, actx: &AnalysisCtx<'e, E>) -> dialog::ButtonDdsgrps<'e> {
        if let Some(cached) = self.button_ddsgrps.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let firegraft = self.firegraft_addresses(actx);
            let &status_arr = firegraft.unit_status_funcs.get(0)?;
            Some(dialog::button_ddsgrps(actx, status_arr))
        }).unwrap_or_else(|| {
            dialog::ButtonDdsgrps {
                cmdbtns: None,
                cmdicons: None,
            }
        });
        self.button_ddsgrps.cache(&result);
        result
    }

    fn cmdicons_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.button_ddsgrps(actx).cmdicons
    }

    fn cmdbtns_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.button_ddsgrps(actx).cmdbtns
    }

    fn mouse_xy(&mut self, actx: &AnalysisCtx<'e, E>) -> MouseXy<'e, E::VirtualAddress> {
        if let Some(cached) = self.mouse_xy.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            Some(dialog::mouse_xy(actx, self.run_dialog(actx)?))
        }).unwrap_or_else(|| {
            MouseXy {
                x_var: None,
                y_var: None,
                x_func: None,
                y_func: None,
            }
        });
        self.mouse_xy.cache(&result);
        result
    }

    fn status_screen_mode(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::StatusScreenMode, |s| {
            let firegraft = s.firegraft_addresses(actx);
            let &status_arr = firegraft.unit_status_funcs.get(0)?;
            dialog::status_screen_mode(actx, status_arr)
        })
    }

    fn check_unit_reqs_struct(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<requirements::CheckUnitRequirements<'e, E::VirtualAddress>> {
        if let Some(cached) = self.check_unit_requirements.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let units_dat = self.dat_virtual_address(DatType::Units, actx)?;
            requirements::check_unit_requirements(actx, units_dat, &self.function_finder())
        });
        self.check_unit_requirements.cache(&result);
        result
    }

    fn check_unit_requirements(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.check_unit_reqs_struct(actx).map(|x| x.check_unit_requirements)
    }

    fn check_dat_requirements(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::CheckDatRequirements, |s| {
            let techdata = s.dat_virtual_address(DatType::TechData, actx)?;
            let functions = s.function_finder();
            requirements::check_dat_requirements(actx, techdata, &functions)
        })
    }

    fn dat_requirement_error(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.check_unit_reqs_struct(actx).map(|x| x.requirement_error)
    }

    fn cheat_flags(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::CheatFlags, |s| {
            requirements::cheat_flags(actx, s.check_dat_requirements(actx)?)
        })
    }

    fn unit_strength(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::UnitStrength, |s| {
            units::strength(actx, s.init_game(actx).init_game?, s.init_units(actx)?)
        })
    }

    /// Smaller size wireframes, that is multiselection and transport
    /// (Fits multiple in status screen)
    /// Also relevant mostly for SD, HD always uses wirefram.ddsgrp for the drawing.
    fn multi_wireframes(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> MultiWireframes<'e, E::VirtualAddress> {
        if let Some(cached) = self.multi_wireframes.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let spawn_dialog = self.spawn_dialog(actx)?;
            Some(dialog::multi_wireframes(actx, spawn_dialog, &self.function_finder()))
        }).unwrap_or_else(|| MultiWireframes::default());
        self.multi_wireframes.cache(&result);
        result
    }

    fn grpwire_grp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.multi_wireframes(actx).grpwire_grp
    }

    fn grpwire_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.multi_wireframes(actx).grpwire_ddsgrp
    }

    fn tranwire_grp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.multi_wireframes(actx).tranwire_grp
    }

    fn tranwire_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.multi_wireframes(actx).tranwire_ddsgrp
    }

    fn status_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.multi_wireframes(actx).status_screen
    }

    fn status_screen_event_handler(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.multi_wireframes(actx).status_screen_event_handler
    }

    fn wirefram_ddsgrp(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::WireframDdsgrp, |s| {
            dialog::wirefram_ddsgrp(actx, s.status_screen_event_handler(actx)?)
        })
    }

    fn init_status_screen(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.multi_wireframes(actx).init_status_screen
    }

    fn run_triggers(&mut self, actx: &AnalysisCtx<'e, E>) -> RunTriggers<E::VirtualAddress> {
        if let Some(cached) = self.run_triggers.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let rng_enable = self.rng(actx).enable?;
            let step_objects = self.step_objects(actx)?;
            Some(map::run_triggers(actx, rng_enable, step_objects, &self.function_finder()))
        }).unwrap_or_else(|| RunTriggers::default());
        self.run_triggers.cache(&result);
        result
    }

    fn trigger_conditions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.run_triggers(actx).conditions
    }

    fn trigger_actions(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.run_triggers(actx).actions
    }

    fn trigger_unit_count_caches(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> TriggerUnitCountCaches<'e> {
        if let Some(cached) = self.trigger_unit_count_caches.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let conditions = self.trigger_conditions(actx)?;
            let game = self.game(actx)?;
            Some(map::trigger_unit_count_caches(actx, conditions, game))
        }).unwrap_or_else(|| Default::default());
        self.trigger_unit_count_caches.cache(&result);
        result
    }

    fn trigger_completed_units_cache(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches(actx).completed_units
    }

    fn trigger_all_units_cache(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches(actx).all_units
    }

    fn snet_handle_packets(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> SnetHandlePackets<E::VirtualAddress> {
        if let Some(cached) = self.snet_handle_packets.cached() {
            return cached;
        }
        let result = network::snet_handle_packets(actx, &self.function_finder());
        self.snet_handle_packets.cache(&result);
        result
    }

    fn snet_send_packets(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.snet_handle_packets(actx).send_packets
    }

    fn snet_recv_packets(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.snet_handle_packets(actx).recv_packets
    }

    fn chk_init_players(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::ChkInitPlayers, |s| {
            let chk_callbacks = s.init_map_from_path_vars(actx)?.map_init_chk_callbacks;
            game_init::chk_init_players(actx, chk_callbacks)
        })
    }

    fn original_chk_player_types(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::OriginalChkPlayerTypes, |s| {
            let init_players = s.chk_init_players(actx)?;
            game_init::original_chk_player_types(actx, init_players, &s.function_finder())
        })
    }

    fn give_ai(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::GiveAi, |s| {
            let actions = s.trigger_actions(actx)?;
            let units_dat = s.dat_virtual_address(DatType::Units, actx)?;
            ai::give_ai(actx, actions, units_dat)
        })
    }

    fn play_sound(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::PlaySound, |s| {
            sound::play_sound(actx, s.step_iscript(actx).switch_table?)
        })
    }

    fn ai_prepare_moving_to(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiPrepareMovingTo, |s| {
            let step_order = s.step_order(actx)?;
            let order_move = step_order::find_order_function(actx, step_order, 0x6)?;
            ai::ai_prepare_moving_to(actx, order_move)
        })
    }

    fn ai_transport_reachability_cached_region(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::AiTransportReachabilityCachedRegion, |s| {
            let prepare_moving = s.ai_prepare_moving_to(actx)?;
            ai::ai_transport_reachability_cached_region(actx, prepare_moving)
        })
    }

    fn player_unit_skins(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::PlayerUnitSkins, |s| {
            renderer::player_unit_skins(actx, s.draw_image(actx)?)
        })
    }

    fn replay_minimap_unexplored_fog_patch(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<Rc<Patch<E::VirtualAddress>>> {
        if let Some(cached) = self.replay_minimap_unexplored_fog_patch.cached() {
            return cached;
        }
        let result = Some(()).and_then(|()| {
            let first_fow_sprite = self.fow_sprites(actx).first_active?;
            let is_replay = self.is_replay(actx)?;
            let funcs = self.function_finder();
            minimap::unexplored_fog_minimap_patch(actx, first_fow_sprite, is_replay, &funcs)
        }).map(|x| Rc::new(x));
        self.replay_minimap_unexplored_fog_patch.cache(&result);
        result
    }

    fn step_replay_commands(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::StepReplayCommands, |s| {
            let process_commands = s.process_commands(actx).process_commands?;
            let game = s.game(actx)?;
            commands::step_replay_commands(actx, process_commands, game, &s.function_finder())
        })
    }

    fn replay_data(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::ReplayData, |s| {
            commands::replay_data(actx, s.process_commands(actx).switch.as_ref()?)
        })
    }

    fn ai_train_military(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiTrainMilitary, |s| {
            ai::train_military(actx, s.ai_spend_money(actx)?, s.game(actx)?)
        })
    }

    fn ai_add_military_to_region(
        &mut self,
        actx: &AnalysisCtx<'e, E>,
    ) -> Option<E::VirtualAddress> {
        self.cache_single_address(AddressAnalysis::AiAddMilitaryToRegion, |s| {
            let train_military = s.ai_train_military(actx)?;
            ai::add_military_to_region(actx, train_military, s.regions(actx).ai_regions?)
        })
    }

    fn vertex_buffer(&mut self, actx: &AnalysisCtx<'e, E>) -> Option<Operand<'e>> {
        self.cache_single_operand(OperandAnalysis::VertexBuffer, |s| {
            renderer::vertex_buffer(actx, &s.renderer_vtables(actx))
        })
    }

    fn crt_fastfail(&mut self, actx: &AnalysisCtx<'e, E>) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.crt_fastfail.cached() {
            return cached;
        }
        let result = Rc::new(crt::fastfail(actx));
        self.crt_fastfail.cache(&result);
        result
    }
}

#[cfg(feature = "x86")]
impl<'e> AnalysisX86<'e> {
    pub fn new(
        binary: &'e BinaryFile<VirtualAddress>,
        ctx: scarf::OperandCtx<'e>,
    ) -> AnalysisX86<'e> {
        AnalysisX86(Analysis::new(binary, ctx))
    }

    pub fn firegraft_addresses(&mut self) -> Rc<FiregraftAddresses<VirtualAddress>> {
        self.0.firegraft_addresses()
    }

    pub fn dat(&mut self, ty: DatType) -> Option<DatTablePtr<'e>> {
        self.0.dat(ty)
    }

    pub fn file_hook(&mut self) -> Rc<Vec<VirtualAddress>> {
        self.0.file_hook()
    }

    pub fn rng(&mut self) -> Rc<Rng<'e>> {
        self.0.rng()
    }

    pub fn step_objects(&mut self) -> Option<VirtualAddress> {
        self.0.step_objects()
    }

    pub fn game(&mut self) -> Option<Operand<'e>> {
        self.0.game()
    }

    pub fn aiscript_hook(&mut self) -> Rc<Option<AiScriptHook<'e, VirtualAddress>>> {
        self.0.aiscript_hook()
    }

    pub fn regions(&mut self) -> Rc<RegionRelated<'e, VirtualAddress>> {
        self.0.regions()
    }

    pub fn pathing(&mut self) -> Option<Operand<'e>> {
        self.0.pathing()
    }

    pub fn active_hidden_units(&mut self) -> Rc<ActiveHiddenUnits<'e>> {
        self.0.active_hidden_units()
    }

    pub fn order_issuing(&mut self) -> Rc<OrderIssuing<VirtualAddress>> {
        self.0.order_issuing()
    }

    pub fn process_commands(&mut self) -> Rc<ProcessCommands<'e, VirtualAddress>> {
        self.0.process_commands()
    }

    pub fn command_user(&mut self) -> Option<Operand<'e>> {
        self.0.command_user()
    }

    // May return an overly long array
    pub fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        self.0.command_lengths()
    }

    pub fn selections(&mut self) -> Rc<Selections<'e>> {
        self.0.selections()
    }

    pub fn is_replay(&mut self) -> Option<Operand<'e>> {
        self.0.is_replay()
    }

    pub fn process_lobby_commands(&mut self) -> Option<VirtualAddress> {
        self.0.process_lobby_commands()
    }

    pub fn send_command(&mut self) -> Option<VirtualAddress> {
        self.0.send_command()
    }

    pub fn print_text(&mut self) -> Option<VirtualAddress> {
        self.0.print_text()
    }

    pub fn init_map_from_path(&mut self) -> Option<VirtualAddress> {
        self.0.init_map_from_path()
    }

    pub fn choose_snp(&mut self) -> Option<VirtualAddress> {
        self.0.choose_snp()
    }

    pub fn renderer_vtables(&mut self) -> Rc<Vec<VirtualAddress>> {
        self.0.renderer_vtables()
    }

    pub fn vtables(&mut self) -> Vec<VirtualAddress> {
        self.0.vtables()
    }

    pub fn vtables_for_class(&mut self, name: &[u8]) -> Vec<VirtualAddress> {
        self.0.vtables_for_class(name)
    }

    pub fn single_player_start(&mut self) -> Rc<SinglePlayerStart<'e, VirtualAddress>> {
        self.0.single_player_start()
    }

    pub fn local_player_id(&mut self) -> Option<Operand<'e>> {
        self.0.local_player_id()
    }

    pub fn game_screen_rclick(&mut self) -> Rc<GameScreenRClick<'e, VirtualAddress>> {
        self.0.game_screen_rclick()
    }

    pub fn select_map_entry(&mut self) -> Rc<SelectMapEntry<'e, VirtualAddress>> {
        self.0.select_map_entry()
    }

    pub fn load_images(&mut self) -> Option<VirtualAddress> {
        self.0.load_images()
    }

    pub fn images_loaded(&mut self) -> Option<Operand<'e>> {
        self.0.images_loaded()
    }

    pub fn init_real_time_lighting(&mut self) -> Option<VirtualAddress> {
        self.0.init_real_time_lighting()
    }

    pub fn local_player_name(&mut self) -> Option<Operand<'e>> {
        self.0.local_player_name()
    }

    pub fn step_network(&mut self) -> Rc<StepNetwork<'e, VirtualAddress>> {
        self.0.step_network()
    }

    pub fn init_game_network(&mut self) -> Option<VirtualAddress> {
        self.0.init_game_network()
    }

    pub fn snp_definitions(&mut self) -> Option<SnpDefinitions<'e>> {
        self.0.snp_definitions()
    }

    pub fn lobby_state(&mut self) -> Option<Operand<'e>> {
        self.0.lobby_state()
    }

    pub fn init_storm_networking(&mut self) -> Rc<InitStormNetworking<VirtualAddress>> {
        self.0.init_storm_networking()
    }

    pub fn step_order(&mut self) -> Option<VirtualAddress> {
        self.0.step_order()
    }

    pub fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<'e, VirtualAddress>>>
    {
        self.0.step_order_hidden()
    }

    pub fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<'e, VirtualAddress>>>
    {
        self.0.step_secondary_order()
    }

    pub fn step_iscript(&mut self) -> Rc<StepIscript<'e, VirtualAddress>> {
        self.0.step_iscript()
    }

    pub fn add_overlay_iscript(&mut self) -> Option<VirtualAddress> {
        self.0.add_overlay_iscript()
    }

    pub fn draw_cursor_marker(&mut self) -> Option<Operand<'e>> {
        self.0.draw_cursor_marker()
    }

    pub fn play_smk(&mut self) -> Option<VirtualAddress> {
        self.0.play_smk()
    }

    pub fn game_init(&mut self) -> Rc<GameInit<'e, VirtualAddress>> {
        self.0.game_init()
    }

    pub fn misc_clientside(&mut self) -> Rc<MiscClientSide<'e>> {
        self.0.misc_clientside()
    }

    pub fn init_units(&mut self) -> Option<VirtualAddress> {
        self.0.init_units()
    }

    pub fn load_dat(&mut self) -> Option<VirtualAddress> {
        self.0.load_dat()
    }

    pub fn units(&mut self) -> Option<Operand<'e>> {
        self.0.units()
    }

    pub fn first_ai_script(&mut self) -> Option<Operand<'e>> {
        self.0.first_ai_script()
    }

    pub fn first_guard_ai(&mut self) -> Option<Operand<'e>> {
        self.0.first_guard_ai()
    }

    pub fn player_ai_towns(&mut self) -> Option<Operand<'e>> {
        self.0.player_ai_towns()
    }

    pub fn player_ai(&mut self) -> Option<Operand<'e>> {
        self.0.player_ai()
    }

    pub fn init_game(&mut self) -> Rc<InitGame<'e, VirtualAddress>> {
        self.0.init_game()
    }

    pub fn sprites(&mut self) -> Rc<Sprites<'e, VirtualAddress>> {
        self.0.sprites()
    }

    pub fn eud_table(&mut self) -> Rc<EudTable<'e>> {
        self.0.eud_table()
    }

    pub fn map_tile_flags(&mut self) -> Rc<MapTileFlags<'e, VirtualAddress>> {
        self.0.map_tile_flags()
    }

    pub fn players(&mut self) -> Option<Operand<'e>> {
        self.0.players()
    }

    pub fn draw_image(&mut self) -> Option<VirtualAddress> {
        self.0.draw_image()
    }

    pub fn bullet_creation(&mut self) -> Rc<BulletCreation<'e, VirtualAddress>> {
        self.0.bullet_creation()
    }

    pub fn net_players(&mut self) -> Rc<NetPlayers<'e, VirtualAddress>> {
        self.0.net_players()
    }

    pub fn campaigns(&mut self) -> Option<Operand<'e>> {
        self.0.campaigns()
    }

    pub fn run_dialog(&mut self) -> Option<VirtualAddress> {
        self.0.run_dialog()
    }

    pub fn ai_update_attack_target(&mut self) -> Option<VirtualAddress> {
        self.0.ai_update_attack_target()
    }

    pub fn is_outside_game_screen(&mut self) -> Option<VirtualAddress> {
        self.0.is_outside_game_screen()
    }

    pub fn game_coord_conversion(&mut self) -> Rc<GameCoordConversion<'e>> {
        self.0.game_coord_conversion()
    }

    pub fn fow_sprites(&mut self) -> Rc<FowSprites<'e>> {
        self.0.fow_sprites()
    }

    pub fn spawn_dialog(&mut self) -> Option<VirtualAddress> {
        self.0.spawn_dialog()
    }

    pub fn unit_creation(&mut self) -> Rc<UnitCreation<VirtualAddress>> {
        self.0.unit_creation()
    }

    pub fn fonts(&mut self) -> Option<Operand<'e>> {
        self.0.fonts()
    }

    pub fn init_sprites(&mut self) -> Option<VirtualAddress> {
        self.0.init_sprites()
    }

    pub fn sprite_array(&mut self) -> Option<(Operand<'e>, u32)> {
        self.0.sprite_array()
    }

    pub fn serialize_sprites(&mut self) -> Option<VirtualAddress> {
        self.0.serialize_sprites()
    }

    pub fn deserialize_sprites(&mut self) -> Option<VirtualAddress> {
        self.0.deserialize_sprites()
    }

    pub fn limits(&mut self) -> Rc<Limits<'e, VirtualAddress>> {
        self.0.limits()
    }

    pub fn font_cache_render_ascii(&mut self) -> Option<VirtualAddress> {
        self.0.font_cache_render_ascii()
    }

    pub fn ttf_cache_character(&mut self) -> Option<VirtualAddress> {
        self.0.ttf_cache_character()
    }

    pub fn ttf_render_sdf(&mut self) -> Option<VirtualAddress> {
        self.0.ttf_render_sdf()
    }

    /// Memory allocation function that at least TTF code uses.
    ///
    /// (Should be Win32 HeapAlloc with a specific heap)
    pub fn ttf_malloc(&mut self) -> Option<VirtualAddress> {
        self.0.ttf_malloc()
    }

    /// Offset to CreateGameScreen.OnMultiplayerGameCreate in the dialog's vtable
    pub fn create_game_dialog_vtbl_on_multiplayer_create(&mut self) -> Option<usize> {
        self.0.create_game_dialog_vtbl_on_multiplayer_create()
    }

    pub fn tooltip_draw_func(&mut self) -> Option<Operand<'e>> {
        self.0.tooltip_draw_func()
    }

    pub fn current_tooltip_ctrl(&mut self) -> Option<Operand<'e>> {
        self.0.current_tooltip_ctrl()
    }

    pub fn layout_draw_text(&mut self) -> Option<VirtualAddress> {
        self.0.layout_draw_text()
    }

    pub fn graphic_layers(&mut self) -> Option<Operand<'e>> {
        self.0.graphic_layers()
    }

    pub fn draw_f10_menu_tooltip(&mut self) -> Option<VirtualAddress> {
        self.0.draw_f10_menu_tooltip()
    }

    pub fn draw_tooltip_layer(&mut self) -> Option<VirtualAddress> {
        self.0.draw_tooltip_layer()
    }

    pub fn draw_graphic_layers(&mut self) -> Option<VirtualAddress> {
        self.0.draw_graphic_layers()
    }

    pub fn prism_vertex_shaders(&mut self) -> Rc<Vec<VirtualAddress>> {
        self.0.prism_vertex_shaders()
    }

    pub fn prism_pixel_shaders(&mut self) -> Rc<Vec<VirtualAddress>> {
        self.0.prism_pixel_shaders()
    }

    pub fn ai_attack_prepare(&mut self) -> Option<VirtualAddress> {
        self.0.ai_attack_prepare()
    }

    pub fn ai_step_region(&mut self) -> Option<VirtualAddress> {
        self.0.ai_step_region()
    }

    pub fn ai_spend_money(&mut self) -> Option<VirtualAddress> {
        self.0.ai_spend_money()
    }

    pub fn join_game(&mut self) -> Option<VirtualAddress> {
        self.0.join_game()
    }

    pub fn snet_initialize_provider(&mut self) -> Option<VirtualAddress> {
        self.0.snet_initialize_provider()
    }

    pub fn set_status_screen_tooltip(&mut self) -> Option<VirtualAddress> {
        self.0.set_status_screen_tooltip()
    }

    pub fn dat_patches(&mut self) -> Option<Rc<DatPatches<'e, VirtualAddress>>> {
        self.0.dat_patches()
    }

    pub fn do_attack(&mut self) -> Option<VirtualAddress> {
        self.0.do_attack()
    }

    pub fn do_attack_main(&mut self) -> Option<VirtualAddress> {
        self.0.do_attack_main()
    }

    pub fn last_bullet_spawner(&mut self) -> Option<Operand<'e>> {
        self.0.last_bullet_spawner()
    }

    pub fn smem_alloc(&mut self) -> Option<VirtualAddress> {
        self.0.smem_alloc()
    }

    pub fn smem_free(&mut self) -> Option<VirtualAddress> {
        self.0.smem_free()
    }

    pub fn cmdicons_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.0.cmdicons_ddsgrp()
    }

    pub fn cmdbtns_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.0.cmdbtns_ddsgrp()
    }

    pub fn mouse_xy(&mut self) -> MouseXy<'e, VirtualAddress> {
        self.0.mouse_xy()
    }

    pub fn status_screen_mode(&mut self) -> Option<Operand<'e>> {
        self.0.status_screen_mode()
    }

    pub fn check_unit_requirements(&mut self) -> Option<VirtualAddress> {
        self.0.check_unit_requirements()
    }

    pub fn check_dat_requirements(&mut self) -> Option<VirtualAddress> {
        self.0.check_dat_requirements()
    }

    pub fn dat_requirement_error(&mut self) -> Option<Operand<'e>> {
        self.0.dat_requirement_error()
    }

    pub fn cheat_flags(&mut self) -> Option<Operand<'e>> {
        self.0.cheat_flags()
    }

    pub fn unit_strength(&mut self) -> Option<Operand<'e>> {
        self.0.unit_strength()
    }

    pub fn grpwire_grp(&mut self) -> Option<Operand<'e>> {
        self.0.grpwire_grp()
    }

    pub fn grpwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.0.grpwire_ddsgrp()
    }

    pub fn tranwire_grp(&mut self) -> Option<Operand<'e>> {
        self.0.tranwire_grp()
    }

    pub fn tranwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.0.tranwire_ddsgrp()
    }

    pub fn status_screen(&mut self) -> Option<Operand<'e>> {
        self.0.status_screen()
    }

    pub fn status_screen_event_handler(&mut self) -> Option<VirtualAddress> {
        self.0.status_screen_event_handler()
    }

    pub fn wirefram_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.0.wirefram_ddsgrp()
    }

    pub fn init_status_screen(&mut self) -> Option<VirtualAddress> {
        self.0.init_status_screen()
    }

    pub fn trigger_conditions(&mut self) -> Option<VirtualAddress> {
        self.0.trigger_conditions()
    }

    pub fn trigger_actions(&mut self) -> Option<VirtualAddress> {
        self.0.trigger_actions()
    }

    pub fn trigger_completed_units_cache(&mut self) -> Option<Operand<'e>> {
        self.0.trigger_completed_units_cache()
    }

    pub fn trigger_all_units_cache(&mut self) -> Option<Operand<'e>> {
        self.0.trigger_all_units_cache()
    }

    pub fn snet_send_packets(&mut self) -> Option<VirtualAddress> {
        self.0.snet_send_packets()
    }

    pub fn snet_recv_packets(&mut self) -> Option<VirtualAddress> {
        self.0.snet_recv_packets()
    }

    pub fn chk_init_players(&mut self) -> Option<Operand<'e>> {
        self.0.chk_init_players()
    }

    pub fn original_chk_player_types(&mut self) -> Option<Operand<'e>> {
        self.0.original_chk_player_types()
    }

    pub fn give_ai(&mut self) -> Option<VirtualAddress> {
        self.0.give_ai()
    }

    pub fn play_sound(&mut self) -> Option<VirtualAddress> {
        self.0.play_sound()
    }

    pub fn ai_prepare_moving_to(&mut self) -> Option<VirtualAddress> {
        self.0.ai_prepare_moving_to()
    }

    pub fn ai_transport_reachability_cached_region(&mut self) -> Option<Operand<'e>> {
        self.0.ai_transport_reachability_cached_region()
    }

    pub fn player_unit_skins(&mut self) -> Option<Operand<'e>> {
        self.0.player_unit_skins()
    }

    pub fn replay_minimap_unexplored_fog_patch(&mut self) -> Option<Rc<Patch<VirtualAddress>>> {
        self.0.replay_minimap_unexplored_fog_patch()
    }

    pub fn step_replay_commands(&mut self) -> Option<VirtualAddress> {
        self.0.step_replay_commands()
    }

    pub fn replay_data(&mut self) -> Option<Operand<'e>> {
        self.0.replay_data()
    }

    pub fn ai_train_military(&mut self) -> Option<VirtualAddress> {
        self.0.ai_train_military()
    }

    pub fn ai_add_military_to_region(&mut self) -> Option<VirtualAddress> {
        self.0.ai_add_military_to_region()
    }

    pub fn vertex_buffer(&mut self) -> Option<Operand<'e>> {
        self.0.vertex_buffer()
    }

    pub fn crt_fastfail(&mut self) -> Rc<Vec<VirtualAddress>> {
        self.0.crt_fastfail()
    }
}

pub struct DatPatchesDebug<'e, Va: VirtualAddressTrait> {
    pub tables: fxhash::FxHashMap<DatType, DatTablePatchesDebug<Va>>,
    pub replaces: Vec<(Va, Vec<u8>)>,
    pub func_replaces: Vec<(Va, DatReplaceFunc)>,
    pub hooks: Vec<(Va, u8, Vec<u8>)>,
    pub two_step_hooks: Vec<(Va, Va, u8, Vec<u8>)>,
    pub ext_array_patches: Vec<(Va, Option<Va>, u8, u32, Operand<'e>)>,
    pub ext_array_args: Vec<(Va, Vec<(usize, u8)>)>,
    pub grp_index_hooks: Vec<Va>,
    pub grp_texture_hooks: Vec<(Va, u8, Operand<'e>, Operand<'e>, Operand<'e>)>,
}

pub struct DatTablePatchesDebug<Va: VirtualAddressTrait> {
    pub array_patches: Vec<Vec<(Va, i32, u32)>>,
    pub entry_counts: Vec<Va>,
}

impl<Va: VirtualAddressTrait> Default for DatTablePatchesDebug<Va> {
    fn default() -> Self {
        DatTablePatchesDebug {
            array_patches: Vec::new(),
            entry_counts: Vec::new(),
        }
    }
}

// Tries to return a func index to the address less or equal to `entry` that is definitely a
// function entry. Has still a hard limit.
fn first_definite_entry<Va: VirtualAddressTrait>(
    binary: &BinaryFile<Va>,
    entry: Va,
    funcs: &[Va],
    limit: usize,
) -> (usize, usize) {
    fn is_definitely_entry<Va: VirtualAddressTrait>(
        binary: &BinaryFile<Va>,
        entry: Va,
    ) -> bool {
        if entry.as_u64() & 0xf != 0 {
            return false;
        }
        // Casting to u64 -> u32 is fine as there aren't going to be 4GB binaries
        let relative = (entry.as_u64() - binary.base.as_u64()) as u32;
        let first_bytes = match binary.slice_from(relative..relative + 3) {
            Ok(o) => o,
            Err(_) => return false,
        };
        if Va::SIZE == 4 {
            // push ebx; mov ebx, esp or push ebp; mov ebp, esp
            // Two different encodings for both
            first_bytes == [0x53, 0x8b, 0xdc] ||
                first_bytes == [0x53, 0x89, 0xe3] ||
                first_bytes == [0x55, 0x8b, 0xec] ||
                first_bytes == [0x55, 0x89, 0xe5]
        } else {
            unimplemented!();
        }
    }
    let mut index = funcs.binary_search_by(|&x| match x <= entry {
        true => std::cmp::Ordering::Less,
        false => std::cmp::Ordering::Greater,
    }).unwrap_or_else(|e| e);
    let end = index;
    if index != 0 {
        index -= 1;
    }
    while index != 0 && !is_definitely_entry(binary, funcs[index]) && end - index < limit {
        index -= 1;
    }
    (index, end)
}

#[derive(Debug)]
pub struct StringRefs<Va> {
    pub use_address: Va,
    pub func_entry: Va,
    pub string_address: Va,
}

#[derive(Debug, Copy, Clone)]
pub struct GlobalRefs<Va: VirtualAddressTrait> {
    pub use_address: Va,
    pub func_entry: Va,
}

pub enum EntryOf<R> {
    Ok(R),
    Retry,
    Stop,
}

impl<R> EntryOf<R> {
    pub fn is_ok(&self) -> bool {
        match self {
            EntryOf::Ok(..) => true,
            EntryOf::Retry | EntryOf::Stop => false,
        }
    }
}

#[derive(Debug)]
enum EntryOfResult<R, Va: VirtualAddressTrait> {
    /// Found the result which was looked for, as well as the entry
    Ok(Va, R),
    /// No result, but determined the address to be entry
    Entry(Va),
    None,
}

impl<R, Va: VirtualAddressTrait> EntryOfResult<R, Va> {
    pub fn into_option(self) -> Option<R> {
        match self {
            EntryOfResult::Ok(_, b) => Some(b),
            _ => None,
        }
    }

    pub fn into_option_with_entry(self) -> Option<(Va, R)> {
        match self {
            EntryOfResult::Ok(a, b) => Some((a, b)),
            _ => None,
        }
    }
}

/// Better version of entry_of, retries with an earlier func if the cb returns false,
/// helps against false positive func entries.
fn entry_of_until<'a, Va: VirtualAddressTrait, R, F>(
    binary: &BinaryFile<Va>,
    funcs: &[Va],
    caller: Va,
    mut cb: F,
) -> EntryOfResult<R, Va>
where F: FnMut(Va) -> EntryOf<R>
{
    entry_of_until_with_limit(binary, funcs, caller, 16, &mut cb)
}

fn entry_of_until_with_limit<'a, Va: VirtualAddressTrait, R, F>(
    binary: &BinaryFile<Va>,
    funcs: &[Va],
    caller: Va,
    limit: usize,
    mut cb: F,
) -> EntryOfResult<R, Va>
where F: FnMut(Va) -> EntryOf<R>
{
    let (start, end) = first_definite_entry(binary, caller, funcs, limit);
    for &entry in funcs.iter().take(end).skip(start) {
        match cb(entry) {
            EntryOf::Ok(s) => return EntryOfResult::Ok(entry, s),
            EntryOf::Stop => return EntryOfResult::Entry(entry),
            EntryOf::Retry => (),
        }
    }
    //debug!("entry_of_until limit reached for caller {:?} {:?}", caller, start..end);
    EntryOfResult::None
}

struct FunctionFinder<'a, 'e, E: ExecutionStateTrait<'e>> {
    functions: &'a [E::VirtualAddress],
    relocs_with_values: &'a [RelocValues<E::VirtualAddress>],
    functions_with_callers: &'a [FuncCallPair<E::VirtualAddress>],
}

impl<'a, 'e, E: ExecutionStateTrait<'e>> FunctionFinder<'a, 'e, E> {
    pub fn functions(&self) -> &[E::VirtualAddress] {
        &self.functions
    }

    pub fn relocs_with_values(&self) -> &[RelocValues<E::VirtualAddress>] {
        &self.relocs_with_values
    }

    pub fn functions_with_callers(&self) -> &[FuncCallPair<E::VirtualAddress>] {
        &self.functions_with_callers
    }

    pub fn string_refs<'acx>(
        &self,
        cache: &'acx AnalysisCtx<'e, E>,
        string: &[u8],
    ) -> BumpVec<'acx, StringRefs<E::VirtualAddress>> {
        let rdata = cache.binary_sections.rdata;
        let bump = &cache.bump;
        let str_ref_addrs = find_strings_casei(bump, &rdata.data, string);
        // (Use rva, string rva)
        let rdata_base = rdata.virtual_address;
        let result = str_ref_addrs
            .into_iter()
            .flat_map(|str_rva| {
                let addr = rdata_base + str_rva.0;
                let ptr_refs = self.find_functions_using_global(cache, addr);
                ptr_refs.into_iter().map(move |x| (x.use_address, x.func_entry, str_rva))
            })
            .map(|(code_va, func_entry, str_rva)| {
                StringRefs {
                    use_address: code_va,
                    func_entry,
                    string_address: rdata_base + str_rva.0,
                }
            });
        BumpVec::from_iter_in(result, bump)
    }

    fn find_callers<'acx>(
        &self,
        analysis: &'acx AnalysisCtx<'e, E>,
        func_entry: E::VirtualAddress,
    ) -> BumpVec<'acx, E::VirtualAddress> {
        use std::cmp::Ordering;
        let callers = self.functions_with_callers();
        let lower_bound = callers.binary_search_by(|x| match x.callee >= func_entry {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let result = (&callers[lower_bound..]).iter()
            .take_while(|&x| x.callee == func_entry)
            .map(|x| x.caller);
        BumpVec::from_iter_in(result, &analysis.bump)
    }

    pub fn find_functions_using_global<'acx>(
        &self,
        actx: &'acx AnalysisCtx<'e, E>,
        addr: E::VirtualAddress,
    ) -> BumpVec<'acx, GlobalRefs<E::VirtualAddress>> {
        use std::cmp::Ordering;

        let relocs = self.relocs_with_values();
        let functions = self.functions();
        let start = relocs.binary_search_by(|x| match x.value >= addr {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let result = (&relocs[start..]).iter()
            .take_while(|x| x.value == addr)
            .map(|x| {
                let index = functions.binary_search(&x.address).unwrap_or_else(|e| e);
                GlobalRefs {
                    use_address: x.address,
                    func_entry: functions[index.saturating_sub(1)],
                }
            });
        BumpVec::from_iter_in(result, &actx.bump)
    }
}

fn read_u32_at<Va: VirtualAddressTrait>(section: &BinarySection<Va>, offset: Rva) -> Option<u32> {
    section.data.get(offset.0 as usize..offset.0 as usize + 4)
        .and_then(|mut x| x.read_u32::<LE>().ok())
}

/// Returns any matching strings as Rvas.
///
/// Remember to null-terminate strings if needed =)
fn find_strings_casei<'a>(bump: &'a Bump, mut data: &[u8], needle: &[u8]) -> BumpVec<'a, Rva> {
    let mut ret = BumpVec::new_in(bump);
    let mut offset = 0usize;
    let first = needle[0];
    while data.len() >= needle.len() {
        let result = match first {
            x if x >= b'a' && x <= b'z' => {
                memchr::memchr2(x, x.wrapping_sub(b'a').wrapping_add(b'A'), data)
            }
            x if x >= b'A' && x <= b'Z' => {
                memchr::memchr2(x, x.wrapping_sub(b'A').wrapping_add(b'a'), data)
            }
            x => memchr::memchr(x, data),
        };
        match result {
            Some(pos) => {
                let end = pos.wrapping_add(needle.len());
                if end > data.len() {
                    break;
                }
                let compare = match data.get(pos..end) {
                    Some(s) => s,
                    None => break,
                };
                if needle.eq_ignore_ascii_case(compare) {
                    ret.push(Rva((offset.wrapping_add(pos)) as u32));
                }
                offset = offset.wrapping_add(pos).wrapping_add(1);
                data = match data.get(pos.wrapping_add(1)..) {
                    Some(s) => s,
                    None => break,
                };
            }
            None => break,
        }
    }
    ret
}

fn find_address_refs<'a, Va: VirtualAddressTrait>(
    bump: &'a Bump,
    data: &[u8],
    addr: Va,
) -> BumpVec<'a, Rva> {
    let mut result = if Va::SIZE == 4 {
        let bytes = (addr.as_u64() as u32).to_le_bytes();
        find_bytes(bump, data, &bytes[..])
    } else {
        let bytes = addr.as_u64().to_le_bytes();
        find_bytes(bump, data, &bytes[..])
    };
    // Filter out if align is less than 4.
    // 64-bit bw can have 4-aligned pointers.
    result.retain(|x| x.0 & 3 == 0);
    result
}

fn find_bytes<'a>(bump: &'a Bump, mut data: &[u8], needle: &[u8]) -> BumpVec<'a, Rva> {
    use memmem::{TwoWaySearcher, Searcher};

    let mut ret = BumpVec::new_in(bump);
    let mut pos = 0;
    let searcher = TwoWaySearcher::new(needle);
    while let Some(index) = searcher.search_in(data) {
        pos += index as u32;
        ret.push(Rva(pos));
        pos += needle.len() as u32;
        data = &data[index + needle.len()..];
    }
    ret
}

fn if_callable_const<'e, A: analysis::Analyzer<'e>>(
    binary: &BinaryFile<<A::Exec as ExecutionStateTrait<'e>>::VirtualAddress>,
    dest: Operand<'e>,
    ctrl: &mut Control<'e, '_, '_, A>
) -> Option<<A::Exec as ExecutionStateTrait<'e>>::VirtualAddress> {
    ctrl.resolve(dest).if_constant()
        .and_then(|dest| {
            let dest = <A::Exec as ExecutionStateTrait<'_>>::VirtualAddress::from_u64(dest);
            let code_section = binary.code_section();
            let code_section_end = code_section.virtual_address + code_section.virtual_size;
            if dest > code_section.virtual_address && dest < code_section_end {
                Some(dest)
            } else {
                None
            }
        })
}

/// Helper extension functions for Option<(Operand<'e>, Operand<'e>)>.
trait OptionExt<'e> {
    /// `opt.and_either(x)` is equivalent to
    /// `opt.and_then(|(l, r)| Operand::either(l, r, x))`
    fn and_either<F, T>(self, cb: F) -> Option<(T, Operand<'e>)>
    where F: FnMut(Operand<'e>) -> Option<T>;
    /// `opt.and_either_other(x)` is equivalent to
    /// `opt.and_then(|(l, r)| Operand::either(l, r, x)).map(|(_, other)| other)`
    fn and_either_other<F, T>(self, cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> Option<T>;
}

impl<'e> OptionExt<'e> for Option<(Operand<'e>, Operand<'e>)> {
    fn and_either<F, T>(self, cb: F) -> Option<(T, Operand<'e>)>
    where F: FnMut(Operand<'e>) -> Option<T>
    {
        self.and_then(|(l, r)| Operand::either(l, r, cb))
    }

    fn and_either_other<F, T>(self, cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> Option<T>
    {
        self.and_either(cb).map(|(_, other)| other)
    }
}

/// Returns true if the stack is setup for a call that seems to be reporting an assertion
/// error
fn seems_assertion_call<'exec, A: analysis::Analyzer<'exec>, Va: VirtualAddressTrait>(
    ctrl: &mut Control<'exec, '_, '_, A>,
    binary: &BinaryFile<Va>,
) -> bool {
    let ctx = ctrl.ctx();
    let esp = ctx.register(4);
    let arg1 = match ctrl.resolve(ctx.mem32(esp)).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg2 = match ctrl.resolve(ctx.mem32(ctx.add(esp, ctx.constant(4)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg3 = match ctrl.resolve(ctx.mem32(ctx.add(esp, ctx.constant(8)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg4 = match ctrl.resolve(ctx.mem32(ctx.add(esp, ctx.constant(0xc)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    if arg4 == 0 || arg4 > 12000 {
        return false;
    }
    // Could check that these are strings
    if binary.section_by_addr(Va::from_u64(arg1)).is_none() {
        return false;
    }
    if binary.section_by_addr(Va::from_u64(arg2)).is_none() {
        return false;
    }
    if binary.section_by_addr(Va::from_u64(arg3)).is_none() {
        return false;
    }
    true
}

// bool true => eq, bool false => not eq
fn if_arithmetic_eq_neq<'e>(op: Operand<'e>) -> Option<(Operand<'e>, Operand<'e>, bool)> {
    op.if_arithmetic_eq()
        .map(|(l, r)| {
            Operand::either(l, r, |x| x.if_constant().filter(|&c| c == 0))
                .and_then(|(_, other)| other.if_arithmetic_eq())
                .map(|(l, r)| (l, r, false))
                .unwrap_or_else(|| (l, r, true))
        })
}

fn unwrap_sext<'e>(operand: Operand<'e>) -> Operand<'e> {
    match *operand.ty() {
        scarf::operand::OperandType::SignExtend(val, ..) => val,
        _ => operand,
    }
}

trait OperandExt<'e> {
    fn if_mem32_offset(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_add_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_sub_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_mul_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_and_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_lsh_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_rsh_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_gt_const(self, offset: u64) -> Option<Operand<'e>>;
}

impl<'e> OperandExt<'e> for Operand<'e> {
    fn if_mem32_offset(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_mem32()?.if_arithmetic_add()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_add_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_add()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_sub_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_sub()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_mul_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_mul()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_and_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_and()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_lsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(scarf::operand::ArithOpType::Lsh)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_rsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(scarf::operand::ArithOpType::Rsh)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_gt_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(scarf::operand::ArithOpType::GreaterThan)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }
}

// This is slightly better for binary size than BumpVec::with_capcity_in,
// as bumpalo is otherwise pretty bad with monomorphizing
fn bumpvec_with_capacity<T>(cap: usize, bump: &Bump) -> BumpVec<'_, T> {
    let mut vec = BumpVec::new_in(bump);
    vec.reserve(cap);
    vec
}

trait ControlExt<'e, E: ExecutionStateTrait<'e>> {
    fn resolve_va(&mut self, operand: Operand<'e>) -> Option<E::VirtualAddress>;
}

impl<'a, 'b, 'e, A: scarf::analysis::Analyzer<'e>> ControlExt<'e, A::Exec> for
    scarf::analysis::Control<'e, 'a, 'b, A>
{
    fn resolve_va(&mut self, operand: Operand<'e>) ->
        Option<<A::Exec as ExecutionStateTrait<'e>>::VirtualAddress>
    {
        self.resolve(operand).if_constant()
            .filter(|&va| va >= self.binary().base().as_u64())
            .map(|x| <A::Exec as ExecutionStateTrait<'e>>::VirtualAddress::from_u64(x))
    }
}
