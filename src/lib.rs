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
    ctx: scarf::OperandCtx<'e>,
    bump: Bump,
    binary: &'e BinaryFile<E::VirtualAddress>,
    binary_sections: BinarySections<'e, E>,
    arg_cache: ArgCache<'e, E>,
    cache: AnalysisCache<'e, E>,
}

struct BinarySections<'e, E: ExecutionStateTrait<'e>> {
    text: &'e BinarySection<E::VirtualAddress>,
    data: &'e BinarySection<E::VirtualAddress>,
    rdata: &'e BinarySection<E::VirtualAddress>,
}

struct AnalysisCache<'e, E: ExecutionStateTrait<'e>> {
    relocs: Cached<Rc<Vec<E::VirtualAddress>>>,
    relocs_with_values: Cached<Rc<Vec<RelocValues<E::VirtualAddress>>>>,
    functions: Cached<Rc<Vec<E::VirtualAddress>>>,
    functions_with_callers: Cached<Rc<Vec<FuncCallPair<E::VirtualAddress>>>>,
    switch_tables: Cached<Rc<Vec<SwitchTable<E::VirtualAddress>>>>,
    open_file: Cached<Rc<Vec<E::VirtualAddress>>>,
    firegraft_addresses: Cached<Rc<FiregraftAddresses<E::VirtualAddress>>>,
    aiscript_hook: Cached<Rc<Option<AiScriptHook<'e, E::VirtualAddress>>>>,
    game: Cached<Option<Operand<'e>>>,
    rng: Cached<Rc<Rng<'e>>>,
    step_objects: Cached<Option<E::VirtualAddress>>,
    player_ai: Cached<Option<Operand<'e>>>,
    regions: Cached<Rc<RegionRelated<'e, E::VirtualAddress>>>,
    pathing: Cached<Option<Operand<'e>>>,
    active_hidden_units: Cached<Rc<ActiveHiddenUnits<'e>>>,
    order_issuing: Cached<Rc<OrderIssuing<E::VirtualAddress>>>,
    process_commands: Cached<Rc<ProcessCommands<'e, E::VirtualAddress>>>,
    command_lengths: Cached<Rc<Vec<u32>>>,
    command_user: Cached<Option<Operand<'e>>>,
    selections: Cached<Rc<Selections<'e>>>,
    is_replay: Cached<Option<Operand<'e>>>,
    process_lobby_commands: Cached<Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)>>,
    send_command: Cached<Option<E::VirtualAddress>>,
    print_text: Cached<Option<E::VirtualAddress>>,
    step_order: Cached<Option<E::VirtualAddress>>,
    step_order_hidden: Cached<Rc<Vec<StepOrderHiddenHook<'e, E::VirtualAddress>>>>,
    init_units: Cached<InitUnits<E::VirtualAddress>>,
    step_secondary_order: Cached<Rc<Vec<SecondaryOrderHook<'e, E::VirtualAddress>>>>,
    init_game: Cached<Rc<InitGame<'e, E::VirtualAddress>>>,
    units: Cached<Option<Operand<'e>>>,
    game_screen_rclick: Cached<Rc<GameScreenRClick<'e, E::VirtualAddress>>>,
    first_ai_script: Cached<Option<Operand<'e>>>,
    first_guard_ai: Cached<Option<Operand<'e>>>,
    player_ai_towns: Cached<Option<Operand<'e>>>,
    step_iscript: Cached<Rc<StepIscript<'e, E::VirtualAddress>>>,
    sprites: Cached<Rc<Sprites<'e, E::VirtualAddress>>>,
    eud: Cached<Rc<EudTable<'e>>>,
    map_tile_flags: Cached<Rc<MapTileFlags<'e, E::VirtualAddress>>>,
    players: Cached<Option<Operand<'e>>>,
    draw_image: Cached<Option<E::VirtualAddress>>,
    renderer_vtables: Cached<Rc<Vec<E::VirtualAddress>>>,
    local_player_id: Cached<Option<Operand<'e>>>,
    bullet_creation: Cached<Rc<BulletCreation<'e, E::VirtualAddress>>>,
    net_players: Cached<Rc<NetPlayers<'e, E::VirtualAddress>>>,
    play_smk: Cached<Option<E::VirtualAddress>>,
    game_init: Cached<Rc<GameInit<'e, E::VirtualAddress>>>,
    add_overlay_iscript: Cached<Option<E::VirtualAddress>>,
    campaigns: Cached<Option<Operand<'e>>>,
    run_dialog: Cached<Option<E::VirtualAddress>>,
    ai_update_attack_target: Cached<Option<E::VirtualAddress>>,
    is_outside_game_screen: Cached<Option<E::VirtualAddress>>,
    game_coord_conversion: Cached<Rc<GameCoordConversion<'e>>>,
    fow_sprites: Cached<Rc<FowSprites<'e>>>,
    init_map_from_path: Cached<Option<InitMapFromPath<E::VirtualAddress>>>,
    choose_snp: Cached<Option<E::VirtualAddress>>,
    single_player_start: Cached<Rc<SinglePlayerStart<'e, E::VirtualAddress>>>,
    select_map_entry: Cached<Rc<SelectMapEntry<'e, E::VirtualAddress>>>,
    load_images: Cached<Option<E::VirtualAddress>>,
    images_loaded: Cached<ImagesLoaded<'e, E::VirtualAddress>>,
    local_player_name: Cached<Option<Operand<'e>>>,
    step_network: Cached<Rc<StepNetwork<'e, E::VirtualAddress>>>,
    init_game_network: Cached<Option<E::VirtualAddress>>,
    snp_definitions: Cached<Option<SnpDefinitions<'e>>>,
    lobby_state: Cached<Option<Operand<'e>>>,
    init_storm_networking: Cached<Rc<InitStormNetworking<E::VirtualAddress>>>,
    draw_cursor_marker: Cached<Option<Operand<'e>>>,
    misc_clientside: Cached<Rc<MiscClientSide<'e>>>,
    spawn_dialog: Cached<Option<E::VirtualAddress>>,
    unit_creation: Cached<Rc<UnitCreation<E::VirtualAddress>>>,
    fonts: Cached<Option<Operand<'e>>>,
    init_sprites: Cached<InitSprites<'e, E::VirtualAddress>>,
    sprite_serialization: Cached<SpriteSerialization<E::VirtualAddress>>,
    limits: Cached<Rc<Limits<'e, E::VirtualAddress>>>,
    font_render: Cached<FontRender<E::VirtualAddress>>,
    ttf_malloc: Cached<Option<E::VirtualAddress>>,
    create_game_dialog_vtbl_on_multiplayer_create: Cached<Option<usize>>,
    tooltip_related: Cached<TooltipRelated<'e, E::VirtualAddress>>,
    draw_graphic_layers: Cached<Option<E::VirtualAddress>>,
    prism_shaders: Cached<PrismShaders<E::VirtualAddress>>,
    ai_attack_prepare: Cached<Option<E::VirtualAddress>>,
    ai_step_region: Cached<Option<E::VirtualAddress>>,
    join_game: Cached<Option<E::VirtualAddress>>,
    snet_initialize_provider: Cached<Option<E::VirtualAddress>>,
    do_attack: Cached<Option<step_order::DoAttack<'e, E::VirtualAddress>>>,
    dat_patches: Cached<Option<Rc<DatPatches<'e, E::VirtualAddress>>>>,
    button_ddsgrps: Cached<dialog::ButtonDdsgrps<'e>>,
    mouse_xy: Cached<dialog::MouseXy<'e, E::VirtualAddress>>,
    status_screen_mode: Cached<Option<Operand<'e>>>,
    check_unit_requirements:
        Cached<Option<requirements::CheckUnitRequirements<'e, E::VirtualAddress>>>,
    check_dat_requirements: Cached<Option<E::VirtualAddress>>,
    cheat_flags: Cached<Option<Operand<'e>>>,
    unit_strength: Cached<Option<Operand<'e>>>,
    multi_wireframes: Cached<MultiWireframes<'e, E::VirtualAddress>>,
    wirefram_ddsgrp: Cached<Option<Operand<'e>>>,
    run_triggers: Cached<RunTriggers<E::VirtualAddress>>,
    trigger_unit_count_caches: Cached<TriggerUnitCountCaches<'e>>,
    snet_handle_packets: Cached<SnetHandlePackets<E::VirtualAddress>>,
    chk_init_players: Cached<Option<Operand<'e>>>,
    original_chk_player_types: Cached<Option<Operand<'e>>>,
    give_ai: Cached<Option<E::VirtualAddress>>,
    play_sound: Cached<Option<E::VirtualAddress>>,
    ai_prepare_moving_to: Cached<Option<E::VirtualAddress>>,
    ai_transport_reachability_cached_region: Cached<Option<Operand<'e>>>,
    player_unit_skins: Cached<Option<Operand<'e>>>,
    replay_minimap_unexplored_fog_patch: Cached<Option<Rc<Patch<E::VirtualAddress>>>>,
    dat_tables: DatTables<'e>,
}

pub(crate) struct AnalysisCtx<'b, 'e, E: ExecutionStateTrait<'e>> {
    cache: &'b mut AnalysisCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    binary_sections: &'b BinarySections<'e, E>,
    ctx: scarf::OperandCtx<'e>,
    arg_cache: &'b ArgCache<'e, E>,
    bump: &'b Bump,
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
        Analysis {
            cache: AnalysisCache {
                relocs: Default::default(),
                relocs_with_values: Default::default(),
                functions: Default::default(),
                functions_with_callers: Default::default(),
                switch_tables: Default::default(),
                open_file: Default::default(),
                firegraft_addresses: Default::default(),
                aiscript_hook: Default::default(),
                game: Default::default(),
                rng: Default::default(),
                step_objects: Default::default(),
                player_ai: Default::default(),
                regions: Default::default(),
                pathing: Default::default(),
                active_hidden_units: Default::default(),
                order_issuing: Default::default(),
                process_commands: Default::default(),
                command_lengths: Default::default(),
                command_user: Default::default(),
                selections: Default::default(),
                is_replay: Default::default(),
                process_lobby_commands: Default::default(),
                send_command: Default::default(),
                print_text: Default::default(),
                step_order: Default::default(),
                step_order_hidden: Default::default(),
                step_secondary_order: Default::default(),
                init_units: Default::default(),
                units: Default::default(),
                game_screen_rclick: Default::default(),
                init_game: Default::default(),
                first_ai_script: Default::default(),
                first_guard_ai: Default::default(),
                player_ai_towns: Default::default(),
                step_iscript: Default::default(),
                sprites: Default::default(),
                eud: Default::default(),
                map_tile_flags: Default::default(),
                players: Default::default(),
                draw_image: Default::default(),
                renderer_vtables: Default::default(),
                local_player_id: Default::default(),
                bullet_creation: Default::default(),
                net_players: Default::default(),
                play_smk: Default::default(),
                game_init: Default::default(),
                add_overlay_iscript: Default::default(),
                campaigns: Default::default(),
                run_dialog: Default::default(),
                ai_update_attack_target: Default::default(),
                is_outside_game_screen: Default::default(),
                game_coord_conversion: Default::default(),
                fow_sprites: Default::default(),
                init_map_from_path: Default::default(),
                choose_snp: Default::default(),
                single_player_start: Default::default(),
                select_map_entry: Default::default(),
                load_images: Default::default(),
                images_loaded: Default::default(),
                local_player_name: Default::default(),
                step_network: Default::default(),
                init_game_network: Default::default(),
                snp_definitions: Default::default(),
                lobby_state: Default::default(),
                init_storm_networking: Default::default(),
                draw_cursor_marker: Default::default(),
                misc_clientside: Default::default(),
                spawn_dialog: Default::default(),
                unit_creation: Default::default(),
                fonts: Default::default(),
                init_sprites: Default::default(),
                sprite_serialization: Default::default(),
                limits: Default::default(),
                font_render: Default::default(),
                ttf_malloc: Default::default(),
                create_game_dialog_vtbl_on_multiplayer_create: Default::default(),
                tooltip_related: Default::default(),
                draw_graphic_layers: Default::default(),
                prism_shaders: Default::default(),
                ai_attack_prepare: Default::default(),
                ai_step_region: Default::default(),
                join_game: Default::default(),
                dat_patches: Default::default(),
                snet_initialize_provider: Default::default(),
                do_attack: Default::default(),
                button_ddsgrps: Default::default(),
                mouse_xy: Default::default(),
                status_screen_mode: Default::default(),
                check_unit_requirements: Default::default(),
                check_dat_requirements: Default::default(),
                cheat_flags: Default::default(),
                unit_strength: Default::default(),
                multi_wireframes: Default::default(),
                wirefram_ddsgrp: Default::default(),
                run_triggers: Default::default(),
                trigger_unit_count_caches: Default::default(),
                snet_handle_packets: Default::default(),
                chk_init_players: Default::default(),
                original_chk_player_types: Default::default(),
                give_ai: Default::default(),
                play_sound: Default::default(),
                ai_prepare_moving_to: Default::default(),
                ai_transport_reachability_cached_region: Default::default(),
                player_unit_skins: Default::default(),
                replay_minimap_unexplored_fog_patch: Default::default(),
                dat_tables: DatTables::new(),
            },
            binary,
            binary_sections: BinarySections {
                rdata: binary.section(b".rdata\0\0").unwrap(),
                data: binary.section(b".data\0\0\0").unwrap(),
                text: binary.section(b".text\0\0\0").unwrap(),
            },
            ctx,
            bump: Bump::new(),
            arg_cache: ArgCache::new(ctx),
        }
    }

    fn is_valid_function(address: E::VirtualAddress) -> bool {
        address.as_u64() & 0xf == 0
    }

    /// Entry point for any analysis calls.
    /// Creates AnalysisCtx from self that is used across actual analysis functions.
    fn enter<F: for<'b> FnOnce(&mut AnalysisCtx<'b, 'e, E>) -> R, R>(
        &mut self,
        func: F,
    ) -> R {
        let mut ctx = AnalysisCtx {
            cache: &mut self.cache,
            binary: self.binary,
            binary_sections: &self.binary_sections,
            ctx: self.ctx,
            arg_cache: &self.arg_cache,
            bump: &self.bump,
        };
        let ret = func(&mut ctx);
        self.bump.reset();
        ret
    }

    pub fn firegraft_addresses(&mut self) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        self.enter(|x| x.firegraft_addresses())
    }

    pub fn dat(&mut self, ty: DatType) -> Option<DatTablePtr<'e>> {
        self.enter(|x| x.dat(ty))
    }

    pub fn file_hook(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x| x.file_hook())
    }

    pub fn rng(&mut self) -> Rc<Rng<'e>> {
        self.enter(|x| x.rng())
    }

    pub fn step_objects(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.step_objects())
    }

    pub fn game(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.game())
    }

    pub fn aiscript_hook(&mut self) -> Rc<Option<AiScriptHook<'e, E::VirtualAddress>>> {
        self.enter(|x| x.aiscript_hook())
    }

    pub fn regions(&mut self) -> Rc<RegionRelated<'e, E::VirtualAddress>> {
        self.enter(|x| x.regions())
    }

    pub fn pathing(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.pathing())
    }

    pub fn active_hidden_units(&mut self) -> Rc<ActiveHiddenUnits<'e>> {
        self.enter(|x| x.active_hidden_units())
    }

    pub fn order_issuing(&mut self) -> Rc<OrderIssuing<E::VirtualAddress>> {
        self.enter(|x| x.order_issuing())
    }

    pub fn process_commands(&mut self) -> Rc<ProcessCommands<'e, E::VirtualAddress>> {
        self.enter(|x| x.process_commands())
    }

    pub fn command_user(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.command_user())
    }

    /// May return an overly long array
    pub fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        self.enter(|x| x.command_lengths())
    }

    pub fn selections(&mut self) -> Rc<Selections<'e>> {
        self.enter(|x| x.selections())
    }

    pub fn is_replay(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.is_replay())
    }

    pub fn process_lobby_commands(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.process_lobby_commands())
    }

    pub fn send_command(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.send_command())
    }

    pub fn print_text(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.print_text())
    }

    pub fn init_map_from_path(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_map_from_path())
    }

    pub fn choose_snp(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.choose_snp())
    }

    pub fn renderer_vtables(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x| x.renderer_vtables())
    }

    pub fn vtables(&mut self) -> Vec<E::VirtualAddress> {
        self.enter(|x| x.vtables())
    }

    pub fn vtables_for_class(&mut self, name: &[u8]) -> Vec<E::VirtualAddress> {
        self.enter(|x| x.vtables_for_class(name))
    }

    pub fn single_player_start(&mut self) -> Rc<SinglePlayerStart<'e, E::VirtualAddress>> {
        self.enter(|x| x.single_player_start())
    }

    pub fn local_player_id(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.local_player_id())
    }

    pub fn game_screen_rclick(&mut self) -> Rc<GameScreenRClick<'e, E::VirtualAddress>> {
        self.enter(|x| x.game_screen_rclick())
    }

    pub fn select_map_entry(&mut self) -> Rc<SelectMapEntry<'e, E::VirtualAddress>> {
        self.enter(|x| x.select_map_entry())
    }

    pub fn load_images(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.load_images())
    }

    pub fn images_loaded(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.images_loaded())
    }

    pub fn init_real_time_lighting(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_real_time_lighting())
    }

    pub fn local_player_name(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.local_player_name())
    }

    pub fn step_network(&mut self) -> Rc<StepNetwork<'e, E::VirtualAddress>> {
        self.enter(|x| x.step_network())
    }

    pub fn init_game_network(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_game_network())
    }

    pub fn snp_definitions(&mut self) -> Option<SnpDefinitions<'e>> {
        self.enter(|x| x.snp_definitions())
    }

    pub fn lobby_state(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.lobby_state())
    }

    pub fn init_storm_networking(&mut self) -> Rc<InitStormNetworking<E::VirtualAddress>> {
        self.enter(|x| x.init_storm_networking())
    }

    pub fn step_order(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.step_order())
    }

    pub fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x| x.step_order_hidden())
    }

    pub fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>>
    {
        self.enter(|x| x.step_secondary_order())
    }

    pub fn step_iscript(&mut self) -> Rc<StepIscript<'e, E::VirtualAddress>> {
        self.enter(|x| x.step_iscript())
    }

    pub fn add_overlay_iscript(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.add_overlay_iscript())
    }

    pub fn draw_cursor_marker(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.draw_cursor_marker())
    }

    pub fn play_smk(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.play_smk())
    }

    pub fn game_init(&mut self) -> Rc<GameInit<'e, E::VirtualAddress>> {
        self.enter(|x| x.game_init())
    }

    pub fn misc_clientside(&mut self) -> Rc<MiscClientSide<'e>> {
        self.enter(|x| x.misc_clientside())
    }

    pub fn init_units(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_units_related().init_units)
    }

    pub fn load_dat(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.load_dat())
    }

    pub fn units(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.units())
    }

    pub fn first_ai_script(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.first_ai_script())
    }

    pub fn first_guard_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.first_guard_ai())
    }

    pub fn player_ai_towns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.player_ai_towns())
    }

    pub fn player_ai(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.player_ai())
    }

    pub fn init_game(&mut self) -> Rc<InitGame<'e, E::VirtualAddress>> {
        self.enter(|x| x.init_game())
    }

    pub fn sprites(&mut self) -> Rc<Sprites<'e, E::VirtualAddress>> {
        self.enter(|x| x.sprites())
    }

    pub fn eud_table(&mut self) -> Rc<EudTable<'e>> {
        self.enter(|x| x.eud_table())
    }

    pub fn map_tile_flags(&mut self) -> Rc<MapTileFlags<'e, E::VirtualAddress>> {
        self.enter(|x| x.map_tile_flags())
    }

    pub fn players(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.players())
    }

    pub fn draw_image(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.draw_image())
    }

    pub fn bullet_creation(&mut self) -> Rc<BulletCreation<'e, E::VirtualAddress>> {
        self.enter(|x| x.bullet_creation())
    }

    pub fn net_players(&mut self) -> Rc<NetPlayers<'e, E::VirtualAddress>> {
        self.enter(|x| x.net_players())
    }

    pub fn campaigns(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.campaigns())
    }

    pub fn run_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.run_dialog())
    }

    pub fn ai_update_attack_target(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ai_update_attack_target())
    }

    pub fn is_outside_game_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.is_outside_game_screen())
    }

    pub fn game_coord_conversion(&mut self) -> Rc<GameCoordConversion<'e>> {
        self.enter(|x| x.game_coord_conversion())
    }

    pub fn fow_sprites(&mut self) -> Rc<FowSprites<'e>> {
        self.enter(|x| x.fow_sprites())
    }

    pub fn spawn_dialog(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.spawn_dialog())
    }

    pub fn unit_creation(&mut self) -> Rc<UnitCreation<E::VirtualAddress>> {
        self.enter(|x| x.unit_creation())
    }

    pub fn fonts(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.fonts())
    }

    pub fn init_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_sprites())
    }

    pub fn sprite_array(&mut self) -> Option<(Operand<'e>, u32)> {
        self.enter(|x| x.sprite_array())
    }

    pub fn serialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.serialize_sprites())
    }

    pub fn deserialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.deserialize_sprites())
    }

    pub fn limits(&mut self) -> Rc<Limits<'e, E::VirtualAddress>> {
        self.enter(|x| x.limits())
    }

    pub fn font_cache_render_ascii(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.font_cache_render_ascii())
    }

    pub fn ttf_cache_character(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ttf_cache_character())
    }

    pub fn ttf_render_sdf(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ttf_render_sdf())
    }

    /// Memory allocation function that at least TTF code uses.
    ///
    /// (Should be Win32 HeapAlloc with a specific heap)
    pub fn ttf_malloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ttf_malloc())
    }

    /// Offset to CreateGameScreen.OnMultiplayerGameCreate in the dialog's vtable
    pub fn create_game_dialog_vtbl_on_multiplayer_create(&mut self) -> Option<usize> {
        self.enter(|x| x.create_game_dialog_vtbl_on_multiplayer_create())
    }

    pub fn tooltip_draw_func(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.tooltip_draw_func())
    }

    pub fn current_tooltip_ctrl(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.current_tooltip_ctrl())
    }

    pub fn layout_draw_text(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.layout_draw_text())
    }

    pub fn graphic_layers(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.graphic_layers())
    }

    pub fn draw_f10_menu_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.draw_f10_menu_tooltip())
    }

    pub fn draw_tooltip_layer(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.draw_tooltip_layer())
    }

    pub fn draw_graphic_layers(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.draw_graphic_layers())
    }

    pub fn prism_vertex_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x| x.prism_vertex_shaders())
    }

    pub fn prism_pixel_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.enter(|x| x.prism_pixel_shaders())
    }

    pub fn ai_attack_prepare(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ai_attack_prepare())
    }

    pub fn ai_step_region(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ai_step_region())
    }

    pub fn join_game(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.join_game())
    }

    pub fn snet_initialize_provider(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.snet_initialize_provider())
    }

    pub fn set_status_screen_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.set_status_screen_tooltip())
    }

    pub fn dat_patches(&mut self) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        self.enter(|x| x.dat_patches())
    }

    pub fn do_attack(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.do_attack())
    }

    pub fn do_attack_main(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.do_attack_main())
    }

    pub fn last_bullet_spawner(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.last_bullet_spawner())
    }

    pub fn smem_alloc(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.smem_alloc())
    }

    pub fn smem_free(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.smem_free())
    }

    pub fn cmdicons_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.cmdicons_ddsgrp())
    }

    pub fn cmdbtns_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.cmdbtns_ddsgrp())
    }

    pub fn mouse_xy(&mut self) -> MouseXy<'e, E::VirtualAddress> {
        self.enter(|x| x.mouse_xy())
    }

    pub fn status_screen_mode(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.status_screen_mode())
    }

    pub fn check_unit_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.check_unit_requirements())
    }

    pub fn check_dat_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.check_dat_requirements())
    }

    pub fn dat_requirement_error(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.dat_requirement_error())
    }

    pub fn cheat_flags(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.cheat_flags())
    }

    pub fn unit_strength(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.unit_strength())
    }

    pub fn grpwire_grp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.grpwire_grp())
    }

    pub fn grpwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.grpwire_ddsgrp())
    }

    pub fn tranwire_grp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.tranwire_grp())
    }

    pub fn tranwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.tranwire_ddsgrp())
    }

    pub fn status_screen(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.status_screen())
    }

    pub fn status_screen_event_handler(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.status_screen_event_handler())
    }

    /// Note: Struct that contains { grp, sd_ddsgrp, hd_ddsgrp }
    pub fn wirefram_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.wirefram_ddsgrp())
    }

    pub fn init_status_screen(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.init_status_screen())
    }

    pub fn trigger_conditions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.trigger_conditions())
    }

    pub fn trigger_actions(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.trigger_actions())
    }

    pub fn trigger_completed_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.trigger_completed_units_cache())
    }

    pub fn trigger_all_units_cache(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.trigger_all_units_cache())
    }

    pub fn snet_send_packets(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.snet_send_packets())
    }

    pub fn snet_recv_packets(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.snet_recv_packets())
    }

    pub fn chk_init_players(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.chk_init_players())
    }

    pub fn original_chk_player_types(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.original_chk_player_types())
    }

    pub fn give_ai(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.give_ai())
    }

    pub fn play_sound(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.play_sound())
    }

    pub fn ai_prepare_moving_to(&mut self) -> Option<E::VirtualAddress> {
        self.enter(|x| x.ai_prepare_moving_to())
    }

    pub fn ai_transport_reachability_cached_region(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.ai_transport_reachability_cached_region())
    }

    pub fn player_unit_skins(&mut self) -> Option<Operand<'e>> {
        self.enter(|x| x.player_unit_skins())
    }

    /// A patch to show resource fog sprites on minimap in replays even if they're
    /// in unexplored fog.
    pub fn replay_minimap_unexplored_fog_patch(
        &mut self,
    ) -> Option<Rc<Patch<E::VirtualAddress>>> {
        self.enter(|x| x.replay_minimap_unexplored_fog_patch())
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

impl<'b, 'e, E: ExecutionStateTrait<'e>> AnalysisCtx<'b, 'e, E> {
    fn functions(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let binary = self.binary;
        let text = self.binary_sections.text;
        let relocs = self.relocs();
        self.cache.functions.get_or_insert_with(|| {
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
        let result = match self.cache.relocs_with_values.is_none() {
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
        self.cache.relocs_with_values.get_or_insert_with(|| {
            Rc::new(result)
        }).clone()
    }

    fn relocs(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let relocs = match self.cache.relocs.is_none() {
            true => match scarf::analysis::find_relocs::<E>(self.binary) {
                Ok(s) => s,
                Err(e) => {
                    debug!("Error getting relocs: {}", e);
                    Vec::new()
                }
            },
            false => Vec::new(),
        };
        self.cache.relocs.get_or_insert_with(|| {
            Rc::new(relocs)
        }).clone()
    }

    // TODO Should share search w/ self.functions
    fn functions_with_callers(&mut self) -> Rc<Vec<FuncCallPair<E::VirtualAddress>>> {
        let binary = self.binary;
        self.cache.functions_with_callers.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions_with_callers::<E>(binary);
            functions.retain(|fun| Analysis::<E>::is_valid_function(fun.callee));
            Rc::new(functions)
        }).clone()
    }

    fn firegraft_addresses(&mut self) -> Rc<FiregraftAddresses<E::VirtualAddress>> {
        if let Some(cached) = self.cache.firegraft_addresses.cached() {
            return cached;
        }
        let buttonsets = firegraft::find_buttonsets(self);
        let status_funcs = firegraft::find_unit_status_funcs(self);
        let reqs = firegraft::find_requirement_tables(self);
        let result = Rc::new(FiregraftAddresses {
            buttonsets,
            requirement_table_refs: reqs,
            unit_status_funcs: status_funcs,
        });
        self.cache.firegraft_addresses.cache(&result);
        result
    }

    // Sorted by switch address
    fn switch_tables(&mut self) -> Rc<Vec<SwitchTable<E::VirtualAddress>>> {
        let binary = self.binary;
        let text = self.binary_sections.text;
        let relocs = self.relocs();
        self.cache.switch_tables.get_or_insert_with(|| {
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
    ) -> Option<(E::VirtualAddress, u32)> {
        let dat = self.dat(ty);
        let result = dat.iter()
            .filter_map(|x| x.address.if_constant().map(|y| (y, x.entry_size)))
            .next()
            .map(|(addr, size)| (E::VirtualAddress::from_u64(addr), size));
        result
    }

    fn dat(&mut self, ty: DatType) -> Option<DatTablePtr<'e>> {
        let filename = {
            let (field, filename) = self.cache.dat_tables.field(ty);
            if let Some(ref f) = *field {
                return f.clone();
            }
            filename
        };
        let result = dat::dat_table(self, filename);
        let (field, _) = self.cache.dat_tables.field(ty);
        *field = Some(result.clone());
        result
    }

    fn file_hook(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.cache.open_file.cached() {
            return cached;
        }
        let result = Rc::new(file::open_file(self));
        self.cache.open_file.cache(&result);
        result
    }

    fn rng(&mut self) -> Rc<Rng<'e>> {
        if let Some(cached) = self.cache.rng.cached() {
            return cached;
        }
        let result = rng::rng(self);
        self.cache.rng.cache(&result);
        result
    }

    fn step_objects(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.step_objects.cached() {
            return cached;
        }
        let result = game::step_objects(self);
        self.cache.step_objects.cache(&result);
        result
    }

    fn game(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.game.cached() {
            return cached;
        }
        let result = game::game(self);
        self.cache.game.cache(&result);
        result
    }

    fn aiscript_hook(&mut self) -> Rc<Option<AiScriptHook<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.cache.aiscript_hook.cached() {
            return cached;
        }
        let result = Rc::new(ai::aiscript_hook(self));
        self.cache.aiscript_hook.cache(&result);
        result
    }

    fn regions(&mut self) -> Rc<RegionRelated<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.regions.cached() {
            return cached;
        }
        let result = pathing::regions(self);
        let result = Rc::new(result);
        self.cache.regions.cache(&result);
        result
    }

    fn pathing(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.pathing.cached() {
            return cached;
        }

        let result = pathing::pathing(self);
        self.cache.pathing.cache(&result);
        result
    }

    fn active_hidden_units(&mut self) -> Rc<ActiveHiddenUnits<'e>> {
        if let Some(cached) = self.cache.active_hidden_units.cached() {
            return cached;
        }
        let result = Rc::new(units::active_hidden_units(self));
        self.cache.active_hidden_units.cache(&result);
        result
    }

    fn order_issuing(&mut self) -> Rc<OrderIssuing<E::VirtualAddress>> {
        if let Some(cached) = self.cache.order_issuing.cached() {
            return cached;
        }

        let result = Rc::new(units::order_issuing(self));
        self.cache.order_issuing.cache(&result);
        result
    }

    fn process_commands(&mut self) -> Rc<ProcessCommands<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.process_commands.cached() {
            return cached;
        }
        let result = Rc::new(commands::process_commands(self));
        self.cache.process_commands.cache(&result);
        result
    }

    fn command_user(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.command_user.cached() {
            return cached;
        }

        let result = commands::command_user(self);
        self.cache.command_user.cache(&result);
        result
    }

    fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        if let Some(cached) = self.cache.command_lengths.cached() {
            return cached;
        }

        let result = commands::command_lengths(self);
        let result = Rc::new(result);
        self.cache.command_lengths.cache(&result);
        result
    }

    fn selections(&mut self) -> Rc<Selections<'e>> {
        if let Some(cached) = self.cache.selections.cached() {
            return cached;
        }

        let result = commands::selections(self);
        let result = Rc::new(result);
        self.cache.selections.cache(&result);
        result
    }

    fn is_replay(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.is_replay.cached() {
            return cached;
        }

        let result = commands::is_replay(self);
        self.cache.is_replay.cache(&result);
        result
    }

    fn process_lobby_commands_switch(&mut self) ->
        Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)>
    {
        if let Some(cached) = self.cache.process_lobby_commands.cached() {
            return cached;
        }
        let mut result = None;
        let switch_tables = self.switch_tables();
        let switches = switch_tables.iter().filter(|switch| {
            switch.cases.len() >= 0x10 && switch.cases.len() < 0x20
        });
        for switch in switches {
            let val = full_switch_info(self, switch)
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
        self.cache.process_lobby_commands.cache(&result);
        result
    }

    fn process_lobby_commands(&mut self) -> Option<E::VirtualAddress> {
        self.process_lobby_commands_switch().map(|x| x.1)
    }

    fn send_command(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.send_command.cached() {
            return cached;
        }
        let result = commands::send_command(self);
        self.cache.send_command.cache(&result);
        result
    }

    fn print_text(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.print_text.cached() {
            return cached;
        }
        let result = commands::print_text(self);
        self.cache.print_text.cache(&result);
        result
    }

    fn init_map_from_path_vars(&mut self) -> Option<InitMapFromPath<E::VirtualAddress>> {
        if let Some(cached) = self.cache.init_map_from_path.cached() {
            return cached;
        }
        let result = game_init::init_map_from_path(self);
        self.cache.init_map_from_path.cache(&result);
        result
    }

    fn init_map_from_path(&mut self) -> Option<E::VirtualAddress> {
        self.init_map_from_path_vars().map(|x| x.init_map_from_path)
    }

    fn choose_snp(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.choose_snp.cached() {
            return cached;
        }
        let result = game_init::choose_snp(self);
        self.cache.choose_snp.cache(&result);
        result
    }

    fn renderer_vtables(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.cache.renderer_vtables.cached() {
            return cached;
        }
        let result = Rc::new(renderer::renderer_vtables(self));
        self.cache.renderer_vtables.cache(&result);
        result
    }

    fn vtables(&mut self) -> Vec<E::VirtualAddress> {
        self.vtables_for_class(b".?AV")
    }

    fn vtables_for_class(&mut self, name: &[u8]) -> Vec<E::VirtualAddress> {
        let mut vtables = vtables::vtables(self, name);
        vtables.sort_unstable();
        vtables.dedup();
        vtables
    }

    fn single_player_start(&mut self) -> Rc<SinglePlayerStart<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.single_player_start.cached() {
            return cached;
        }
        let result = Rc::new(game_init::single_player_start(self));
        self.cache.single_player_start.cache(&result);
        result
    }

    fn local_player_id(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.local_player_id.cached() {
            return cached;
        }
        let result = players::local_player_id(self);
        self.cache.local_player_id.cache(&result);
        result
    }

    fn game_screen_rclick(&mut self) -> Rc<GameScreenRClick<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.game_screen_rclick.cached() {
            return cached;
        }

        let result = Rc::new(clientside::game_screen_rclick(self));
        self.cache.game_screen_rclick.cache(&result);
        result
    }

    fn select_map_entry(&mut self) -> Rc<SelectMapEntry<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.select_map_entry.cached() {
            return cached;
        }
        let result = Rc::new(game_init::select_map_entry(self));
        self.cache.select_map_entry.cache(&result);
        result
    }

    fn load_images(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.load_images.cached() {
            return cached;
        }
        let result = game_init::load_images(self);
        self.cache.load_images.cache(&result);
        result
    }

    fn images_loaded(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.images_loaded.cached() {
            return cached.images_loaded;
        }
        let result = game_init::images_loaded(self);
        self.cache.images_loaded.cache(&result);
        result.images_loaded
    }

    fn init_real_time_lighting(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.images_loaded.cached() {
            return cached.init_real_time_lighting;
        }
        let result = game_init::images_loaded(self);
        self.cache.images_loaded.cache(&result);
        result.init_real_time_lighting
    }

    fn local_player_name(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.local_player_name.cached() {
            return cached;
        }
        let result = game_init::local_player_name(self);
        self.cache.local_player_name.cache(&result);
        result
    }

    fn step_network(&mut self) -> Rc<StepNetwork<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.step_network.cached() {
            return cached;
        }
        let result = Rc::new(commands::step_network(self));
        self.cache.step_network.cache(&result);
        result
    }

    fn init_game_network(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.init_game_network.cached() {
            return cached;
        }
        let result = game_init::init_game_network(self);
        self.cache.init_game_network.cache(&result);
        result
    }

    fn snp_definitions(&mut self) -> Option<SnpDefinitions<'e>> {
        if let Some(cached) = self.cache.snp_definitions.cached() {
            return cached;
        }
        let result = network::snp_definitions(self);
        self.cache.snp_definitions.cache(&result);
        result
    }

    fn lobby_state(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.lobby_state.cached() {
            return cached;
        }
        let result = game_init::lobby_state(self);
        self.cache.lobby_state.cache(&result);
        result
    }

    fn init_storm_networking(&mut self) -> Rc<InitStormNetworking<E::VirtualAddress>> {
        if let Some(cached) = self.cache.init_storm_networking.cached() {
            return cached;
        }
        let result = Rc::new(network::init_storm_networking(self));
        self.cache.init_storm_networking.cache(&result);
        result
    }

    fn step_order(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.step_order.cached() {
            return cached;
        }
        let result = step_order::step_order(self);
        self.cache.step_order.cache(&result);
        result
    }

    fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<'e, E::VirtualAddress>>>
    {
        if let Some(cached) = self.cache.step_order_hidden.cached() {
            return cached;
        }
        let result = step_order::step_order_hidden(self);
        let result = Rc::new(result);
        self.cache.step_order_hidden.cache(&result);
        result
    }

    fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<'e, E::VirtualAddress>>>
    {
        if let Some(cached) = self.cache.step_secondary_order.cached() {
            return cached;
        }
        let result = step_order::step_secondary_order(self);
        let result = Rc::new(result);
        self.cache.step_secondary_order.cache(&result);
        result
    }

    fn step_iscript(&mut self) -> Rc<StepIscript<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.step_iscript.cached() {
            return cached;
        }
        let result = iscript::step_iscript(self);
        let result = Rc::new(result);
        self.cache.step_iscript.cache(&result);
        result
    }

    fn add_overlay_iscript(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.add_overlay_iscript.cached() {
            return cached;
        }
        let result = iscript::add_overlay_iscript(self);
        self.cache.add_overlay_iscript.cache(&result);
        result
    }

    fn draw_cursor_marker(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.draw_cursor_marker.cached() {
            return cached;
        }
        let result = iscript::draw_cursor_marker(self);
        self.cache.draw_cursor_marker.cache(&result);
        result
    }

    fn play_smk(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.play_smk.cached() {
            return cached;
        }
        let result = game_init::play_smk(self);
        self.cache.play_smk.cache(&result);
        result
    }

    fn game_init(&mut self) -> Rc<GameInit<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.game_init.cached() {
            return cached;
        }
        let result = game_init::game_init(self);
        let result = Rc::new(result);
        self.cache.game_init.cache(&result);
        result
    }

    fn misc_clientside(&mut self) -> Rc<MiscClientSide<'e>> {
        if let Some(cached) = self.cache.misc_clientside.cached() {
            return cached;
        }
        let result = clientside::misc_clientside(self);
        let result = Rc::new(result);
        self.cache.misc_clientside.cache(&result);
        result
    }

    fn init_units_related(&mut self) -> InitUnits<E::VirtualAddress> {
        if let Some(cached) = self.cache.init_units.cached() {
            return cached;
        }
        let result = units::init_units(self);
        self.cache.init_units.cache(&result);
        result
    }

    fn init_units(&mut self) -> Option<E::VirtualAddress> {
        self.init_units_related().init_units
    }

    fn load_dat(&mut self) -> Option<E::VirtualAddress> {
        self.init_units_related().load_dat
    }

    fn units(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.units.cached() {
            return cached;
        }

        let result = units::units(self);
        self.cache.units.cache(&result);
        result
    }

    fn first_ai_script(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.first_ai_script.cached() {
            return cached;
        }

        let result = ai::first_ai_script(self);
        self.cache.first_ai_script.cache(&result);
        result
    }

    fn first_guard_ai(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.first_guard_ai.cached() {
            return cached;
        }

        let result = ai::first_guard_ai(self);
        self.cache.first_guard_ai.cache(&result);
        result
    }

    fn player_ai_towns(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.player_ai_towns.cached() {
            return cached;
        }

        let result = ai::player_ai_towns(self);
        self.cache.player_ai_towns.cache(&result);
        result
    }

    fn player_ai(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.player_ai.cached() {
            return cached;
        }
        let result = ai::player_ai(self);
        self.cache.player_ai.cache(&result);
        result
    }

    fn init_game(&mut self) -> Rc<InitGame<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.init_game.cached() {
            return cached;
        }
        let result = Rc::new(game_init::init_game(self));
        self.cache.init_game.cache(&result);
        result
    }

    fn sprites(&mut self) -> Rc<Sprites<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.sprites.cached() {
            return cached;
        }
        let result = sprites::sprites(self);
        let result = Rc::new(result);
        self.cache.sprites.cache(&result);
        result
    }

    fn eud_table(&mut self) -> Rc<EudTable<'e>> {
        if let Some(cached) = self.cache.eud.cached() {
            return cached;
        }
        let result = eud::eud_table(self);
        let result = Rc::new(result);
        self.cache.eud.cache(&result);
        result
    }

    fn map_tile_flags(&mut self) -> Rc<MapTileFlags<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.map_tile_flags.cached() {
            return cached;
        }
        let result = Rc::new(map::map_tile_flags(self));
        self.cache.map_tile_flags.cache(&result);
        result
    }

    fn players(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.players.cached() {
            return cached;
        }
        let result = players::players(self);
        self.cache.players.cache(&result);
        result
    }

    fn draw_image(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.draw_image.cached() {
            return cached;
        }
        let result = renderer::draw_image(self);
        self.cache.draw_image.cache(&result);
        result
    }

    fn bullet_creation(&mut self) -> Rc<BulletCreation<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.bullet_creation.cached() {
            return cached;
        }
        let result = bullets::bullet_creation(self);
        let result = Rc::new(result);
        self.cache.bullet_creation.cache(&result);
        result
    }

    fn net_players(&mut self) -> Rc<NetPlayers<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.net_players.cached() {
            return cached;
        }
        let result = players::net_players(self);
        let result = Rc::new(result);
        self.cache.net_players.cache(&result);
        result
    }

    fn campaigns(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.campaigns.cached() {
            return cached;
        }
        let result = campaign::campaigns(self);
        self.cache.campaigns.cache(&result);
        result
    }

    fn run_dialog(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.run_dialog.cached() {
            return cached;
        }
        let result = dialog::run_dialog(self);
        self.cache.run_dialog.cache(&result);
        result
    }

    fn ai_update_attack_target(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.ai_update_attack_target.cached() {
            return cached;
        }
        let result = ai::ai_update_attack_target(self);
        self.cache.ai_update_attack_target.cache(&result);
        result
    }

    fn is_outside_game_screen(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.is_outside_game_screen.cached() {
            return cached;
        }
        let result = clientside::is_outside_game_screen(self);
        self.cache.is_outside_game_screen.cache(&result);
        result
    }

    fn game_coord_conversion(&mut self) -> Rc<GameCoordConversion<'e>> {
        if let Some(cached) = self.cache.game_coord_conversion.cached() {
            return cached;
        }
        let result = clientside::game_coord_conversion(self);
        let result = Rc::new(result);
        self.cache.game_coord_conversion.cache(&result);
        result
    }

    fn fow_sprites(&mut self) -> Rc<FowSprites<'e>> {
        if let Some(cached) = self.cache.fow_sprites.cached() {
            return cached;
        }
        let result = sprites::fow_sprites(self);
        let result = Rc::new(result);
        self.cache.fow_sprites.cache(&result);
        result
    }

    fn spawn_dialog(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.spawn_dialog.cached() {
            return cached;
        }
        let result = dialog::spawn_dialog(self);
        self.cache.spawn_dialog.cache(&result);
        result
    }

    fn unit_creation(&mut self) -> Rc<UnitCreation<E::VirtualAddress>> {
        if let Some(cached) = self.cache.unit_creation.cached() {
            return cached;
        }
        let result = Rc::new(units::unit_creation(self));
        self.cache.unit_creation.cache(&result);
        result
    }

    fn fonts(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.fonts.cached() {
            return cached;
        }
        let result = text::fonts(self);
        self.cache.fonts.cache(&result);
        result
    }

    fn init_sprites_etc(&mut self) -> InitSprites<'e, E::VirtualAddress> {
        if let Some(cached) = self.cache.init_sprites.cached() {
            return cached;
        }
        let result = sprites::init_sprites(self);
        self.cache.init_sprites.cache(&result);
        result
    }

    fn init_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.init_sprites_etc().init_sprites
    }

    fn sprite_array(&mut self) -> Option<(Operand<'e>, u32)> {
        self.init_sprites_etc().sprites
    }

    fn sprite_serialization(&mut self) -> SpriteSerialization<E::VirtualAddress> {
        if let Some(cached) = self.cache.sprite_serialization.cached() {
            return cached;
        }
        let result = save::sprite_serialization(self);
        self.cache.sprite_serialization.cache(&result);
        result
    }

    fn serialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.sprite_serialization().serialize_sprites
    }

    fn deserialize_sprites(&mut self) -> Option<E::VirtualAddress> {
        self.sprite_serialization().deserialize_sprites
    }

    fn limits(&mut self) -> Rc<Limits<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.limits.cached() {
            return cached;
        }
        let result = Rc::new(game::limits(self));
        self.cache.limits.cache(&result);
        result
    }

    fn font_render(&mut self) -> FontRender<E::VirtualAddress> {
        if let Some(cached) = self.cache.font_render.cached() {
            return cached;
        }
        let result = text::font_render(self);
        self.cache.font_render.cache(&result);
        result
    }

    fn font_cache_render_ascii(&mut self) -> Option<E::VirtualAddress> {
        self.font_render().font_cache_render_ascii
    }

    fn ttf_cache_character(&mut self) -> Option<E::VirtualAddress> {
        self.font_render().ttf_cache_character
    }

    fn ttf_render_sdf(&mut self) -> Option<E::VirtualAddress> {
        self.font_render().ttf_render_sdf
    }

    fn ttf_malloc(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.ttf_malloc.cached() {
            return cached;
        }
        let result = text::ttf_malloc(self);
        self.cache.ttf_malloc.cache(&result);
        result
    }

    fn create_game_dialog_vtbl_on_multiplayer_create(&mut self) -> Option<usize> {
        if let Some(cached) = self.cache.create_game_dialog_vtbl_on_multiplayer_create.cached() {
            return cached;
        }
        let result = game_init::create_game_dialog_vtbl_on_multiplayer_create(self);
        self.cache.create_game_dialog_vtbl_on_multiplayer_create.cache(&result);
        result
    }

    fn tooltip_related(&mut self) -> TooltipRelated<'e, E::VirtualAddress> {
        if let Some(cached) = self.cache.tooltip_related.cached() {
            return cached;
        }
        let result = dialog::tooltip_related(self);
        self.cache.tooltip_related.cache(&result);
        result
    }

    fn tooltip_draw_func(&mut self) -> Option<Operand<'e>> {
        self.tooltip_related().tooltip_draw_func
    }

    fn current_tooltip_ctrl(&mut self) -> Option<Operand<'e>> {
        self.tooltip_related().current_tooltip_ctrl
    }

    fn layout_draw_text(&mut self) -> Option<E::VirtualAddress> {
        self.tooltip_related().layout_draw_text
    }

    fn graphic_layers(&mut self) -> Option<Operand<'e>> {
        self.tooltip_related().graphic_layers
    }

    fn draw_f10_menu_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.tooltip_related().draw_f10_menu_tooltip
    }

    fn draw_tooltip_layer(&mut self) -> Option<E::VirtualAddress> {
        self.tooltip_related().draw_tooltip_layer
    }

    fn draw_graphic_layers(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.draw_graphic_layers.cached() {
            return cached;
        }
        let result = dialog::draw_graphic_layers(self);
        self.cache.draw_graphic_layers.cache(&result);
        result
    }

    fn prism_shaders(&mut self) -> PrismShaders<E::VirtualAddress> {
        if let Some(cached) = self.cache.prism_shaders.cached() {
            return cached;
        }
        let result = renderer::prism_shaders(self);
        self.cache.prism_shaders.cache(&result);
        result
    }

    fn prism_vertex_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders().vertex_shaders
    }

    fn prism_pixel_shaders(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        self.prism_shaders().pixel_shaders
    }

    fn ai_attack_prepare(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.ai_attack_prepare.cached() {
            return cached;
        }
        let result = ai::attack_prepare(self);
        self.cache.ai_attack_prepare.cache(&result);
        result
    }

    fn ai_step_region(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.ai_step_region.cached() {
            return cached;
        }
        let result = ai::step_region(self);
        self.cache.ai_step_region.cache(&result);
        result
    }

    fn join_game(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.join_game.cached() {
            return cached;
        }
        let result = game_init::join_game(self);
        self.cache.join_game.cache(&result);
        result
    }

    fn snet_initialize_provider(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.snet_initialize_provider.cached() {
            return cached;
        }
        let result = game_init::snet_initialize_provider(self);
        self.cache.snet_initialize_provider.cache(&result);
        result
    }

    fn set_status_screen_tooltip(&mut self) -> Option<E::VirtualAddress> {
        self.dat_patches()?.set_status_screen_tooltip
    }

    fn dat_patches(&mut self) -> Option<Rc<DatPatches<'e, E::VirtualAddress>>> {
        if let Some(cached) = self.cache.dat_patches.cached() {
            return cached;
        }
        let result = dat::dat_patches(self).map(|x| Rc::new(x));
        self.cache.dat_patches.cache(&result);
        result

    }

    fn do_attack_struct(&mut self) -> Option<step_order::DoAttack<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.do_attack.cached() {
            return cached;
        }
        let result = step_order::do_attack(self);
        self.cache.do_attack.cache(&result);
        result
    }

    fn do_attack(&mut self) -> Option<E::VirtualAddress> {
        self.do_attack_struct().map(|x| x.do_attack)
    }

    fn do_attack_main(&mut self) -> Option<E::VirtualAddress> {
        self.do_attack_struct().map(|x| x.do_attack_main)
    }

    fn last_bullet_spawner(&mut self) -> Option<Operand<'e>> {
        self.do_attack_struct().map(|x| x.last_bullet_spawner)
    }

    fn smem_alloc(&mut self) -> Option<E::VirtualAddress> {
        self.limits().smem_alloc
    }

    fn smem_free(&mut self) -> Option<E::VirtualAddress> {
        self.limits().smem_free
    }

    fn button_ddsgrps(&mut self) -> dialog::ButtonDdsgrps<'e> {
        if let Some(cached) = self.cache.button_ddsgrps.cached() {
            return cached;
        }
        let result = dialog::button_ddsgrps(self);
        self.cache.button_ddsgrps.cache(&result);
        result
    }

    fn cmdicons_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.button_ddsgrps().cmdicons
    }

    fn cmdbtns_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.button_ddsgrps().cmdbtns
    }

    fn mouse_xy(&mut self) -> MouseXy<'e, E::VirtualAddress> {
        if let Some(cached) = self.cache.mouse_xy.cached() {
            return cached;
        }
        let result = dialog::mouse_xy(self);
        self.cache.mouse_xy.cache(&result);
        result
    }

    fn status_screen_mode(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.status_screen_mode.cached() {
            return cached;
        }
        let result = dialog::status_screen_mode(self);
        self.cache.status_screen_mode.cache(&result);
        result
    }

    fn check_unit_reqs_struct(
        &mut self,
    ) -> Option<requirements::CheckUnitRequirements<'e, E::VirtualAddress>> {
        if let Some(cached) = self.cache.check_unit_requirements.cached() {
            return cached;
        }
        let result = requirements::check_unit_requirements(self);
        self.cache.check_unit_requirements.cache(&result);
        result
    }

    fn check_unit_requirements(&mut self) -> Option<E::VirtualAddress> {
        self.check_unit_reqs_struct().map(|x| x.check_unit_requirements)
    }

    fn check_dat_requirements(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.check_dat_requirements.cached() {
            return cached;
        }
        let result = requirements::check_dat_requirements(self);
        self.cache.check_dat_requirements.cache(&result);
        result
    }

    fn dat_requirement_error(&mut self) -> Option<Operand<'e>> {
        self.check_unit_reqs_struct().map(|x| x.requirement_error)
    }

    fn cheat_flags(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.cheat_flags.cached() {
            return cached;
        }
        let result = requirements::cheat_flags(self);
        self.cache.cheat_flags.cache(&result);
        result
    }

    fn unit_strength(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.unit_strength.cached() {
            return cached;
        }
        let result = units::strength(self);
        self.cache.unit_strength.cache(&result);
        result
    }

    /// Smaller size wireframes, that is multiselection and transport
    /// (Fits multiple in status screen)
    /// Also relevant mostly for SD, HD always uses wirefram.ddsgrp for the drawing.
    fn multi_wireframes(&mut self) -> MultiWireframes<'e, E::VirtualAddress> {
        if let Some(cached) = self.cache.multi_wireframes.cached() {
            return cached;
        }
        let result = dialog::multi_wireframes(self);
        self.cache.multi_wireframes.cache(&result);
        result
    }

    fn grpwire_grp(&mut self) -> Option<Operand<'e>> {
        self.multi_wireframes().grpwire_grp
    }

    fn grpwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.multi_wireframes().grpwire_ddsgrp
    }

    fn tranwire_grp(&mut self) -> Option<Operand<'e>> {
        self.multi_wireframes().tranwire_grp
    }

    fn tranwire_ddsgrp(&mut self) -> Option<Operand<'e>> {
        self.multi_wireframes().tranwire_ddsgrp
    }

    fn status_screen(&mut self) -> Option<Operand<'e>> {
        self.multi_wireframes().status_screen
    }

    fn status_screen_event_handler(&mut self) -> Option<E::VirtualAddress> {
        self.multi_wireframes().status_screen_event_handler
    }

    fn wirefram_ddsgrp(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.wirefram_ddsgrp.cached() {
            return cached;
        }
        let result = dialog::wirefram_ddsgrp(self);
        self.cache.wirefram_ddsgrp.cache(&result);
        result
    }

    fn init_status_screen(&mut self) -> Option<E::VirtualAddress> {
        self.multi_wireframes().init_status_screen
    }

    fn run_triggers(&mut self) -> RunTriggers<E::VirtualAddress> {
        if let Some(cached) = self.cache.run_triggers.cached() {
            return cached;
        }
        let result = map::run_triggers(self);
        self.cache.run_triggers.cache(&result);
        result
    }

    fn trigger_conditions(&mut self) -> Option<E::VirtualAddress> {
        self.run_triggers().conditions
    }

    fn trigger_actions(&mut self) -> Option<E::VirtualAddress> {
        self.run_triggers().actions
    }

    fn trigger_unit_count_caches(&mut self) -> TriggerUnitCountCaches<'e> {
        if let Some(cached) = self.cache.trigger_unit_count_caches.cached() {
            return cached;
        }
        let result = map::trigger_unit_count_caches(self);
        self.cache.trigger_unit_count_caches.cache(&result);
        result
    }

    fn trigger_completed_units_cache(&mut self) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches().completed_units
    }

    fn trigger_all_units_cache(&mut self) -> Option<Operand<'e>> {
        self.trigger_unit_count_caches().all_units
    }

    fn snet_handle_packets(&mut self) -> SnetHandlePackets<E::VirtualAddress> {
        if let Some(cached) = self.cache.snet_handle_packets.cached() {
            return cached;
        }
        let result = network::snet_handle_packets(self);
        self.cache.snet_handle_packets.cache(&result);
        result
    }

    fn snet_send_packets(&mut self) -> Option<E::VirtualAddress> {
        self.snet_handle_packets().send_packets
    }

    fn snet_recv_packets(&mut self) -> Option<E::VirtualAddress> {
        self.snet_handle_packets().recv_packets
    }

    fn chk_init_players(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.chk_init_players.cached() {
            return cached;
        }
        let result = game_init::chk_init_players(self);
        self.cache.chk_init_players.cache(&result);
        result
    }

    fn original_chk_player_types(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.original_chk_player_types.cached() {
            return cached;
        }
        let result = game_init::original_chk_player_types(self);
        self.cache.original_chk_player_types.cache(&result);
        result
    }

    fn give_ai(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.give_ai.cached() {
            return cached;
        }
        let result = ai::give_ai(self);
        self.cache.give_ai.cache(&result);
        result
    }

    fn play_sound(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.play_sound.cached() {
            return cached;
        }
        let result = sound::play_sound(self);
        self.cache.play_sound.cache(&result);
        result
    }

    fn ai_prepare_moving_to(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.cache.ai_prepare_moving_to.cached() {
            return cached;
        }
        let result = ai::ai_prepare_moving_to(self);
        self.cache.ai_prepare_moving_to.cache(&result);
        result
    }

    fn ai_transport_reachability_cached_region(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.ai_transport_reachability_cached_region.cached() {
            return cached;
        }
        let result = ai::ai_transport_reachability_cached_region(self);
        self.cache.ai_transport_reachability_cached_region.cache(&result);
        result
    }

    fn player_unit_skins(&mut self) -> Option<Operand<'e>> {
        if let Some(cached) = self.cache.player_unit_skins.cached() {
            return cached;
        }
        let result = renderer::player_unit_skins(self);
        self.cache.player_unit_skins.cache(&result);
        result
    }

    fn replay_minimap_unexplored_fog_patch(&mut self) -> Option<Rc<Patch<E::VirtualAddress>>> {
        if let Some(cached) = self.cache.replay_minimap_unexplored_fog_patch.cached() {
            return cached;
        }
        let result = minimap::unexplored_fog_minimap_patch(self)
            .map(|x| Rc::new(x));
        self.cache.replay_minimap_unexplored_fog_patch.cache(&result);
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

fn string_refs<'acx, 'e, E: ExecutionStateTrait<'e>>(
    cache: &mut AnalysisCtx<'acx, 'e, E>,
    string: &[u8],
) -> BumpVec<'acx, StringRefs<E::VirtualAddress>> {
    let rdata = cache.binary_sections.rdata;
    let bump = cache.bump;
    let str_ref_addrs = find_strings_casei(bump, &rdata.data, string);
    // (Use rva, string rva)
    let rdata_base = rdata.virtual_address;
    let result = str_ref_addrs
        .into_iter()
        .flat_map(|str_rva| {
            let addr = rdata_base + str_rva.0;
            let ptr_refs = find_functions_using_global(cache, addr);
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

fn find_callers<'acx, 'exec, E: ExecutionStateTrait<'exec>>(
    cache: &mut AnalysisCtx<'acx, 'exec, E>,
    func_entry: E::VirtualAddress,
) -> BumpVec<'acx, E::VirtualAddress> {
    use std::cmp::Ordering;
    let callers = cache.functions_with_callers();
    let lower_bound = callers.binary_search_by(|x| match x.callee >= func_entry {
        true => Ordering::Greater,
        false => Ordering::Less,
    }).unwrap_err();
    let result = (&callers[lower_bound..]).iter()
        .take_while(|&x| x.callee == func_entry)
        .map(|x| x.caller);
    BumpVec::from_iter_in(result, cache.bump)
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

fn find_functions_using_global<'acx, 'exec, E: ExecutionStateTrait<'exec>>(
    cache: &mut AnalysisCtx<'acx, 'exec, E>,
    addr: E::VirtualAddress,
) -> BumpVec<'acx, GlobalRefs<E::VirtualAddress>> {
    use std::cmp::Ordering;

    let relocs = cache.relocs_with_values();
    let functions = cache.functions();
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
    BumpVec::from_iter_in(result, cache.bump)
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
