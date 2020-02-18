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

mod ai;
mod bullets;
mod campaign;
mod clientside;
mod commands;
mod dat;
mod dialog;
mod eud;
mod file;
mod firegraft;
mod game;
mod game_init;
mod iscript;
mod map;
mod network;
mod pathing;
mod players;
mod renderer;
mod rng;
mod step_order;
mod sprites;
mod switch;
mod units;
mod vtables;

use std::rc::Rc;

use byteorder::{ReadBytesExt, LE};
use quick_error::quick_error;

use scarf::{DestOperand, Operand, OperandType, Operation, Rva};
use scarf::analysis::{self, Control, FuncCallPair, RelocValues};
use scarf::exec_state::{InternMap};
use scarf::operand::{MemAccessSize, OperandContext};

pub use scarf;
pub use scarf::{BinarySection, VirtualAddress};
pub use crate::ai::AiScriptHook;
pub use crate::bullets::BulletCreation;
pub use crate::clientside::{GameScreenRClick, GameCoordConversion, MiscClientSide};
pub use crate::commands::{ProcessCommands, Selections, StepNetwork};
pub use crate::dat::{DatTablePtr};
pub use crate::eud::EudTable;
pub use crate::firegraft::RequirementTables;
pub use crate::game_init::{GameInit, SinglePlayerStart, SelectMapEntry};
pub use crate::iscript::StepIscript;
pub use crate::network::{InitStormNetworking, SnpDefinitions};
pub use crate::pathing::RegionRelated;
pub use crate::players::NetPlayers;
pub use crate::rng::Rng;
pub use crate::step_order::{SecondaryOrderHook, StepOrderHiddenHook};
pub use crate::sprites::{FowSprites, Sprites};
pub use crate::units::{ActiveHiddenUnits, OrderIssuing};

use crate::switch::{CompleteSwitch, full_switch_info};

use scarf::exec_state::ExecutionState as ExecutionStateTrait;
use scarf::ExecutionStateX86;
use scarf::ExecutionStateX86 as ExecutionState;
type BinaryFile = scarf::BinaryFile<VirtualAddress>;
type FuncAnalysis<'a, T> = analysis::FuncAnalysis<'a, ExecutionState<'a>, T>;
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

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Scarf(addr: VirtualAddress, e: scarf::analysis::Error) {
            display("Scarf {:08x}: {}", addr.0, e)
        }
        Scarf2(e: scarf::Error) {
            display("Scarf: {}", e)
            from()
        }
    }
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

pub struct Analysis<'a, E: ExecutionStateTrait<'a>> {
    relocs: Cached<Rc<Vec<E::VirtualAddress>>>,
    relocs_with_values: Cached<Rc<Vec<RelocValues<E::VirtualAddress>>>>,
    functions: Cached<Rc<Vec<E::VirtualAddress>>>,
    functions_with_callers: Cached<Rc<Vec<FuncCallPair<E::VirtualAddress>>>>,
    switch_tables: Cached<Rc<Vec<SwitchTable<E::VirtualAddress>>>>,
    open_file: Cached<Rc<Vec<E::VirtualAddress>>>,
    aiscript_hook: Cached<Rc<Option<AiScriptHook<E::VirtualAddress>>>>,
    game: Cached<Option<Rc<Operand>>>,
    rng: Cached<Rc<Rng>>,
    step_objects: Cached<Option<E::VirtualAddress>>,
    player_ai: Cached<Option<Rc<Operand>>>,
    regions: Cached<Rc<RegionRelated<E::VirtualAddress>>>,
    pathing: Cached<Option<Rc<Operand>>>,
    active_hidden_units: Cached<Rc<ActiveHiddenUnits>>,
    order_issuing: Cached<Rc<OrderIssuing<E::VirtualAddress>>>,
    process_commands: Cached<Rc<ProcessCommands<E::VirtualAddress>>>,
    command_lengths: Cached<Rc<Vec<u32>>>,
    command_user: Cached<Option<Rc<Operand>>>,
    selections: Cached<Rc<Selections>>,
    is_replay: Cached<Option<Rc<Operand>>>,
    process_lobby_commands: Cached<Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)>>,
    send_command: Cached<Option<E::VirtualAddress>>,
    print_text: Cached<Option<E::VirtualAddress>>,
    step_order: Cached<Option<E::VirtualAddress>>,
    step_order_hidden: Cached<Rc<Vec<step_order::StepOrderHiddenHook<E::VirtualAddress>>>>,
    init_units: Cached<Option<E::VirtualAddress>>,
    step_secondary_order: Cached<Rc<Vec<step_order::SecondaryOrderHook<E::VirtualAddress>>>>,
    init_game: Cached<Rc<InitGame>>,
    units: Cached<Option<Rc<Operand>>>,
    game_screen_rclick: Cached<Rc<GameScreenRClick<E::VirtualAddress>>>,
    first_ai_script: Cached<Option<Rc<Operand>>>,
    first_guard_ai: Cached<Option<Rc<Operand>>>,
    player_ai_towns: Cached<Option<Rc<Operand>>>,
    step_iscript: Cached<Rc<StepIscript<E::VirtualAddress>>>,
    sprites: Cached<Rc<Sprites>>,
    eud: Cached<Rc<EudTable>>,
    map_tile_flags: Cached<Rc<map::MapTileFlags>>,
    players: Cached<Option<Rc<Operand>>>,
    draw_image: Cached<Option<E::VirtualAddress>>,
    renderer_vtables: Cached<Rc<Vec<E::VirtualAddress>>>,
    local_player_id: Cached<Option<Rc<Operand>>>,
    bullet_creation: Cached<Rc<BulletCreation>>,
    net_players: Cached<Rc<NetPlayers>>,
    play_smk: Cached<Option<E::VirtualAddress>>,
    game_init: Cached<Rc<GameInit<E::VirtualAddress>>>,
    add_overlay_iscript: Cached<Option<E::VirtualAddress>>,
    campaigns: Cached<Option<Rc<Operand>>>,
    run_dialog: Cached<Option<E::VirtualAddress>>,
    ai_update_attack_target: Cached<Option<E::VirtualAddress>>,
    is_outside_game_screen: Cached<Option<E::VirtualAddress>>,
    game_coord_conversion: Cached<Rc<GameCoordConversion>>,
    fow_sprites: Cached<Rc<FowSprites>>,
    init_map_from_path: Cached<Option<E::VirtualAddress>>,
    choose_snp: Cached<Option<E::VirtualAddress>>,
    single_player_start: Cached<Rc<SinglePlayerStart<E::VirtualAddress>>>,
    select_map_entry: Cached<Rc<SelectMapEntry<E::VirtualAddress>>>,
    load_images: Cached<Option<E::VirtualAddress>>,
    images_loaded: Cached<Option<Rc<Operand>>>,
    local_player_name: Cached<Option<Rc<Operand>>>,
    step_network: Cached<Rc<StepNetwork<E::VirtualAddress>>>,
    init_game_network: Cached<Option<E::VirtualAddress>>,
    snp_definitions: Cached<Option<SnpDefinitions>>,
    lobby_state: Cached<Option<Rc<Operand>>>,
    init_storm_networking: Cached<Rc<InitStormNetworking<E::VirtualAddress>>>,
    draw_cursor_marker: Cached<Option<Rc<Operand>>>,
    misc_clientside: Cached<Rc<MiscClientSide>>,
    dat_tables: DatTables,
    binary: &'a scarf::BinaryFile<E::VirtualAddress>,
    ctx: &'a scarf::OperandContext,
    arg_cache: ArgCache<'a, E>,
}

struct ArgCache<'e, E: ExecutionStateTrait<'e>> {
    args: Vec<Rc<Operand>>,
    ctx: &'e scarf::OperandContext,
    phantom: std::marker::PhantomData<E>,
}

impl<'e, E: ExecutionStateTrait<'e>> ArgCache<'e, E> {
    fn new(ctx: &'e OperandContext) -> ArgCache<'e, E> {
        use scarf::operand_helpers::*;

        let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
        let stack_pointer = ctx.register(4);
        let args = (0..8).map(|i| {
            if is_x64 {
                match i {
                    0 => ctx.register(1),
                    1 => ctx.register(2),
                    2 => ctx.register(8),
                    3 => ctx.register(9),
                    _ => Operand::simplified(
                        mem64(operand_add(
                            stack_pointer.clone(),
                            ctx.constant(i * 8),
                        )),
                    ),
                }
            } else {
                Operand::simplified(
                    mem32(operand_add(
                        stack_pointer.clone(),
                        ctx.constant(i * 4),
                    )),
                )
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
    pub fn on_call(&self, index: u8) -> Rc<Operand> {
        use scarf::operand_helpers::*;

        if (index as usize) < self.args.len() {
            self.args[index as usize].clone()
        } else {
            let size = <E::VirtualAddress as VirtualAddressTrait>::SIZE as u64;
            let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
            let stack_pointer = self.ctx.register(4);
            let mem_size = match is_x64 {
                true => MemAccessSize::Mem64,
                false => MemAccessSize::Mem32,
            };
            Operand::simplified(
                mem_variable_rc(mem_size, operand_add(
                    stack_pointer.clone(),
                    self.ctx.constant(index as u64 * size),
                )),
            )
        }
    }

    /// Returns operand corresponding to location of argument *on function entry*.
    pub fn on_entry(&self, index: u8) -> Rc<Operand> {
        use scarf::operand_helpers::*;

        let is_x64 = <E::VirtualAddress as VirtualAddressTrait>::SIZE == 8;
        let stack_pointer = self.ctx.register(4);
        if !is_x64 {
            if index as usize + 1 < self.args.len() {
                self.args[index as usize + 1].clone()
            } else {
                Operand::simplified(
                    mem32(operand_add(
                        stack_pointer.clone(),
                        self.ctx.constant((index as u64 + 1) * 4),
                    )),
                )
            }
        } else {
            if index < 4 {
                self.args[index as usize].clone()
            } else {
                Operand::simplified(
                    mem64(operand_add(
                        stack_pointer.clone(),
                        self.ctx.constant((index as u64 + 1) * 8),
                    )),
                )
            }
        }
    }
}

macro_rules! declare_dat {
    ($($struct_field:ident, $filename:expr, $enum_variant:ident,)*) => {
        struct DatTables {
            $($struct_field: Option<Option<DatTablePtr>>,)*
        }

        impl DatTables {
            fn new() -> DatTables {
                DatTables {
                    $($struct_field: None,)*
                }
            }

            fn field(&mut self, field: DatType) ->
                (&mut Option<Option<DatTablePtr>>, &'static str)
            {
                match field {
                    $(DatType::$enum_variant =>
                      (&mut self.$struct_field, concat!("arr\\", $filename)),)*
                }
            }
        }

        #[derive(Copy, Clone, Debug)]
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

#[derive(Clone, Debug)]
pub struct InitGame {
    pub loaded_save: Option<Rc<Operand>>,
    pub init_game: Option<VirtualAddress>,
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

impl<'a, E: ExecutionStateTrait<'a>> Analysis<'a, E> {
    pub fn new(
        binary: &'a scarf::BinaryFile<E::VirtualAddress>,
        ctx: &'a scarf::OperandContext,
    ) -> Analysis<'a, E> {
        Analysis {
            relocs: Default::default(),
            relocs_with_values: Default::default(),
            functions: Default::default(),
            functions_with_callers: Default::default(),
            switch_tables: Default::default(),
            open_file: Default::default(),
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
            dat_tables: DatTables::new(),
            binary,
            ctx,
            arg_cache: ArgCache::new(ctx),
        }
    }
}

impl<'a, E: ExecutionStateTrait<'a>> Analysis<'a, E> {
    fn is_valid_function(address: E::VirtualAddress) -> bool {
        address.as_u64() & 0xf == 0
    }

    fn functions(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let binary = self.binary;
        let relocs = self.relocs();
        self.functions.get_or_insert_with(|| {
            let mut functions = scarf::analysis::find_functions::<E>(binary, &relocs);
            functions.retain(|&fun| Analysis::<E>::is_valid_function(fun));
            Rc::new(functions)
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

    fn relocs(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        let relocs = match self.relocs.is_none() {
            true => match scarf::analysis::find_relocs::<E>(&self.binary) {
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

    fn relocs_with_values(&mut self) -> Rc<Vec<RelocValues<E::VirtualAddress>>> {
        let result = match self.relocs_with_values.is_none() {
            true => {
                let relocs = self.relocs();
                match scarf::analysis::relocs_with_values(&self.binary, &relocs) {
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

    pub fn firegraft_addresses(&mut self) -> FiregraftAddresses<E::VirtualAddress> {
        let buttonsets = firegraft::find_buttonsets(&self.binary);
        let status_funcs = firegraft::find_unit_status_funcs(&self.binary, self);
        let reqs = firegraft::find_requirement_tables(self);
        FiregraftAddresses {
            buttonsets,
            requirement_table_refs: reqs,
            unit_status_funcs: status_funcs,
        }
    }

    // Sorted by switch address
    fn switch_tables(&mut self) -> Rc<Vec<SwitchTable<E::VirtualAddress>>> {
        let binary = self.binary;
        let relocs = self.relocs();
        self.switch_tables.get_or_insert_with(|| {
            let text = binary.section(b".text\0\0\0").unwrap();
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
            result.sort_by_key(|x| x.address);
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

    pub fn dat(&mut self, ty: DatType) -> Option<DatTablePtr> {
        let filename = {
            let (field, filename) = self.dat_tables.field(ty);
            if let Some(ref f) = *field {
                return f.clone();
            }
            filename
        };
        let result = dat::dat_table(self, filename);
        let (field, _) = self.dat_tables.field(ty);
        *field = Some(result.clone());
        result
    }

    pub fn file_hook(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.open_file.cached() {
            return cached;
        }
        let result = Rc::new(file::open_file(self));
        self.open_file.cache(&result);
        result
    }

    pub fn rng(&mut self) -> Rc<Rng> {
        if let Some(cached) = self.rng.cached() {
            return cached;
        }
        let result = rng::rng(self);
        self.rng.cache(&result);
        result
    }

    pub fn step_objects(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.step_objects.cached() {
            return cached;
        }
        let result = game::step_objects(self);
        self.step_objects.cache(&result);
        result
    }

    pub fn game(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.game.cached() {
            return cached;
        }
        let result = game::game(self);
        self.game.cache(&result);
        result
    }

    pub fn aiscript_hook(&mut self) -> Rc<Option<AiScriptHook<E::VirtualAddress>>> {
        if let Some(cached) = self.aiscript_hook.cached() {
            return cached;
        }
        let result = Rc::new(ai::aiscript_hook(self));
        self.aiscript_hook.cache(&result);
        result
    }

    pub fn regions(&mut self) -> Rc<RegionRelated<E::VirtualAddress>> {
        if let Some(cached) = self.regions.cached() {
            return cached;
        }
        let result = pathing::regions(self);
        let result = Rc::new(result);
        self.regions.cache(&result);
        result
    }

    pub fn pathing(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.pathing.cached() {
            return cached;
        }

        let result = pathing::pathing(self);
        self.pathing.cache(&result);
        result
    }

    pub fn active_hidden_units(&mut self) -> Rc<ActiveHiddenUnits> {
        if let Some(cached) = self.active_hidden_units.cached() {
            return cached;
        }
        let result = Rc::new(units::active_hidden_units(self));
        self.active_hidden_units.cache(&result);
        result
    }

    pub fn order_issuing(&mut self) -> Rc<OrderIssuing<E::VirtualAddress>> {
        if let Some(cached) = self.order_issuing.cached() {
            return cached;
        }

        let result = Rc::new(units::order_issuing(self));
        self.order_issuing.cache(&result);
        result
    }

    pub fn process_commands(&mut self) -> Rc<ProcessCommands<E::VirtualAddress>> {
        if let Some(cached) = self.process_commands.cached() {
            return cached;
        }
        let result = Rc::new(commands::process_commands(self));
        self.process_commands.cache(&result);
        result
    }

    pub fn command_user(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.command_user.cached() {
            return cached;
        }

        let result = commands::command_user(self);
        self.command_user.cache(&result);
        result
    }

    // May return an overly long array
    pub fn command_lengths(&mut self) -> Rc<Vec<u32>> {
        if let Some(cached) = self.command_lengths.cached() {
            return cached;
        }

        let result = commands::command_lengths(self);
        let result = Rc::new(result);
        self.command_lengths.cache(&result);
        result
    }

    pub fn selections(&mut self) -> Rc<Selections> {
        if let Some(cached) = self.selections.cached() {
            return cached;
        }

        let result = commands::selections(self);
        let result = Rc::new(result);
        self.selections.cache(&result);
        result
    }

    pub fn is_replay(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.is_replay.cached() {
            return cached;
        }

        let result = commands::is_replay(self);
        self.is_replay.cache(&result);
        result
    }

    fn process_lobby_commands_switch(&mut self) ->
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
        self.process_lobby_commands.cache(&result);
        result
    }

    pub fn process_lobby_commands(&mut self) -> Option<E::VirtualAddress> {
        self.process_lobby_commands_switch().map(|x| x.1)
    }

    pub fn send_command(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.send_command.cached() {
            return cached;
        }
        let result = commands::send_command(self);
        self.send_command.cache(&result);
        result
    }

    pub fn print_text(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.print_text.cached() {
            return cached;
        }
        let result = commands::print_text(self);
        self.print_text.cache(&result);
        result
    }

    pub fn init_map_from_path(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.init_map_from_path.cached() {
            return cached;
        }
        let result = game_init::init_map_from_path(self);
        self.init_map_from_path.cache(&result);
        result
    }

    pub fn choose_snp(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.choose_snp.cached() {
            return cached;
        }
        let result = game_init::choose_snp(self);
        self.choose_snp.cache(&result);
        result
    }

    pub fn renderer_vtables(&mut self) -> Rc<Vec<E::VirtualAddress>> {
        if let Some(cached) = self.renderer_vtables.cached() {
            return cached;
        }
        let result = Rc::new(renderer::renderer_vtables(self));
        self.renderer_vtables.cache(&result);
        result
    }

    pub fn single_player_start(&mut self) -> Rc<SinglePlayerStart<E::VirtualAddress>> {
        if let Some(cached) = self.single_player_start.cached() {
            return cached;
        }
        let result = Rc::new(game_init::single_player_start(self));
        self.single_player_start.cache(&result);
        result
    }

    pub fn local_player_id(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.local_player_id.cached() {
            return cached;
        }
        let result = players::local_player_id(self);
        self.local_player_id.cache(&result);
        result
    }

    pub fn game_screen_rclick(&mut self) -> Rc<GameScreenRClick<E::VirtualAddress>> {
        if let Some(cached) = self.game_screen_rclick.cached() {
            return cached;
        }

        let result = Rc::new(clientside::game_screen_rclick(self));
        self.game_screen_rclick.cache(&result);
        result
    }

    pub fn select_map_entry(&mut self) -> Rc<SelectMapEntry<E::VirtualAddress>> {
        if let Some(cached) = self.select_map_entry.cached() {
            return cached;
        }
        let result = Rc::new(game_init::select_map_entry(self));
        self.select_map_entry.cache(&result);
        result
    }

    pub fn load_images(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.load_images.cached() {
            return cached;
        }
        let result = game_init::load_images(self);
        self.load_images.cache(&result);
        result
    }

    pub fn images_loaded(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.images_loaded.cached() {
            return cached;
        }
        let result = game_init::images_loaded(self);
        self.images_loaded.cache(&result);
        result
    }

    pub fn local_player_name(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.local_player_name.cached() {
            return cached;
        }
        let result = game_init::local_player_name(self);
        self.local_player_name.cache(&result);
        result
    }

    pub fn step_network(&mut self) -> Rc<StepNetwork<E::VirtualAddress>> {
        if let Some(cached) = self.step_network.cached() {
            return cached;
        }
        let result = Rc::new(commands::step_network(self));
        self.step_network.cache(&result);
        result
    }

    pub fn init_game_network(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.init_game_network.cached() {
            return cached;
        }
        let result = game_init::init_game_network(self);
        self.init_game_network.cache(&result);
        result
    }

    pub fn snp_definitions(&mut self) -> Option<SnpDefinitions> {
        if let Some(cached) = self.snp_definitions.cached() {
            return cached;
        }
        let result = network::snp_definitions(self);
        self.snp_definitions.cache(&result);
        result
    }

    pub fn lobby_state(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.lobby_state.cached() {
            return cached;
        }
        let result = game_init::lobby_state(self);
        self.lobby_state.cache(&result);
        result
    }

    pub fn init_storm_networking(&mut self) -> Rc<InitStormNetworking<E::VirtualAddress>> {
        if let Some(cached) = self.init_storm_networking.cached() {
            return cached;
        }
        let result = Rc::new(network::init_storm_networking(self));
        self.init_storm_networking.cache(&result);
        result
    }

    pub fn step_order(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.step_order.cached() {
            return cached;
        }
        let result = step_order::step_order(self);
        self.step_order.cache(&result);
        result
    }

    pub fn step_order_hidden(&mut self) ->
        Rc<Vec<step_order::StepOrderHiddenHook<E::VirtualAddress>>>
    {
        if let Some(cached) = self.step_order_hidden.cached() {
            return cached;
        }
        let result = step_order::step_order_hidden(self);
        let result = Rc::new(result);
        self.step_order_hidden.cache(&result);
        result
    }

    pub fn step_secondary_order(&mut self) ->
        Rc<Vec<step_order::SecondaryOrderHook<E::VirtualAddress>>>
    {
        if let Some(cached) = self.step_secondary_order.cached() {
            return cached;
        }
        let result = step_order::step_secondary_order(self);
        let result = Rc::new(result);
        self.step_secondary_order.cache(&result);
        result
    }

    pub fn step_iscript(&mut self) -> Rc<StepIscript<E::VirtualAddress>> {
        if let Some(cached) = self.step_iscript.cached() {
            return cached;
        }
        let result = iscript::step_iscript(self);
        let result = Rc::new(result);
        self.step_iscript.cache(&result);
        result
    }

    pub fn add_overlay_iscript(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.add_overlay_iscript.cached() {
            return cached;
        }
        let result = iscript::add_overlay_iscript(self);
        self.add_overlay_iscript.cache(&result);
        result
    }

    pub fn draw_cursor_marker(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.draw_cursor_marker.cached() {
            return cached;
        }
        let result = iscript::draw_cursor_marker(self);
        self.draw_cursor_marker.cache(&result);
        result
    }

    pub fn play_smk(&mut self) -> Option<E::VirtualAddress> {
        if let Some(cached) = self.play_smk.cached() {
            return cached;
        }
        let result = game_init::play_smk(self);
        self.play_smk.cache(&result);
        result
    }

    pub fn game_init(&mut self) -> Rc<GameInit<E::VirtualAddress>> {
        if let Some(cached) = self.game_init.cached() {
            return cached;
        }
        let result = game_init::game_init(self);
        let result = Rc::new(result);
        self.game_init.cache(&result);
        result
    }

    pub fn misc_clientside(&mut self) -> Rc<MiscClientSide> {
        if let Some(cached) = self.misc_clientside.cached() {
            return cached;
        }
        let result = clientside::misc_clientside(self);
        let result = Rc::new(result);
        self.misc_clientside.cache(&result);
        result
    }
}

impl<'a> Analysis<'a, ExecutionStateX86<'a>> {
    pub fn units(&mut self) -> Option<Rc<Operand>> {
        fn check_memcpy(
            state: &mut ExecutionState,
            ctx: &OperandContext,
            i: &mut InternMap,
        ) -> Option<Rc<Operand>> {
            use scarf::operand_helpers::*;
            let esp = ctx.register(4);
            let arg2_loc = mem32(operand_add(esp.clone(), constval(4)));
            let arg2 = state.resolve(&arg2_loc, i);
            if arg2.ty != OperandType::Constant(0) {
                return None;
            }
            let arg3_loc = mem32(operand_add(esp.clone(), constval(8)));
            let arg3 = state.resolve(&arg3_loc, i);
            let arg3_ok = (
                arg3.if_arithmetic_mul()
                    .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                    .map(|(c, _)| c == 0x150)
                    .unwrap_or(false)
                ) || (
                    arg3.if_constant().map(|c| c == 0x150 * 1700).unwrap_or(false)
                );
            if arg3_ok {
                let arg1_loc = mem32(esp.clone());
                Some(state.resolve(&arg1_loc, i))
            } else {
                None
            }
        }

        if let Some(cached) = self.units.cached() {
            return cached;
        }

        let binary = self.binary;
        let ctx = &OperandContext::new();
        let init_units = self.init_units();
        let result = init_units.as_ref().and_then(|&entry| {
            let mut result = None;
            let mut analysis = FuncAnalysis::new(binary, &ctx, entry);
            'outer: while let Some(mut branch) = analysis.next_branch() {
                let mut operations = branch.operations();
                while let Some((op, state, _address, i)) = operations.next() {
                    match *op {
                        Operation::Call(ref dest) => {
                            if if_callable_const(binary, state, dest, i).is_some() {
                                let new = check_memcpy(state, &ctx, i);
                                if single_result_assign(new, &mut result) {
                                    break 'outer;
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
            result
        });

        self.units.cache(&result);
        result
    }

    pub fn first_ai_script(&mut self) -> Option<Rc<Operand>> {
        use crate::ai::*;
        if let Some(cached) = self.first_ai_script.cached() {
            return cached;
        }

        let binary = self.binary;
        let ctx = &OperandContext::new();
        let mut errors = Vec::new();

        let funcs = &self.functions();
        let aiscript_hook = self.aiscript_hook();
        let aiscript_hook = (*aiscript_hook).as_ref();
        let result = aiscript_hook.map(|x| x.op_limit_hook_begin).and_then(|hook_start| {
            entry_of_until(binary, &funcs, hook_start, |entry| {
                let mut result = None;
                let callers = find_callers(self, entry);
                for caller in callers {
                    let new = check_step_ai_scripts(binary, funcs, ctx, caller, &mut errors);
                    if single_result_assign(new, &mut result) {
                        break;
                    }
                }
                if let Some(res) = result {
                    EntryOf::Ok(res)
                } else {
                    EntryOf::Retry
                }
            }).into_option()
        });

        for e in errors {
            debug!("first_ai_script {}", e);
        }
        self.first_ai_script.cache(&result);
        result
    }

    pub fn first_guard_ai(&mut self) -> Option<Rc<Operand>> {
        use scarf::operand_helpers::*;

        if let Some(cached) = self.first_guard_ai.cached() {
            return cached;
        }

        let binary = self.binary;
        let ctx = &OperandContext::new();

        // There's a function referring build times and looping through all guard ais,
        // guard ais are the first memaccess
        let funcs = &self.functions();
        let build_time_refs = {
            let units_dat = self.dat_virtual_address(DatType::Units);
            units_dat.and_then(|(dat, dat_table_size)| {
                binary.read_u32(dat + 0x2a * dat_table_size).ok().map(|times| {
                    find_functions_using_global(self, VirtualAddress(times))
                        .into_iter()
                        .map(|global_ref| (VirtualAddress(times), global_ref.use_address))
                        .collect::<Vec<_>>()
                })
            }).unwrap_or_else(|| Vec::new())
        };
        let mut result = None;
        for (dat_address, use_address) in build_time_refs {
            let mut jump_limit = 0;
            let new = entry_of_until_memref(
                binary,
                &funcs,
                dat_address,
                use_address,
                &ctx,
                |reset, op, state, _ins_address, i| {
                    if reset {
                        jump_limit = 5;
                    }
                    if jump_limit == 0 {
                        return None;
                    }
                    match op {
                        Operation::Call(..) | Operation::Jump { .. } => {
                            jump_limit -= 1;
                        }
                        Operation::Move(_, ref val, _) => {
                            let val = state.resolve(val, i);
                            return val.if_memory()
                                .filter(|mem| mem.size == MemAccessSize::Mem32)
                                .and_then(|mem| mem.address.if_arithmetic_add())
                                .and_then(|(l, r)| {
                                    Operand::either(l, r, |x| x.if_arithmetic_mul())
                                })
                                .and_then(|((l, r), other)| {
                                    Operand::either(l, r, |x| x.if_constant())
                                        .filter(|&(c, _)| c == 8)
                                        .map(|_| other)
                                }).map(|val| {
                                    Operand::simplified(operand_sub(val.clone(), ctx.const_4()))
                                });
                        }
                        _ => (),
                    }
                    None
                },
            ).into_option();
            if single_result_assign(new, &mut result) {
                break;
            }
        }

        self.first_guard_ai.cache(&result);
        result
    }

    pub fn player_ai_towns(&mut self) -> Option<Rc<Operand>> {
        use crate::ai::*;

        #[derive(Clone)]
        struct AiTownState {
            jump_count: u32,
        }
        impl analysis::AnalysisState for AiTownState {
            fn merge(&mut self, new: AiTownState) {
                self.jump_count = self.jump_count.max(new.jump_count);
            }
        }
        struct AiTownAnalyzer<'a> {
            result: Option<Rc<Operand>>,
            binary: &'a BinaryFile,
            ctx: &'a OperandContext,
        }
        impl<'a> analysis::Analyzer<'a> for AiTownAnalyzer<'a> {
            type State = AiTownState;
            type Exec = scarf::ExecutionStateX86<'a>;
            fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
                match *op {
                    Operation::Call(ref dest) => {
                        let dest = {
                            let (state, i) = ctrl.exec_state();
                            if_callable_const(self.binary, state, dest, i)
                        };
                        if let Some(dest) = dest {
                            let res = ai_towns_child_func(
                                self.binary,
                                dest,
                                &self.ctx,
                            );
                            if single_result_assign(res, &mut self.result) {
                                ctrl.end_analysis();
                            }
                        }
                    }
                    Operation::Move(ref _dest, ref val, ref _cond) => {
                        let res = {
                            let (state, i) = ctrl.exec_state();
                            ai_towns_check(val, state, i, &self.ctx)
                        };
                        if single_result_assign(res, &mut self.result) {
                            ctrl.end_analysis();
                        }
                    }
                    Operation::Jump { ref to, .. } => {
                        let end = {
                            let state = ctrl.user_state();
                            if to.if_constant().is_none() {
                                state.jump_count = !0;
                            } else {
                                state.jump_count += 1;
                            };
                            state.jump_count > 2
                        };
                        if end {
                            ctrl.end_branch();
                        }
                    }
                    _ => (),
                }
            }
        }

        if let Some(cached) = self.player_ai_towns.cached() {
            return cached;
        }

        let binary = self.binary;
        let ctx = &OperandContext::new();

        let aiscript = self.aiscript_hook();

        let mut result = None;
        for aiscript_hook in aiscript.iter() {
            let start_town = match binary.read_u32(aiscript_hook.switch_table + 0x3 * 4) {
                Ok(o) => VirtualAddress(o),
                Err(_) => continue,
            };

            let state = AiTownState {
                jump_count: 0,
            };
            let mut i = InternMap::new();
            let exec_state = ExecutionState::new(&ctx, &mut i);
            let mut analysis =
                FuncAnalysis::custom_state(binary, ctx, start_town, exec_state, state, i);
            let mut analyzer = AiTownAnalyzer {
                result: None,
                binary,
                ctx,
            };
            analysis.analyze(&mut analyzer);
            if single_result_assign(analyzer.result, &mut result) {
                break;
            }
        }

        self.player_ai_towns.cache(&result);
        result
    }

    pub fn init_units(&mut self) -> Option<VirtualAddress> {
        if let Some(cached) = self.init_units.cached() {
            return cached;
        }
        let binary = self.binary;
        let ctx = &OperandContext::new();

        let units = self.dat(DatType::Units)?;
        let orders = self.dat(DatType::Orders)?;
        let mut unit_refs = Vec::new();
        let mut order_refs = Vec::new();
        {
            let mut arr = [(&units, &mut unit_refs), (&orders, &mut order_refs)];
            for &mut (ref dat, ref mut out) in &mut arr {
                **out = dat.address.iter()
                    .filter_map(|x| x.if_constant())
                    .flat_map(|x| {
                        find_functions_using_global(self, VirtualAddress::from_u64(x))
                    }).collect::<Vec<_>>()
            }
        }
        let str_refs = string_refs(binary, self, b"arr\\units.dat\0");

        let mut common = unit_refs.iter()
            .filter(|x| order_refs.iter().any(|y| x.func_entry == y.func_entry))
            .filter(|x| str_refs.iter().any(|y| x.func_entry == y.func_entry))
            .map(|x| x.func_entry)
            .next();
        if common.is_none() {
            // Different strategy if a fake call happens to be in between orders and units
            struct Analyzer<'a> {
                units_dat_seen: bool,
                units_dat: &'a Rc<Operand>,
                units_dat_str_seen: bool,
                units_dat_str_refs: &'a [StringRefs<VirtualAddress>],
            }
            impl<'a, 'exec: 'a> scarf::Analyzer<'exec> for Analyzer<'a> {
                type State = analysis::DefaultState;
                type Exec = scarf::ExecutionStateX86<'exec>;
                fn operation(&mut self, ctrl: &mut Control<Self>, op: &Operation) {
                    match *op {
                        Operation::Move(_, ref from, None) => {
                            let from = ctrl.resolve(from);
                            for oper in from.iter() {
                                if *oper == **self.units_dat {
                                    self.units_dat_seen = true;
                                }
                            }
                            let str_ref_addr = self.units_dat_str_refs.iter().any(|x| {
                                x.use_address >= ctrl.address() &&
                                    x.use_address < ctrl.current_instruction_end()
                            });
                            if str_ref_addr {
                                self.units_dat_str_seen = true;
                            }
                            if self.units_dat_seen && self.units_dat_str_seen {
                                ctrl.end_analysis();
                            }
                        }
                        _ => (),
                    }
                }
            }

            common = order_refs.iter().filter(|order_ref| {
                let mut analyzer = Analyzer {
                    units_dat_seen: false,
                    units_dat: &units.address,
                    units_dat_str_seen: false,
                    units_dat_str_refs: &str_refs[..],
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, order_ref.func_entry);
                analysis.analyze(&mut analyzer);
                analyzer.units_dat_seen && analyzer.units_dat_str_seen
            }).map(|x| x.func_entry).next();
        }

        debug!("init_units {:?}", common);
        let result = common;
        self.init_units.cache(&result);
        result
    }

    pub fn init_game(&mut self) -> Rc<InitGame> {
        if let Some(cached) = self.init_game.cached() {
            return cached;
        }
        let binary = self.binary;
        let ctx = &OperandContext::new();

        let init_units = self.init_units();
        let functions = self.functions();

        //let mut result = Vec::new();
        let mut errors = Vec::new();
        let mut result = None;
        'outer: for &x in init_units.iter() {
            let callers = find_callers(self, x);
            for call in callers {
                let mut invalid_handle_cmps: Vec<(VirtualAddress, _)> = Vec::new();
                result = entry_of_until_call(
                    binary,
                    &functions,
                    call,
                    ctx,
                    &mut errors,
                    |reset, op, state, ins_address, i| {
                        if reset {
                            invalid_handle_cmps.clear();
                        }
                        match *op {
                            Operation::Jump { ref condition, .. } => {
                                let cond = state.resolve(condition, i);
                                let cmp_invalid_handle = cond.iter_no_mem_addr()
                                    .filter_map(|x| x.if_arithmetic_eq())
                                    .filter_map(|(l, r)| {
                                        Operand::either(l, r, |x| x.if_constant())
                                    })
                                    .filter(|&(c, _)| c as u32 == u32::max_value())
                                    .map(|x| x.1.clone())
                                    .next();
                                if let Some(h) = cmp_invalid_handle {
                                    if !invalid_handle_cmps.iter().any(|x| x.0 == ins_address) {
                                        invalid_handle_cmps.push((ins_address, h));
                                    }
                                    if invalid_handle_cmps.len() >= 3 {
                                        let first = &invalid_handle_cmps[0].1;
                                        let ok = (&invalid_handle_cmps[1..]).iter()
                                            .all(|x| x.1 == *first);
                                        if ok {
                                            return Some(invalid_handle_cmps.swap_remove(0).1);
                                        }
                                    }
                                }
                            }
                            _ => (),
                        }
                        None
                    },
                ).into_option_with_entry();
                if result.is_some() {
                    break 'outer;
                }
            }
        }

        let result = if let Some((entry, loaded_save)) = result {
            InitGame {
                init_game: Some(entry),
                loaded_save: Some(loaded_save),
            }
        } else {
            InitGame {
                init_game: None,
                loaded_save: None,
            }
        };
        let result = Rc::new(result);
        self.init_game.cache(&result);
        result
    }

    pub fn player_ai(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.player_ai.cached() {
            return cached;
        }
        let binary = self.binary;
        let aiscript = self.aiscript_hook();
        let mut errors = Vec::new();
        let mut result = None;
        'outest: for aiscript_hook in aiscript.iter() {
            use scarf::operand_helpers::*;

            let farms_notiming = match binary.read_u32(aiscript_hook.switch_table + 0x32 * 4) {
                Ok(o) => VirtualAddress(o),
                Err(_) => continue,
            };

            let ctx = OperandContext::new();
            // Set script->player to 0
            let mut interner = InternMap::new();
            let mut state = ExecutionState::new(&ctx, &mut interner);
            let player = mem32(operand_add(
                aiscript_hook.script_operand_at_switch.clone(),
                ctx.constant(0x10),
            ));
            state.move_to(&DestOperand::from_oper(&player), ctx.const_0(), &mut interner);
            let mut analysis = FuncAnalysis::with_state(
                binary,
                &ctx,
                farms_notiming,
                state,
                interner,
            );
            'fn_branches: while let Some(mut branch) = analysis.next_branch() {
                let mut operations = branch.operations();
                while let Some((op, state, _address, interner)) = operations.next() {
                    match *op {
                        Operation::Call(ref dest) => {
                            if let Some(dest) = if_callable_const(binary, state, dest, interner) {
                                let res = find_player_ai_child_func(
                                    binary,
                                    dest,
                                    state.clone(),
                                    &ctx,
                                    interner.clone(),
                                    &mut errors,
                                );
                                if single_result_assign(res, &mut result) {
                                    break 'outest;
                                }
                            }
                        }
                        Operation::Move(ref dest, ref val, ref _cond) => {
                            let ai = player_ai_detect_write(dest, val, state, interner);
                            if single_result_assign(ai, &mut result) {
                                break 'outest;
                            }
                        }
                        Operation::Jump { .. } => {
                            // Early break as optimization since jumps shouldn't be needed ever
                            // (Now only in tests since single_result_assign, oh well)
                            if result.is_some() {
                                break 'fn_branches;
                            }
                        }
                        _ => (),
                    }
                }
            }
            errors.extend(analysis.errors.into_iter().map(|(a, b)| {
                Error::Scarf(to_default_base(binary, a), b)
            }));
        }
        for e in errors {
            debug!("player_ai {}", e);
        }
        self.player_ai.cache(&result);
        result
    }

    pub fn sprites(&mut self) -> Rc<Sprites> {
        if let Some(cached) = self.sprites.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = sprites::sprites(self, &ctx);
        let result = Rc::new(result);
        self.sprites.cache(&result);
        result
    }

    pub fn eud_table(&mut self) -> Rc<EudTable> {
        if let Some(cached) = self.eud.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = eud::eud_table(self, &ctx);
        let result = Rc::new(result);
        self.eud.cache(&result);
        result
    }

    pub fn map_tile_flags(&mut self) -> Rc<map::MapTileFlags> {
        if let Some(cached) = self.map_tile_flags.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = Rc::new(map::map_tile_flags(self, &ctx));
        self.map_tile_flags.cache(&result);
        result
    }

    pub fn players(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.players.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = players::players(self, &ctx);
        self.players.cache(&result);
        result
    }

    pub fn draw_image(&mut self) -> Option<VirtualAddress> {
        if let Some(cached) = self.draw_image.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = renderer::draw_image(self, &ctx);
        self.draw_image.cache(&result);
        result
    }

    pub fn bullet_creation(&mut self) -> Rc<BulletCreation> {
        if let Some(cached) = self.bullet_creation.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = bullets::bullet_creation(self, &ctx);
        let result = Rc::new(result);
        self.bullet_creation.cache(&result);
        result
    }

    pub fn net_players(&mut self) -> Rc<NetPlayers> {
        if let Some(cached) = self.net_players.cached() {
            return cached;
        }
        let ctx = OperandContext::new();
        let result = players::net_players(self, &ctx);
        let result = Rc::new(result);
        self.net_players.cache(&result);
        result
    }

    pub fn campaigns(&mut self) -> Option<Rc<Operand>> {
        if let Some(cached) = self.campaigns.cached() {
            return cached;
        }
        let result = campaign::campaigns(self);
        self.campaigns.cache(&result);
        result
    }

    pub fn run_dialog(&mut self) -> Option<VirtualAddress> {
        if let Some(cached) = self.run_dialog.cached() {
            return cached;
        }
        let result = dialog::run_dialog(self);
        self.run_dialog.cache(&result);
        result
    }

    pub fn ai_update_attack_target(&mut self) -> Option<VirtualAddress> {
        if let Some(cached) = self.ai_update_attack_target.cached() {
            return cached;
        }
        let result = ai::ai_update_attack_target(self);
        self.ai_update_attack_target.cache(&result);
        result
    }

    pub fn is_outside_game_screen(&mut self) -> Option<VirtualAddress> {
        if let Some(cached) = self.is_outside_game_screen.cached() {
            return cached;
        }
        let result = clientside::is_outside_game_screen(self);
        self.is_outside_game_screen.cache(&result);
        result
    }

    pub fn game_coord_conversion(&mut self) -> Rc<GameCoordConversion> {
        if let Some(cached) = self.game_coord_conversion.cached() {
            return cached;
        }
        let result = clientside::game_coord_conversion(self);
        let result = Rc::new(result);
        self.game_coord_conversion.cache(&result);
        result
    }

    pub fn fow_sprites(&mut self) -> Rc<FowSprites> {
        if let Some(cached) = self.fow_sprites.cached() {
            return cached;
        }
        let result = sprites::fow_sprites(self);
        let result = Rc::new(result);
        self.fow_sprites.cache(&result);
        result
    }
}

// Tries to return a func index to the address less or equal to `entry` that is definitely a
// function entry. Has still a hard limit.
fn first_definite_entry<Va: VirtualAddressTrait>(
    binary: &scarf::BinaryFile<Va>,
    entry: Va,
    funcs: &[Va],
    limit: usize,
) -> (usize, usize) {
    fn is_definitely_entry<Va: VirtualAddressTrait>(
        binary: &scarf::BinaryFile<Va>,
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

fn find_player_ai_child_func(
    binary: &BinaryFile,
    func: VirtualAddress,
    mut state: ExecutionState,
    ctx: &OperandContext,
    mut interner: InternMap,
    errors: &mut Vec<Error>,
) -> Option<Rc<Operand>> {
    use scarf::operand_helpers::*;

    trace!("player_ai child func {:x}", func.0);
    let esp = ctx.register(4);
    state.move_to(&DestOperand::from_oper(&esp), operand_sub(esp, ctx.const_4()), &mut interner);
    let mut analysis = FuncAnalysis::with_state(binary, &ctx, func, state, interner);
    let mut result = None;
    'outer: while let Some(mut branch) = analysis.next_branch() {
        let mut operations = branch.operations();
        while let Some((op, state, _address, interner)) = operations.next() {
            match *op {
                Operation::Move(ref dest, ref val, ref _cond) => {
                    let ai = player_ai_detect_write(dest, val, state, interner);
                    if single_result_assign(ai, &mut result) {
                        break 'outer;
                    }
                }
                _ => (),
            }
        }
    }
    errors.extend(analysis.errors.into_iter().map(|(a, b)| {
        Error::Scarf(to_default_base(binary, a), b)
    }));
    result
}

fn player_ai_detect_write(
    dest: &DestOperand,
    val: &Rc<Operand>,
    state: &mut ExecutionState,
    interner: &mut InternMap,
) -> Option<Rc<Operand>> {
    use scarf::operand_helpers::*;
    if let DestOperand::Memory(ref mem) = *dest {
        let dest = state.resolve(&mem.address, interner);
        let val = state.resolve(val, interner);
        val.if_arithmetic_or()
            .and_either_other(|x| x.if_memory().filter(|mem| mem.address == dest))
            .and_then(|y| y.if_constant())
            .and_then(|c| match c {
                // mem.address is &player_ai[0].flags
                0x10 => Some(Operand::simplified(operand_sub(dest, constval(0x218)))),
                _ => None,
            })
    } else {
        None
    }
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

pub fn string_refs<'a, E: ExecutionStateTrait<'a>>(
    binary: &scarf::BinaryFile<E::VirtualAddress>,
    cache: &mut Analysis<'a, E>,
    string: &[u8],
) -> Vec<StringRefs<E::VirtualAddress>> {
    let text = binary.section(b".text\0\0\0").unwrap();
    let rdata = binary.section(b".rdata\0\0").unwrap();
    let str_ref_addrs = find_strings_casei(&rdata.data, string);
    // (Use rva, string rva)
    let code_addresses = str_ref_addrs.into_iter().flat_map(|str_rva| {
        let ptr_refs = if <E::VirtualAddress as VirtualAddressTrait>::SIZE == 4 {
            let bytes = ((rdata.virtual_address + str_rva.0).as_u64() as u32).to_le_bytes();
            find_bytes(&text.data, &bytes[..])
        } else {
            let bytes = ((rdata.virtual_address + str_rva.0).as_u64()).to_le_bytes();
            find_bytes(&text.data, &bytes[..])
        };
        ptr_refs.into_iter().map(move |x| (x, str_rva))
    }).collect::<Vec<_>>();
    let functions = cache.functions();
    // (Func addr, string address)
    // Takes just the first func above the string use rva
    code_addresses.iter().map(|&(code_rva, str_rva)| {
        let code_va = text.virtual_address + code_rva.0;
        let index = match functions.binary_search(&code_va) {
            Ok(x) => x,
            Err(x) => x,
        };
        StringRefs {
            use_address: code_va,
            func_entry: functions[index.saturating_sub(1)],
            string_address: rdata.virtual_address + str_rva.0,
        }
    }).collect()
}

fn find_callers<'exec, E: ExecutionStateTrait<'exec>>(
    cache: &mut Analysis<'exec, E>,
    func_entry: E::VirtualAddress,
) -> Vec<E::VirtualAddress> {
    use std::cmp::Ordering;
    let callers = cache.functions_with_callers();
    let lower_bound = callers.binary_search_by(|x| match x.callee >= func_entry {
        true => Ordering::Greater,
        false => Ordering::Less,
    }).unwrap_err();
    (&callers[lower_bound..]).iter()
        .take_while(|&x| x.callee == func_entry)
        .map(|x| x.caller)
        .collect()
}

pub enum EntryOf<R> {
    Ok(R),
    Retry,
    Stop,
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

fn entry_of_until_memref<'a, F, R>(
    binary: &'a BinaryFile,
    funcs: &[VirtualAddress],
    mem_address: VirtualAddress,
    ref_address: VirtualAddress,
    ctx: &'a OperandContext,
    mut cb: F,
) -> EntryOfResult<R, VirtualAddress>
where F: FnMut(
    bool,
    &Operation,
    &mut ExecutionState<'a>,
    VirtualAddress,
    &mut InternMap,
) -> Option<R>
{
    fn check_op(operand: &Rc<Operand>, addr: VirtualAddress) -> bool {
        operand.iter().any(|x| match x.ty {
            OperandType::Constant(c) => c == addr.as_u64(),
            _ => false,
        })
    }
    entry_of_until(binary, funcs, ref_address, |entry| {
        let mut reset = true;
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        let mut call_found = false;
        let mut result = None;
        'outer: while let Some(mut branch) = analysis.next_branch() {
            let mut operations = branch.operations();
            while let Some((op, state, ins_address, i)) = operations.next() {
                if !call_found {
                    if ins_address >= ref_address && ins_address < ref_address + 16 {
                        match *op {
                            // All of these are intentionally unresolved, assuming
                            // that if a globalref was found, it'd be in a unresolved
                            // ins as well.
                            Operation::Move(ref to, ref from, _) => {
                                if check_op(from, mem_address) {
                                    call_found = true;
                                } else {
                                    if let DestOperand::Memory(ref mem) = *to {
                                        if check_op(&mem.address, mem_address) {
                                            call_found = true;
                                        }
                                    }
                                }
                            }
                            Operation::Jump { ref to, .. } => {
                                // Skipping cond since x86 can't globalref in conds
                                if check_op(to, mem_address) {
                                    call_found = true;
                                }
                            }
                            Operation::Call(ref dest) => {
                                if check_op(dest, mem_address) {
                                    call_found = true;
                                }
                            }
                            _ => (),
                        }
                    }
                }
                result = cb(reset, op, state, ins_address, i);
                reset = false;
                if result.is_some() {
                    break 'outer;
                }
            }
        }
        if let Some(res) = result {
            return EntryOf::Ok(res);
        }
        if call_found {
            EntryOf::Stop
        } else {
            EntryOf::Retry
        }
    })
}

fn entry_of_until_call<'a, F, R>(
    binary: &'a BinaryFile,
    funcs: &[VirtualAddress],
    caller: VirtualAddress,
    ctx: &'a OperandContext,
    errors: &mut Vec<Error>,
    mut cb: F,
) -> EntryOfResult<R, VirtualAddress>
where F: FnMut(
    bool,
    &Operation,
    &mut ExecutionState<'a>,
    VirtualAddress,
    &mut InternMap,
) -> Option<R>
{
    entry_of_until(binary, funcs, caller, |entry| {
        let mut reset = true;
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        let mut call_found = false;
        let mut result = None;
        'outer: while let Some(mut branch) = analysis.next_branch() {
            let mut operations = branch.operations();
            while let Some((op, state, ins_address, i)) = operations.next() {
                if ins_address == caller {
                    call_found = true;
                }
                result = cb(reset, op, state, ins_address, i);
                reset = false;
                if result.is_some() {
                    break 'outer;
                }
            }
        }
        errors.extend(analysis.errors.into_iter().map(|(a, b)| {
            Error::Scarf(to_default_base(binary, a), b)
        }));
        if let Some(res) = result {
            return EntryOf::Ok(res);
        }
        if call_found {
            EntryOf::Stop
        } else {
            EntryOf::Retry
        }
    })
}

/// Better version of entry_of, retries with an earlier func if the cb returns false,
/// helps against false positive func entries.
fn entry_of_until<'a, Va: VirtualAddressTrait, R, F>(
    binary: &scarf::BinaryFile<Va>,
    funcs: &[Va],
    caller: Va,
    mut cb: F,
) -> EntryOfResult<R, Va>
where F: FnMut(Va) -> EntryOf<R>
{
    let entry = entry_of(funcs, caller);
    let (start, end) = first_definite_entry(binary, entry, funcs, 16);
    for &entry in funcs.iter().take(end).skip(start) {
        match cb(entry) {
            EntryOf::Ok(s) => return EntryOfResult::Ok(entry, s),
            EntryOf::Stop => return EntryOfResult::Entry(entry),
            EntryOf::Retry => (),
        }
    }
    debug!("entry_of_until limit reached for caller {:?} {:?}", caller, start..end);
    EntryOfResult::None
}

fn entry_of<Va: VirtualAddressTrait>(funcs: &[Va], func: Va) -> Va {
    let index = funcs.binary_search_by(|&x| match x <= func {
        true => std::cmp::Ordering::Less,
        false => std::cmp::Ordering::Greater,
    }).unwrap_or_else(|e| e);
    funcs[index.saturating_sub(1)]
}

fn find_functions_using_global<'exec, E: ExecutionStateTrait<'exec>>(
    cache: &mut Analysis<'exec, E>,
    addr: E::VirtualAddress,
) -> Vec<GlobalRefs<E::VirtualAddress>> {
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
        })
        .collect();
    result
}

fn read_u32_at<Va: VirtualAddressTrait>(section: &BinarySection<Va>, offset: Rva) -> Option<u32> {
    section.data.get(offset.0 as usize..offset.0 as usize + 4)
        .and_then(|mut x| x.read_u32::<LE>().ok())
}

fn to_default_base(binary: &BinaryFile, addr: VirtualAddress) -> VirtualAddress {
    let text = binary.section(b".text\0\0\0").unwrap();
    VirtualAddress(0x0040_1000) + (addr - text.virtual_address)
}

/// Returns any matching strings as Rvas.
///
/// Remember to null-terminate strings if needed =)
fn find_strings_casei(mut data: &[u8], needle: &[u8]) -> Vec<Rva> {
    let mut ret = vec![];
    let mut offset = 0;
    let first = needle[0];
    while data.len() >= needle.len() {
        let result = match first {
            x if x >= b'a' && x <= b'z' => memchr::memchr2(x, x - b'a' + b'A', data),
            x if x >= b'A' && x <= b'Z' => memchr::memchr2(x, x - b'A' + b'a', data),
            x => memchr::memchr(x, data),
        };
        match result {
            Some(pos) => {
                if pos + needle.len() > data.len() {
                    break;
                }
                if needle.eq_ignore_ascii_case(&data[pos..pos + needle.len()]) {
                    ret.push(Rva((offset + pos) as u32));
                }
                offset += pos + 1;
                data = &data[pos + 1..];
            }
            None => break,
        }
    }
    ret
}

fn find_address_refs<Va: VirtualAddressTrait>(data: &[u8], addr: Va) -> Vec<Rva> {
    let mut result = if Va::SIZE == 4 {
        let bytes = (addr.as_u64() as u32).to_le_bytes();
        find_bytes(data, &bytes[..])
    } else {
        let bytes = addr.as_u64().to_le_bytes();
        find_bytes(data, &bytes[..])
    };
    // Filter out if align is less than 4.
    // 64-bit bw can have 4-aligned pointers.
    result.retain(|x| x.0 & 3 == 0);
    result
}

fn find_bytes(mut data: &[u8], needle: &[u8]) -> Vec<Rva> {
    let mut ret = vec![];
    let mut offset = 0;
    let first = needle[0];
    while data.len() >= needle.len() {
        let result = memchr::memchr(first, data);
        match result {
            Some(pos) => {
                if pos + needle.len() > data.len() {
                    break;
                }
                if needle == &data[pos..pos + needle.len()] {
                    ret.push(Rva((offset + pos) as u32));
                }
                offset += pos + 1;
                data = &data[pos + 1..];
            }
            None => break,
        }
    }
    ret
}

fn if_callable_const<'e, E: ExecutionStateTrait<'e>>(
    binary: &scarf::BinaryFile<E::VirtualAddress>,
    state: &mut E,
    dest: &Rc<Operand>,
    interner: &mut InternMap,
) -> Option<E::VirtualAddress> {
    state.resolve(dest, interner).if_constant()
        .and_then(|dest| {
            let dest = E::VirtualAddress::from_u64(dest);
            let code_section = binary.code_section();
            let code_section_end = code_section.virtual_address + code_section.virtual_size;
            if dest > code_section.virtual_address && dest < code_section_end {
                Some(dest)
            } else {
                None
            }
        })
}

/// Helper extension functions for Option<(&Rc<Operand>, &Rc<Operand>)>.
trait OptionExt<'a> {
    /// `opt.and_either(x)` is equivalent to
    /// `opt.and_then(|(l, r)| Operand::either(l, r, x))`
    fn and_either<F, T>(self, cb: F) -> Option<(T, &'a Rc<Operand>)>
    where F: FnMut(&'a Rc<Operand>) -> Option<T>;
    /// `opt.and_either_other(x)` is equivalent to
    /// `opt.and_then(|(l, r)| Operand::either(l, r, x)).map(|(_, other)| other)`
    fn and_either_other<F, T>(self, cb: F) -> Option<&'a Rc<Operand>>
    where F: FnMut(&'a Rc<Operand>) -> Option<T>;
}

impl<'a> OptionExt<'a> for Option<(&'a Rc<Operand>, &'a Rc<Operand>)> {
    fn and_either<F, T>(self, cb: F) -> Option<(T, &'a Rc<Operand>)>
    where F: FnMut(&'a Rc<Operand>) -> Option<T>
    {
        self.and_then(|(l, r)| Operand::either(l, r, cb))
    }

    fn and_either_other<F, T>(self, cb: F) -> Option<&'a Rc<Operand>>
    where F: FnMut(&'a Rc<Operand>) -> Option<T>
    {
        self.and_either(cb).map(|(_, other)| other)
    }
}

/// Returns true if the stack is setup for a call that seems to be reporting an assertion
/// error
fn seems_assertion_call<'exec, A: analysis::Analyzer<'exec>>(
    ctrl: &mut Control<'exec, '_, '_, A>,
    binary: &BinaryFile,
) -> bool {
    use scarf::operand_helpers::*;
    let esp = operand_register(4);
    let arg1 = match ctrl.resolve(&mem32(esp.clone())).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg2 = match ctrl.resolve(&mem32(operand_add(esp.clone(), constval(4)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg3 = match ctrl.resolve(&mem32(operand_add(esp.clone(), constval(8)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg4 = match ctrl.resolve(&mem32(operand_add(esp, constval(0xc)))).if_constant() {
        Some(s) => s,
        None => return false,
    };
    if arg4 == 0 || arg4 > 12000 {
        return false;
    }
    // Could check that these are strings
    if binary.section_by_addr(VirtualAddress::from_u64(arg1)).is_none() {
        return false;
    }
    if binary.section_by_addr(VirtualAddress::from_u64(arg2)).is_none() {
        return false;
    }
    if binary.section_by_addr(VirtualAddress::from_u64(arg3)).is_none() {
        return false;
    }
    true
}

// bool true => eq, bool false => not eq
fn if_arithmetic_eq_neq(op: &Rc<Operand>) -> Option<(&Rc<Operand>, &Rc<Operand>, bool)> {
    op.if_arithmetic_eq()
        .map(|(l, r)| {
            Operand::either(l, r, |x| x.if_constant().filter(|&c| c == 0))
                .and_then(|(_, other)| other.if_arithmetic_eq())
                .map(|(l, r)| (l, r, false))
                .unwrap_or_else(|| (l, r, true))
        })
}
