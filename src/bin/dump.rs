extern crate fern;
extern crate log;
extern crate samase_scarf;
extern crate scarf;

use std::io::{self, Write};
use std::path::Path;

use anyhow::{anyhow, Context, Result};
use byteorder::{LittleEndian, ByteOrder};

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile};

use samase_scarf::{Analysis, DatType};

fn format_op_operand(op: Option<scarf::Operand>) -> String {
    op.as_ref().map(|x| x.to_string()).unwrap_or_else(|| "None".into())
}

fn main() {
    init_stdout_log();
    let start_time = ::std::time::Instant::now();
    let exe = std::env::args_os().nth(1).unwrap();
    let do_dump_shaders = std::env::args_os().nth(2).and_then(|arg| {
        let ok = arg.to_str()? == "--dump-shaders";
        Some(()).filter(|()| ok)
    }).is_some();
    let do_dump_vtables = std::env::args_os().nth(2).and_then(|arg| {
        let ok = arg.to_str()? == "--dump-vtables";
        Some(()).filter(|()| ok)
    }).is_some();

    let mut binary = scarf::parse(&exe).unwrap();
    let relocs = scarf::analysis::find_relocs::<scarf::ExecutionStateX86<'_>>(&binary).unwrap();
    binary.set_relocs(relocs);
    let ctx = &scarf::OperandContext::new();
    let mut analysis = Analysis::<scarf::ExecutionStateX86<'_>>::new(&binary, ctx);

    if do_dump_shaders {
        let path = std::env::args_os().nth(3).unwrap();
        if let Err(e) = dump_shaders(&binary, &mut analysis, Path::new(&path)) {
            eprintln!("Failed to dump shaders: {:?}", e);
        }
        return;
    }
    if do_dump_vtables {
        dump_vtables(&binary, &mut analysis);
        return;
    }

    let open_file = analysis.file_hook();
    println!("open_file: {:?}", open_file);
    let firegraft = analysis.firegraft_addresses();
    println!("Buttonsets: {:?}", firegraft.buttonsets);
    println!("Unit status: {:?}", firegraft.unit_status_funcs);
    println!(
        "Req tables:\n\
        Units: {:?}\n\
        Upgrades: {:?}\n\
        Tech use: {:?}\n\
        Tech research: {:?}\n\
        Orders: {:?}",
        firegraft.requirement_table_refs.units,
        firegraft.requirement_table_refs.upgrades,
        firegraft.requirement_table_refs.tech_use,
        firegraft.requirement_table_refs.tech_research,
        firegraft.requirement_table_refs.orders,
    );
    let aiscript_hook = analysis.aiscript_hook();
    println!("Aiscript hook: {:#?}", aiscript_hook);
    let rng = analysis.rng();
    println!("Rng seed: {}", format_op_operand(rng.seed));
    println!("Rng enable: {}", format_op_operand(rng.enable));
    let step_objects = analysis.step_objects();
    println!("step_objects: {:?}", step_objects);
    let game = analysis.game();
    println!("game: {}", format_op_operand(game));
    let player_ai = analysis.player_ai();
    println!("Player AI: {}", format_op_operand(player_ai));
    let regions = analysis.regions();
    println!("get_region: {:?}", regions.get_region);
    println!("AI regions: {}", format_op_operand(regions.ai_regions));
    println!("change_ai_region_state: {:?}", regions.change_ai_region_state);
    let pathing = analysis.pathing();
    println!("pathing: {}", format_op_operand(pathing));
    let unit_lists = analysis.active_hidden_units();
    println!("first_active_unit: {}", format_op_operand(unit_lists.first_active_unit));
    println!("first_hidden_unit: {}", format_op_operand(unit_lists.first_hidden_unit));
    let order_issuing = analysis.order_issuing();
    println!("prepare_issue_order: {:?}", order_issuing.prepare_issue_order);
    println!("do_next_queued_order: {:?}", order_issuing.do_next_queued_order);
    let step_order = analysis.step_order();
    println!("step_order: {:?}", step_order);
    let step_order_hidden = analysis.step_order_hidden();
    println!("step_order_hidden: {:?}", step_order_hidden);
    let step_secondary = analysis.step_secondary_order();
    println!("step_secondary_order: {:?}", step_secondary);
    let commands = analysis.process_commands();
    println!("process_commands: {:?}", commands.process_commands);
    println!("storm_command_user: {}", format_op_operand(commands.storm_command_user));
    for switch in &commands.switch {
        println!(
            "process_commands switch: {:?} ({:?} @ {:x})",
            switch.address, switch.indirection, switch.offset,
        );
    }
    let command_user = analysis.command_user();
    println!("command_user: {}", format_op_operand(command_user));
    let selections = analysis.selections();
    println!("unique_command_user: {}", format_op_operand(selections.unique_command_user));
    println!("selections: {}", format_op_operand(selections.selections));
    let lengths = analysis.command_lengths();
    let lengths = lengths.iter().map(|&x| x as i32).collect::<Vec<_>>();
    println!("command_lengths: len {:x}, {:?}", lengths.len(), lengths);
    let lobby_commands = analysis.process_lobby_commands();
    println!("process_lobby_commands: {:?}", lobby_commands);
    let send_command = analysis.send_command();
    println!("send_command: {:?}", send_command);
    let print_text = analysis.print_text();
    println!("print_text: {:?}", print_text);

    let format_dat = |val: &Option<samase_scarf::DatTablePtr>| {
        if let Some(x) = val {
            format!("{} (entry size {})", x.address, x.entry_size)
        } else {
            format!("None")
        }
    };
    println!("units.dat: {}", format_dat(&analysis.dat(DatType::Units)));
    println!("weapons.dat: {}", format_dat(&analysis.dat(DatType::Weapons)));
    println!("flingy.dat: {}", format_dat(&analysis.dat(DatType::Flingy)));
    println!("sprites.dat: {}", format_dat(&analysis.dat(DatType::Sprites)));
    println!("images.dat: {}", format_dat(&analysis.dat(DatType::Images)));
    println!("orders.dat: {}", format_dat(&analysis.dat(DatType::Orders)));
    println!("upgrades.dat: {}", format_dat(&analysis.dat(DatType::Upgrades)));
    println!("techdata.dat: {}", format_dat(&analysis.dat(DatType::TechData)));
    println!("sfxdata.dat: {}", format_dat(&analysis.dat(DatType::SfxData)));

    println!("init_units: {:?}", analysis.init_units());
    println!("load_dat: {:?}", analysis.load_dat());
    let init_game = analysis.init_game();
    println!("init_game: {:?}", init_game.init_game);
    println!(
        "loaded_save: {}",
        init_game.loaded_save.as_ref()
            .map(|x| x.to_string()).unwrap_or_else(|| "None".to_string()),
    );

    let is_replay = analysis.is_replay();
    println!("is_replay: {}", format_op_operand(is_replay));
    let units = analysis.units();
    println!("units: {}", format_op_operand(units));

    let rclick = analysis.game_screen_rclick();
    println!("game_screen_rclick: {:?}", rclick.game_screen_rclick);
    println!("client_selection: {}", format_op_operand(rclick.client_selection));

    let first_ai_script = analysis.first_ai_script();
    println!("first_ai_script: {}", format_op_operand(first_ai_script));
    let first_guard_ai = analysis.first_guard_ai();
    println!("first_guard_ai: {}", format_op_operand(first_guard_ai));
    let towns = analysis.player_ai_towns();
    println!("active_ai_towns: {}", format_op_operand(towns));

    let iscript = analysis.step_iscript();
    println!("step_iscript: {:?}", iscript.step_fn);
    println!("step iscript script ptr: {}", format_op_operand(iscript.script_operand_at_switch));
    println!("step iscript switch: {:?}", iscript.switch_table);
    println!("step iscript opcode check: {:?}", iscript.opcode_check);
    println!("iscript_bin: {}", format_op_operand(iscript.iscript_bin));

    let sprites = analysis.sprites();
    println!("sprite_hlines: {}", format_op_operand(sprites.sprite_hlines));
    println!("sprite_hlines_end: {}", format_op_operand(sprites.sprite_hlines_end));
    println!("first_free_sprite: {}", format_op_operand(sprites.first_free_sprite));
    println!("last_free_sprite: {}", format_op_operand(sprites.last_free_sprite));
    println!("first_lone: {}", format_op_operand(sprites.first_lone));
    println!("last_lone: {}", format_op_operand(sprites.last_lone));
    println!("first_free_lone: {}", format_op_operand(sprites.first_free_lone));
    println!("last_free_lone: {}", format_op_operand(sprites.last_free_lone));
    println!("create_lone: {:?}", sprites.create_lone_sprite);
    println!("sprite_x: {}", format_op_operand(sprites.sprite_x_position.map(|x| x.0)));
    println!("sprite_x_offset: {:x?}", sprites.sprite_x_position.map(|x| x.1));
    println!("sprite_x_size: {:x?}", sprites.sprite_x_position.map(|x| x.2));
    println!("sprite_y: {}", format_op_operand(sprites.sprite_y_position.map(|x| x.0)));
    println!("sprite_y_offset: {:x?}", sprites.sprite_y_position.map(|x| x.1));
    println!("sprite_y_size: {:x?}", sprites.sprite_x_position.map(|x| x.2));

    let euds = analysis.eud_table();
    println!("{} euds", euds.euds.len());

    let map_tile_flags = analysis.map_tile_flags();
    println!("map_tile_flags: {}", format_op_operand(map_tile_flags.map_tile_flags));
    println!("update_visibility_point: {:?}", map_tile_flags.update_visibility_point);
    let players = analysis.players();
    println!("players: {}", format_op_operand(players));
    let draw_image = analysis.draw_image();
    println!("draw_image: {:?}", draw_image);
    let renderer_vtables = analysis.renderer_vtables();
    println!("renderer_vtables: {:?}", renderer_vtables);
    let local_player_id = analysis.local_player_id();
    println!("local_player_id: {}", format_op_operand(local_player_id));
    let bullet_creation = analysis.bullet_creation();
    println!("first_active_bullet: {}", format_op_operand(bullet_creation.first_active_bullet));
    println!("last_active_bullet: {}", format_op_operand(bullet_creation.last_active_bullet));
    println!("first_free_bullet: {}", format_op_operand(bullet_creation.first_free_bullet));
    println!("last_free_bullet: {}", format_op_operand(bullet_creation.last_free_bullet));
    println!("active_iscript_unit: {}", format_op_operand(bullet_creation.active_iscript_unit));
    println!("create_bullet: {:?}", bullet_creation.create_bullet);

    let net_players = analysis.net_players();
    if let Some(ref net_players) = net_players.net_players {
        println!("net_players: {}, Size 0x{:x}", net_players.0, net_players.1);
    } else {
        println!("net_players: None");
    }
    println!("init_net_player: {:?}", net_players.init_net_player);
    let play_smk = analysis.play_smk();
    println!("play_smk: {:?}", play_smk);

    let game_init = analysis.game_init();
    println!("sc_main: {:?}", game_init.sc_main);
    println!("mainmenu_entry_hook: {:?}", game_init.mainmenu_entry_hook);
    println!("game_loop: {:?}", game_init.game_loop);
    println!("scmain_state: {}", format_op_operand(game_init.scmain_state));

    let add_overlay_iscript = analysis.add_overlay_iscript();
    println!("add_overlay_iscript: {:?}", add_overlay_iscript);
    let campaigns = analysis.campaigns();
    println!("campaigns: {}", format_op_operand(campaigns));
    let run_dialog = analysis.run_dialog();
    println!("run_dialog: {:?}", run_dialog);
    let spawn_dialog = analysis.spawn_dialog();
    println!("spawn_dialog: {:?}", spawn_dialog);
    let ai_update_attack_target = analysis.ai_update_attack_target();
    println!("ai_update_attack_target: {:?}", ai_update_attack_target);
    let is_outside_game_screen = analysis.is_outside_game_screen();
    println!("is_outside_game_screen: {:?}", is_outside_game_screen);

    let coords = analysis.game_coord_conversion();
    println!("screen_x: {}", format_op_operand(coords.screen_x));
    println!("screen_y: {}", format_op_operand(coords.screen_y));
    println!("graphic_scale: {}", format_op_operand(coords.scale));

    let fow = analysis.fow_sprites();
    println!("first_active_fow_sprite: {}", format_op_operand(fow.first_active));
    println!("last_active_fow_sprite: {}", format_op_operand(fow.last_active));
    println!("first_free_fow_sprite: {}", format_op_operand(fow.first_free));
    println!("last_free_fow_sprite: {}", format_op_operand(fow.last_free));

    let init_map_from_path = analysis.init_map_from_path();
    println!("init_map_from_path: {:?}", init_map_from_path);
    let choose_snp = analysis.choose_snp();
    println!("choose_snp: {:?}", choose_snp);
    println!("SNetInitializeProvider: {:?}", analysis.snet_initialize_provider());

    let start = analysis.single_player_start();
    println!("single_player_start: {:?}", start.single_player_start);
    println!("local_storm_player_id: {}", format_op_operand(start.local_storm_player_id));
    println!("local_unique_player_id: {}", format_op_operand(start.local_unique_player_id));
    println!("net_player_to_game: {}", format_op_operand(start.net_player_to_game));
    println!("net_player_to_unique: {}", format_op_operand(start.net_player_to_unique));
    println!("game_data: {}", format_op_operand(start.game_data));
    println!("skins: {}", format_op_operand(start.skins));
    println!("player_skins: {}", format_op_operand(start.player_skins));
    println!("skins_size: {:x}", start.skins_size);

    let sel = analysis.select_map_entry();
    println!("select_map_entry: {:?}", sel.select_map_entry);
    println!("is_multiplayer: {}", format_op_operand(sel.is_multiplayer));
    let load_images = analysis.load_images();
    println!("load_images: {:?}", load_images);
    let images_loaded = analysis.images_loaded();
    println!("images_loaded: {}", format_op_operand(images_loaded));
    let init_rtl = analysis.init_real_time_lighting();
    println!("init_real_time_lighting: {:?}", init_rtl);
    let local_player_name = analysis.local_player_name();
    println!("local_player_name: {}", format_op_operand(local_player_name));

    let step = analysis.step_network();
    println!("step_network: {:?}", step.step_network);
    println!("receive_storm_turns: {:?}", step.receive_storm_turns);
    println!("menu_screen_id: {}", format_op_operand(step.menu_screen_id));
    println!("net_player_flags: {}", format_op_operand(step.net_player_flags));
    println!("player_turns: {}", format_op_operand(step.player_turns));
    println!("player_turns_size: {}", format_op_operand(step.player_turns_size));
    println!("network_ready: {}", format_op_operand(step.network_ready));

    let init_game_network = analysis.init_game_network();
    println!("init_game_network: {:?}", init_game_network);

    let snp_definitions = analysis.snp_definitions();
    if let Some(defs) = snp_definitions {
        println!("snp_definitions: {}, {:x} bytes", defs.snp_definitions, defs.entry_size);
    } else {
        println!("snp_definitions: None");
    }

    let lobby_state = analysis.lobby_state();
    println!("lobby_state: {}", format_op_operand(lobby_state));
    let init_storm_networking = analysis.init_storm_networking();
    println!("init_storm_networking: {:?}", init_storm_networking.init_storm_networking);
    println!("load_snp_list: {:?}", init_storm_networking.load_snp_list);

    let draw_cursor_marker = analysis.draw_cursor_marker();
    println!("draw_cursor_marker: {}", format_op_operand(draw_cursor_marker));

    let misc_clientside = analysis.misc_clientside();
    println!("is_paused: {}", format_op_operand(misc_clientside.is_paused));
    println!("is_placing_building: {}", format_op_operand(misc_clientside.is_placing_building));
    println!("is_targeting: {}", format_op_operand(misc_clientside.is_targeting));

    let unit_creation = analysis.unit_creation();
    println!("create_unit: {:?}", unit_creation.create_unit);
    println!("finish_unit_pre: {:?}", unit_creation.finish_unit_pre);
    println!("finish_unit_post: {:?}", unit_creation.finish_unit_post);

    let fonts = analysis.fonts();
    println!("fonts: {}", format_op_operand(fonts));

    println!("init_sprites: {:?}", analysis.init_sprites());
    let sprite_array = analysis.sprite_array();
    println!("sprite_array: {}", format_op_operand(sprite_array.map(|x| x.0)));
    println!("sprite_struct_size: {:?}", sprite_array.map(|x| format!("0x{:x}", x.1)));
    println!("serialize_sprites: {:?}", analysis.serialize_sprites());
    println!("deserialize_sprites: {:?}", analysis.deserialize_sprites());

    let limits = analysis.limits();
    println!("set_limits: {:?}", limits.set_limits);
    for (i, arr) in limits.arrays.iter().enumerate() {
        let name = match i {
            0 => "images".into(),
            1 => "sprites".into(),
            2 => "lone_sprites".into(),
            3 => "units".into(),
            4 => "bullets".into(),
            5 => "orders".into(),
            6 => "fow_sprites".into(),
            i => format!("unk_{}", i * 4),
        };
        println!("limits.{}: {:?}", name, arr);
    }

    println!("font_cache_render_ascii: {:?}", analysis.font_cache_render_ascii());
    println!("ttf_cache_character: {:?}", analysis.ttf_cache_character());
    println!("ttf_render_sdf: {:?}", analysis.ttf_render_sdf());
    println!("ttf_malloc: {:?}", analysis.ttf_malloc());

    let offset = analysis.create_game_dialog_vtbl_on_multiplayer_create();
    println!("CreateGameScreen.on_multiplayer_create offset: {:x?}", offset);

    println!("tooltip_draw_func: {}", format_op_operand(analysis.tooltip_draw_func()));
    println!("current_tooltip_ctrl: {}", format_op_operand(analysis.current_tooltip_ctrl()));
    println!("layout_draw_text: {:?}", analysis.layout_draw_text());
    println!("graphic_layers: {}", format_op_operand(analysis.graphic_layers()));
    println!("draw_tooltip_layer: {:?}", analysis.draw_tooltip_layer());
    println!("draw_f10_menu_tooltip: {:?}", analysis.draw_f10_menu_tooltip());
    println!("draw_graphic_layers: {:?}", analysis.draw_graphic_layers());

    println!("Prism vertex shader sets: 0x{:x}", analysis.prism_vertex_shaders().len());
    println!("Prism pixel shader sets: 0x{:x}", analysis.prism_pixel_shaders().len());

    println!("ai_attack_prepare: {:?}", analysis.ai_attack_prepare());
    println!("ai_step_region: {:?}", analysis.ai_step_region());

    println!("join_game: {:?}", analysis.join_game());

    let undef = ctx.new_undef();
    println!();
    println!("Undefined count: {}", match *undef.ty() {
        scarf::operand::OperandType::Undefined(x) => x.0,
        _ => 0,
    });
    println!("Interned count: {}", ctx.interned_count());

    let elapsed = start_time.elapsed();
    println!("Time taken: {}.{:09} s", elapsed.as_secs(), elapsed.subsec_nanos());
}

fn init_stdout_log() {
    let _ = fern::Dispatch::new()
        .format(|out, message, record| {
            out.finish(
                format_args!(
                    "[{}:{}][{}] {}",
                    record.file().unwrap_or("???"),
                    record.line().unwrap_or(0),
                    record.level(),
                    message
                )
            )
        })
        .level(log::LevelFilter::Info)
        //.level_for("samase_scarf", log::LevelFilter::Trace)
        .chain(std::io::stdout())
        .apply();
}

fn create_dir(path: &Path) -> Result<()> {
    if !path.exists() {
        std::fs::create_dir(path)
            .with_context(|| format!("Couldn't create directory '{}'", path.display()))
    } else {
        Ok(())
    }
}

fn dump_shaders<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    analysis: &mut Analysis<'e, E>,
    path: &Path,
) -> Result<()> {
    create_dir(path)?;
    let vertex_shaders = analysis.prism_vertex_shaders();
    for (i, &set) in vertex_shaders.iter().enumerate() {
        let name = match i {
            0 => "vert_uv1".into(),
            1 => "vert_uv2".into(),
            2 => "vert_uv3".into(),
            3 => "flat_color_vert".into(),
            4 => "colored_vert".into(),
            5 => "deferred_blit_vert".into(),
            _ => format!("vertex_{}", i),
        };
        dump_shader_set(&path.join(&name), binary, set)
            .with_context(|| format!("Dumping {}", name))?;
    }
    let pixel_shaders = analysis.prism_pixel_shaders();
    for (i, &set) in pixel_shaders.iter().enumerate() {
        let name = match i {
            0x0 => "textured_frag".into(),
            0x1 => "textured_frag_bicubic".into(),
            0x2 => "flat_color_frag".into(),
            0x3 => "fbo_cloak_frag".into(),
            0x4 => "colored_frag".into(),
            0x5 => "colored_frag_gradient".into(),
            0x6 => "colored_frag_font".into(),
            0x7 => "video_444_frag".into(),
            0x8 => "video_YCbCR_frag".into(),
            0x9 => "palette_color_frag".into(),
            0xa => "bw_frag".into(),
            0xb => "deferred_blit".into(),
            0xc => "sprite_frag".into(),
            0xd => "sprite_forward_lit".into(),
            0xe => "sprite_tile".into(),
            0xf => "sprite_tile_draw_effect".into(),
            0x10 => "sprite_solid_frag".into(),
            0x11 => "sprite_solid_frag_deferred".into(),
            0x12 => "sprite_effect_shadow".into(),
            0x13 => "sprite_effect_cloaked".into(),
            0x14 => "sprite_effect_warped".into(),
            0x15 => "sprite_effect_deferred_cloak".into(),
            0x16 => "sprite_mapped_frag".into(),
            0x17 => "sprite_part_solid_frag".into(),
            0x18 => "deferred_sprite_part_solid".into(),
            0x19 => "deferred_sprite".into(),
            0x1a => "deferred_sprite_draw_effect".into(),
            0x1b => "blur".into(),
            0x1c => "mask".into(),
            0x1d => "bloom".into(),
            0x1e => "effect_mask".into(),
            0x1f => "deferred_effect_mask".into(),
            0x20 => "water".into(),
            0x21 => "water_deferred".into(),
            0x22 => "heat_distortion".into(),
            0x23 => "heat_distortion_deferred".into(),
            0x24 => "sprite_brighten_frag".into(),
            0x25 => "sprite_brighten_frag_deferred".into(),
            0x26 => "hp_bar".into(),
            0x27 => "hp_bar_deferred".into(),
            0x28 => "sprite_tile_draw_effect_color_draw".into(),
            0x29 => "sprite_tile_draw_effect_alpha_draw".into(),
            0x2a => "textured_frag_pylon_power".into(),
            _ => format!("pixel_{}", i),
        };
        dump_shader_set(&path.join(&name), binary, set)
            .with_context(|| format!("Dumping {}", name))?;
    }
    Ok(())
}

fn dump_shader_set<'e, Va: VirtualAddress, P: AsRef<Path>>(
    path: P,
    binary: &'e BinaryFile<Va>,
    addr: Va,
) -> Result<()> {
    let path = path.as_ref();
    create_dir(path)?;
    let shader_count = binary.read_u32(addr)?;
    let shader_addr = binary.read_address(addr + 4)?;
    for i in 0..shader_count {
        let addr = shader_addr + i * 0x10;
        let format = binary.read_u8(addr)?;
        let data = binary.read_address(addr + 0x8)?;
        let len = binary.read_u32(addr + 0xc)?;
        let slice = binary.slice_from_address(data, len)?;
        dump_shader(path, format, slice)
            .with_context(|| format!("Shader {} (format {:x}) @ addr {:?}", i, format, addr))?;
    }
    Ok(())
}

fn dump_shader(path: &Path, format: u8, data: &[u8]) -> Result<()> {
    if data.len() > 0x10_0000 {
        return Err(anyhow!("Unreasonably large shader ({} bytes)", data.len()));
    }
    if data.len() < 0x4 {
        return Err(anyhow!("Header too small"));
    }
    let wrap_format = LittleEndian::read_u32(&data[0x0..]);
    let shader_bin = match wrap_format {
        1 => {
            if data.len() < 0x14 {
                return Err(anyhow!("Header too small, expected {:x} got {:x}", 0x14, data.len()));
            }
            let len = LittleEndian::read_u32(&data[0x8..]);
            if len != data.len() as u32 - 0x14 {
                return Err(anyhow!("Unexpected shader len {:x}", len));
            }
            &data[0x14..]
        }
        3 => {
            if data.len() < 0x38 {
                return Err(anyhow!("Header too small, expected {:x} got {:x}", 0x38, data.len()));
            }
            let len = LittleEndian::read_u32(&data[0x30..]);
            let offset = LittleEndian::read_u32(&data[0x34..]);
            if offset != 4 || len != data.len() as u32 - 0x38 {
                return Err(anyhow!("Unexpected shader offset / len {:x} {:x}", offset, len));
            }
            &data[0x38..]
        }
        _ => {
            return Err(anyhow!("Invalid wrap format {:x}", wrap_format));
        }
    };
    let name = match format {
        0x0 => "dx_sm4".into(),
        0x4 => "dx_sm5".into(),
        0x1a => "metal".into(),
        _ => format!("format_{}", format),
    };
    let filename = path.join(&format!("{}.bin", name));
    let mut file = std::fs::File::create(&filename)
        .with_context(|| format!("Couldn't create {}", filename.display()))?;
    file.write_all(shader_bin).context("Writing shader")?;
    if matches!(format, 0 | 4) {
        d3d_disassemble(path, &name, shader_bin)?;
    }
    Ok(())
}

fn d3d_disassemble(path: &Path, name: &str, data: &[u8]) -> Result<()> {
    use winapi::um::d3dcompiler::D3DDisassemble;

    let filename = path.join(&format!("{}.asm", name));
    let mut file = std::fs::File::create(&filename)
        .with_context(|| format!("Couldn't create {}", filename.display()))?;

    unsafe {
        let mut blob = std::ptr::null_mut();
        let error = D3DDisassemble(
            data.as_ptr() as *const _,
            data.len(),
            0,
            b"\0".as_ptr() as *const _,
            &mut blob,
        );
        if error != 0 {
            return Err(io::Error::from_raw_os_error(error).into());
        }
        scopeguard::defer! {
            (*blob).Release();
        }
        let slice = std::slice::from_raw_parts(
            (*blob).GetBufferPointer() as *const u8,
            (*blob).GetBufferSize(),
        );
        file.write_all(slice)?;
    }
    Ok(())
}

fn dump_vtables<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    analysis: &mut Analysis<'e, E>,
) {
    let vtables = analysis.vtables();
    println!("{} vtables", vtables.len());
    for vtable in vtables {
        let name = binary.read_address(vtable - E::VirtualAddress::SIZE).ok()
            .and_then(|x| binary.read_address(x + 0xc).ok())
            .map(|x| x + 8)
            .and_then(|x| {
                let section = binary.section_by_addr(x)?;
                let relative = x.as_u64() - section.virtual_address.as_u64();
                let slice = section.data.get(relative as usize..)?;
                let end = slice.iter().position(|&x| x == 0)?;
                Some(&slice[..end])
            })
            .and_then(|name_u8| std::str::from_utf8(name_u8).ok());
        if let Some(name) = name {
            println!("{}: {:?}", name, vtable);
        }
    }
}
