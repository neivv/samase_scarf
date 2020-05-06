extern crate fern;
extern crate log;
extern crate samase_scarf;
extern crate scarf;

use samase_scarf::DatType;

fn format_op_operand(op: Option<scarf::Operand>) -> String {
    op.as_ref().map(|x| x.to_string()).unwrap_or_else(|| "None".into())
}

fn main() {
    init_stdout_log();
    let start_time = ::std::time::Instant::now();
    let exe = ::std::env::args_os().nth(1).unwrap();
    let mut binary = scarf::parse(&exe).unwrap();
    let relocs = scarf::analysis::find_relocs::<scarf::ExecutionStateX86<'_>>(&binary).unwrap();
    binary.set_relocs(relocs);
    let ctx = &scarf::OperandContext::new();
    let mut analysis = samase_scarf::Analysis::<scarf::ExecutionStateX86<'_>>::new(&binary, ctx);

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

    let init_units = analysis.init_units();
    println!("init_units: {:?}", init_units);
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
