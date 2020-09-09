extern crate fern;
extern crate log;
extern crate samase_scarf;
extern crate scarf;

use std::path::Path;

use scarf::{Operand, OperandType, VirtualAddress, ExecutionStateX86, OperandContext, OperandCtx};
use scarf::operand::Register;
use scarf::exec_state::VirtualAddress as VirtualAddressTrait;
use samase_scarf::DatType;

#[test]
fn everything_1207() {
    test(Path::new("1207.exe"));
}

#[test]
fn everything_1208() {
    test_with_extra_checks(Path::new("1208.exe"), |ctx, analysis| {
        let sprite_array = analysis.sprite_array().unwrap().0;
        assert_eq!(sprite_array, ctx.constant(0x00E7E820));
        let init_sprites = analysis.init_sprites().unwrap();
        assert_eq!(init_sprites.0, 0x00666040);
        let serialize = analysis.serialize_sprites().unwrap();
        assert_eq!(serialize.0, 0x00666900);

        assert_eq!(analysis.grpwire_grp().unwrap(), ctx.mem32(ctx.constant(0x113e9bc)));
        assert_eq!(analysis.tranwire_grp().unwrap(), ctx.mem32(ctx.constant(0x113e9b8)));
        assert_eq!(analysis.grpwire_ddsgrp().unwrap(), ctx.constant(0x113e960));
        assert_eq!(analysis.tranwire_ddsgrp().unwrap(), ctx.constant(0x113e96c));
        assert_eq!(analysis.status_screen().unwrap(), ctx.mem32(ctx.constant(0x113e9c0)));
        assert_eq!(analysis.status_screen_event_handler().unwrap().0, 0x00813760);
        // This is actually only address of the grp on old versions like 1208;
        // the ddsgrp set doesn't exist here.
        assert_eq!(analysis.wirefram_ddsgrp().unwrap(), ctx.constant(0x113f5d0));

        assert_eq!(analysis.trigger_conditions().unwrap().0, 0x00DC8BB0);
        assert_eq!(analysis.trigger_actions().unwrap().0, 0x00DC8AC0);
    });
}

#[test]
fn everything_1209() {
    test(Path::new("1209.exe"));
}

#[test]
fn everything_1209b() {
    test_with_extra_checks(Path::new("1209b.exe"), |ctx, analysis| {
        let ais = analysis.aiscript_hook();
        let ais = (*ais).as_ref().unwrap();
        assert_eq!(ais.opcode_operand.if_register(), Some(Register(0)));
        assert_eq!(ais.switch_loop_address.0, 0x00607ED0);
        assert_eq!(ais.return_address.0, 0x00608F4F);

        let sel = analysis.select_map_entry();
        assert_eq!(sel.select_map_entry.unwrap().0, 0x008A1ED0);
        assert_eq!(sel.is_multiplayer.unwrap(), ctx.mem8(ctx.constant(0x1036D20)));
    });
}

#[test]
fn everything_12010() {
    test(Path::new("12010.exe"));
}

#[test]
fn everything_12011() {
    test(Path::new("12011.exe"));
}

#[test]
fn everything_12011b() {
    test_with_extra_checks(Path::new("12011b.exe"), |ctx, analysis| {
        let active_hidden = analysis.active_hidden_units();
        assert_eq!(active_hidden.first_active_unit.unwrap(), ctx.mem32(ctx.constant(0xf240ac)));
        assert_eq!(active_hidden.first_hidden_unit.unwrap(), ctx.mem32(ctx.constant(0xf240c4)));
        let order_issuing = analysis.order_issuing();
        assert_eq!(order_issuing.prepare_issue_order.unwrap().0, 0x006A8FB0);
        assert_eq!(order_issuing.do_next_queued_order.unwrap().0, 0x006A96A0);
    });
}

#[test]
fn everything_1210() {
    test_with_extra_checks(Path::new("1210.exe"), |ctx, analysis| {
        let limits = analysis.limits();
        assert_eq!(limits.set_limits.unwrap().0, 0x005d85a0);
        assert!(limits.arrays[0].iter().any(|x| *x == (ctx.constant(0xd522ec), 0, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xd62e38), 0, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xd653ac), 1, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xd653bc), 0, 0)));
        assert!(limits.arrays[2].iter().any(|x| *x == (ctx.constant(0xd6375c), 0, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd637d4), 1, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd637e0), 1, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd4b020), 0, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd637a8), 0, 2)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd637b4), 0, 2)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xd63830), 0, 0)));
        assert!(limits.arrays[4].iter().any(|x| *x == (ctx.constant(0xd4b02c), 0, 0)));
        assert!(limits.arrays[6].iter().any(|x| *x == (ctx.constant(0xd6376c), 0, 0)));
    });
}

#[test]
fn everything_1210b() {
    test_with_extra_checks(Path::new("1210b.exe"), |ctx, analysis| {
        let net_players = analysis.net_players();
        assert_eq!(net_players.init_net_player.unwrap().0, 0x006F28E0);
        assert_eq!(net_players.net_players.as_ref().unwrap().0, ctx.constant(0x00F31988));

        assert_eq!(analysis.tooltip_draw_func().unwrap(), ctx.mem32(ctx.constant(0xd49148)));
        assert_eq!(analysis.current_tooltip_ctrl().unwrap(), ctx.mem32(ctx.constant(0xd4914c)));
        assert_eq!(analysis.layout_draw_text().unwrap().0, 0x008d5fd0);

        assert_eq!(analysis.smem_alloc().unwrap().0, 0x0089ead0);
        assert_eq!(analysis.smem_free().unwrap().0, 0x0089eb10);
    });
}

#[test]
fn everything_1211() {
    test_with_extra_checks(Path::new("1211.exe"), |_ctx, analysis| {
        let ais = analysis.aiscript_hook();
        let ais = (*ais).as_ref().unwrap();
        assert_eq!(ais.opcode_operand.if_register(), Some(Register(0)));
        assert_eq!(ais.script_operand_at_switch.if_register(), Some(Register(6)));
        assert_eq!(ais.op_limit_hook_begin.0, 0x007134EB);
        assert_eq!(ais.op_limit_hook_end.0, 0x007134FA);
        assert_eq!(ais.switch_loop_address.0, 0x00714EF9);
    });
}

#[test]
fn everything_1211b() {
    test_with_extra_checks(Path::new("1211b.exe"), |ctx, analysis| {
        let commands = analysis.process_commands();
        assert_eq!(commands.process_commands.unwrap().0, 0x0072D560);
        assert_eq!(commands.storm_command_user.unwrap(), ctx.mem32(ctx.constant(0x00D61584)));
        assert_eq!(
            commands.switch.as_ref().unwrap().indirection.unwrap() -
                commands.switch.as_ref().unwrap().offset,
            VirtualAddress(0x00731270) - 5
        );

        let print = analysis.print_text();
        assert_eq!(print.unwrap().0, 0x007044C0);
        let step_order = analysis.step_order();
        assert_eq!(step_order.unwrap().0, 0x005DBC10);
        let hidden = analysis.step_order_hidden();
        assert_eq!(
            hidden[0],
            samase_scarf::StepOrderHiddenHook::Separate(VirtualAddress(0x005DC610))
        );

        let units_dat = analysis.dat(DatType::Units).unwrap();
        assert_eq!(units_dat.address, ctx.constant(0x00D584F8));
        let orders_dat = analysis.dat(DatType::Orders).unwrap();
        assert_eq!(orders_dat.address, ctx.constant(0x00D58168));
        let secondary_order = analysis.step_secondary_order();
        assert_eq!(
            secondary_order[0],
            samase_scarf::SecondaryOrderHook::Separate(VirtualAddress(0x005dbb00))
        );
    });
}

#[test]
fn everything_1212() {
    test_with_extra_checks(Path::new("1212.exe"), |ctx, analysis| {
        let commands = analysis.process_lobby_commands();
        assert_eq!(commands.unwrap().0, 0x006CAE40);
        let send_command = analysis.send_command();
        assert_eq!(send_command.unwrap().0, 0x006D1880);
        let players = analysis.players().unwrap();
        let val = ctx.xor(
            ctx.add(
                ctx.constant(0x9be5b25d),
                ctx.mul(
                    ctx.mem32(ctx.constant(0xd1775e)),
                    ctx.constant(2),
                ),
            ),
            ctx.mem32(ctx.constant(0xf25830)),
        );
        assert_eq!(players, val);

        let iscript = analysis.step_iscript();
        assert_eq!(iscript.step_fn.unwrap().0, 0x0054a250);
        assert_eq!(iscript.script_operand_at_switch.unwrap(), ctx.register(6));
        assert_eq!(iscript.iscript_bin.unwrap(), ctx.mem32(ctx.constant(0xd35994)));
    });
}

#[test]
fn everything_1212b() {
    test_with_extra_checks(Path::new("1212b.exe"), |_ctx, analysis| {
        let commands = analysis.process_commands();
        assert_eq!(commands.process_commands.unwrap().0, 0x0069ca80);
    })
}

#[test]
fn everything_1213() {
    test_with_extra_checks(Path::new("1213.exe"), |ctx, analysis| {
        let step_order = analysis.step_order();
        assert_eq!(step_order.unwrap().0, 0x0058E330);
        let secondary_order = analysis.step_secondary_order();
        assert_eq!(secondary_order[0], samase_scarf::SecondaryOrderHook::Inlined {
            entry: VirtualAddress(0x0058f7c5),
            exit: VirtualAddress(0x0058f86e),
            unit: ctx.register(6),
        });

        assert_eq!(analysis.smem_alloc().unwrap().0, 0x0083ee80);
        assert_eq!(analysis.smem_free().unwrap().0, 0x0083eec0);
        assert_eq!(analysis.cmdicons_ddsgrp().unwrap(), ctx.constant(0x0EC7CAC));

        let mouse_xy = analysis.mouse_xy();
        assert_eq!(mouse_xy.x_var.unwrap(), ctx.mem16(ctx.constant(0xea9910)));
        assert_eq!(mouse_xy.y_var.unwrap(), ctx.mem16(ctx.constant(0xea9914)));
    })
}

#[test]
fn everything_1213b() {
    test_with_extra_checks(Path::new("1213b.exe"), |ctx, analysis| {
        let secondary_order = analysis.step_secondary_order();
        assert_eq!(secondary_order[0], samase_scarf::SecondaryOrderHook::Inlined {
            entry: VirtualAddress(0x005999e5),
            exit: VirtualAddress(0x00599a8e),
            unit: ctx.register(6),
        });
        let commands = analysis.process_commands();
        assert_eq!(commands.process_commands.unwrap().0, 0x00696d80);

        let init_game = analysis.init_game();
        assert_eq!(init_game.init_game.unwrap().0, 0x00643460);
        assert_eq!(init_game.loaded_save.unwrap(), ctx.mem32(ctx.constant(0x00c666dc)));

        let command_user = analysis.command_user().unwrap();
        assert_eq!(command_user, ctx.mem32(ctx.constant(0x00c65de4)));

        let selections = analysis.selections();
        assert_eq!(
            selections.unique_command_user.unwrap(),
            ctx.mem32(ctx.constant(0x00c65de8))
        );
        assert_eq!(selections.selections.unwrap(), ctx.constant(0x00eb4d90));

        let is_replay = analysis.is_replay().unwrap();
        assert_eq!(is_replay, ctx.mem32(ctx.constant(0x00ea9940)));

        let units = analysis.units().unwrap();
        assert_eq!(units, ctx.mem32(ctx.constant(0x00CBDB8C)));

        let rclick = analysis.game_screen_rclick();
        assert_eq!(rclick.game_screen_rclick.unwrap().0, 0x006b2400);
        assert_eq!(rclick.client_selection.unwrap(), ctx.constant(0x00ec3750));
    })
}

#[test]
fn everything_1214() {
    test_with_extra_checks(Path::new("1214.exe"), |ctx, analysis| {
        let script = analysis.first_ai_script().unwrap();
        assert_eq!(script, ctx.mem32(ctx.constant(0x00cee4e8)));
    })
}

#[test]
fn everything_1214b() {
    test_with_extra_checks(Path::new("1214b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1214c() {
    test_with_extra_checks(Path::new("1214c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215() {
    test_with_extra_checks(Path::new("1215.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215b() {
    test_with_extra_checks(Path::new("1215b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215c() {
    test_with_extra_checks(Path::new("1215c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215d() {
    test_with_extra_checks(Path::new("1215d.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215e() {
    test_with_extra_checks(Path::new("1215e.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215f() {
    test_with_extra_checks(Path::new("1215f.exe"), |ctx, analysis| {
        let guard_ai = analysis.first_guard_ai().unwrap();
        assert_eq!(guard_ai, ctx.constant(0x0D258A8));

        let ais = analysis.aiscript_hook();
        let ais = (*ais).as_ref().unwrap();
        assert_eq!(ais.return_address.0, 0x005BCB3C);

        let pathing = analysis.pathing().unwrap();
        assert_eq!(pathing, ctx.mem32(ctx.constant(0x00EDFE30)));
    })
}

#[test]
fn everything_1215g() {
    test_with_extra_checks(Path::new("1215g.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215h() {
    test_with_extra_checks(Path::new("1215h.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1215i() {
    test_with_extra_checks(Path::new("1215i.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220() {
    test_with_extra_checks(Path::new("1220.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220b() {
    test_with_extra_checks(Path::new("1220b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220c() {
    test_with_extra_checks(Path::new("1220c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220d() {
    test_with_extra_checks(Path::new("1220d.exe"), |ctx, analysis| {
        let guard_ai = analysis.player_ai_towns().unwrap();
        assert_eq!(guard_ai, ctx.constant(0x0DFAE80));
    })
}

#[test]
fn everything_1220e() {
    test_with_extra_checks(Path::new("1220e.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220f() {
    test_with_extra_checks(Path::new("1220f.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220g() {
    test_with_extra_checks(Path::new("1220g.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1220h() {
    test_with_extra_checks(Path::new("1220h.exe"), |ctx, analysis| {
        let iscript = analysis.step_iscript();
        assert_eq!(iscript.step_fn.unwrap().0, 0x005474C0);
        assert_eq!(iscript.script_operand_at_switch.unwrap(), ctx.register(6));
    })
}

#[test]
fn everything_1221() {
    test_with_extra_checks(Path::new("1221.exe"), |ctx, analysis| {
        let guard_ai = analysis.first_guard_ai().unwrap();
        assert_eq!(guard_ai, ctx.constant(0x00ee41b8));

        let open_file = analysis.file_hook();
        assert_eq!(open_file[0].0, 0x00527860);

        let init_map_from_path = analysis.init_map_from_path().unwrap();
        assert_eq!(init_map_from_path.0, 0x006D7C30);
        let choose_snp = analysis.choose_snp().unwrap();
        assert_eq!(choose_snp.0, 0x006fef60);

        let start = analysis.single_player_start();
        assert_eq!(start.skins.unwrap(), ctx.constant(0x00E55158));
        assert_eq!(start.player_skins.unwrap(), ctx.constant(0x010A52A0));

        let sel = analysis.select_map_entry();
        assert_eq!(sel.select_map_entry.unwrap().0, 0x005E7350);
        assert_eq!(sel.is_multiplayer.unwrap(), ctx.mem8(ctx.constant(0x010A5138)));

        let load = analysis.load_images().unwrap();
        assert_eq!(load.0, 0x0054D1E0);

        assert_eq!(analysis.ai_step_region().unwrap().0, 0x00619800);
    })
}

#[test]
fn everything_1221b() {
    test_with_extra_checks(Path::new("1221b.exe"), |ctx, analysis| {
        let init = analysis.init_game_network().unwrap();
        assert_eq!(init.0, 0x006ed550);

        let lobby_state = analysis.lobby_state();
        assert_eq!(lobby_state.unwrap(), ctx.mem8(ctx.constant(0x01060fc5)));
        let init = analysis.init_storm_networking().init_storm_networking.unwrap();
        assert_eq!(init.0, 0x006F0BB0);
    })
}

#[test]
fn everything_1221c() {
    test_with_extra_checks(Path::new("1221c.exe"), |ctx, analysis| {
        let iscript = analysis.step_iscript();
        assert_eq!(iscript.step_fn.unwrap().0, 0x00546760);
        assert_eq!(iscript.script_operand_at_switch.unwrap(), ctx.register(7));

        let sprites = analysis.sprites();
        assert_eq!(sprites.sprite_hlines.unwrap(), ctx.constant(0x00e7ccc0));
        assert_eq!(sprites.sprite_hlines_end.unwrap(), ctx.constant(0x00e7d0c0));
        assert_eq!(sprites.first_free_sprite.unwrap(), ctx.constant(0x00e7c9a0));
        assert_eq!(sprites.last_free_sprite.unwrap(), ctx.constant(0x00e7c9a4));
        assert_eq!(sprites.first_lone.unwrap(), ctx.constant(0x00e7d610));
        assert_eq!(sprites.last_lone.unwrap(), ctx.constant(0x00e7d614));
        assert_eq!(sprites.first_free_lone.unwrap(), ctx.constant(0x00e7d608));
        assert_eq!(sprites.last_free_lone.unwrap(), ctx.constant(0x00e7d60c));
    })
}

#[test]
fn everything_1222() {
    test_with_extra_checks(Path::new("1222.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1222b() {
    test_with_extra_checks(Path::new("1222b.exe"), |ctx, analysis| {
        let pathing = analysis.pathing().unwrap();
        assert_eq!(pathing, ctx.mem32(ctx.constant(0x00ff1274)));
    })
}

#[test]
fn everything_1222c() {
    test_with_extra_checks(Path::new("1222c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1222d() {
    test_with_extra_checks(Path::new("1222d.exe"), |ctx, analysis| {
        let init_game = analysis.init_game();
        assert_eq!(init_game.init_game.unwrap().0, 0x00694330);
        assert_eq!(init_game.loaded_save.unwrap(), ctx.mem32(ctx.constant(0x00da61cc)));
    })
}

#[test]
fn everything_1223() {
    test_with_extra_checks(Path::new("1223.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1223b() {
    test_with_extra_checks(Path::new("1223b.exe"), |ctx, analysis| {
        let towns = analysis.player_ai_towns().unwrap();
        assert_eq!(towns, ctx.constant(0xe2fc68));
    })
}

#[test]
fn everything_1223c() {
    test_with_extra_checks(Path::new("1223c.exe"), |ctx, analysis| {
        let map_tile_flags = analysis.map_tile_flags();
        assert_eq!(map_tile_flags.map_tile_flags.unwrap(), ctx.mem32(ctx.constant(0xe47004)));
    })
}

#[test]
fn everything_1223d() {
    test_with_extra_checks(Path::new("1223d.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1223e() {
    test_with_extra_checks(Path::new("1223e.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1223_ptr1() {
    test_with_extra_checks(Path::new("1223_ptr1.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1224() {
    test_with_extra_checks(Path::new("1224.exe"), |ctx, analysis| {
        let players = analysis.players().unwrap();
        let val = ctx.xor(
            ctx.xor(
                ctx.constant(0x1c7e5fe2),
                ctx.mem32(ctx.constant(0x1020c70)),
            ),
            ctx.mem32(ctx.constant(0xe0770d)),
        );
        assert_eq!(players, val);

        let sprites = analysis.sprites();
        assert_eq!(sprites.sprite_hlines.unwrap(), ctx.constant(0x00e287e8));
        assert_eq!(sprites.sprite_hlines_end.unwrap(), ctx.constant(0x00e28be8));

        let draw_image = analysis.draw_image().unwrap();
        assert_eq!(draw_image.0, 0x0055CDA0);
        let vtables = analysis.renderer_vtables();
        assert_eq!(vtables.len(), 2);
        assert!(vtables.iter().any(|x| x.0 == 0xca4b94));
        assert!(vtables.iter().any(|x| x.0 == 0xca4b28));

        let local_player_id = analysis.local_player_id().unwrap();
        assert_eq!(local_player_id, ctx.mem32(ctx.constant(0xdc7940)));
    })
}

#[test]
fn everything_1224b() {
    test_with_extra_checks(Path::new("1224b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1224c() {
    test_with_extra_checks(Path::new("1224c.exe"), |ctx, analysis| {
        let iscript = analysis.step_iscript();
        assert_eq!(iscript.step_fn.unwrap().0, 0x005409e0);
        assert_eq!(iscript.script_operand_at_switch.unwrap(), ctx.register(6));
        assert_eq!(iscript.iscript_bin.unwrap(), ctx.mem32(ctx.constant(0xde75c4)));
        assert_eq!(iscript.opcode_check.unwrap(), (VirtualAddress(0x00540A2A), 2));
        let bullets = analysis.bullet_creation();
        assert_eq!(bullets.first_active_bullet.unwrap(), ctx.constant(0xde60c4));
        assert_eq!(bullets.last_active_bullet.unwrap(), ctx.constant(0xde60c8));
        assert_eq!(bullets.first_free_bullet.unwrap(), ctx.constant(0xde6094));
        assert_eq!(bullets.last_free_bullet.unwrap(), ctx.constant(0xde6098));
        assert_eq!(bullets.create_bullet.unwrap().0, 0x531f00);
        assert_eq!(bullets.active_iscript_unit.unwrap(), ctx.mem32(ctx.constant(0xde7190)));

        let net_players = analysis.net_players();
        assert_eq!(net_players.init_net_player.unwrap().0, 0x00721680);
        assert_eq!(net_players.net_players.unwrap().0, ctx.constant(0x00FED8D8));
        let play_smk = analysis.play_smk();
        assert_eq!(play_smk.unwrap().0, 0x00739200);
        let game_init = analysis.game_init();
        assert_eq!(game_init.sc_main.unwrap().0, 0x006e4350);
        assert_eq!(game_init.mainmenu_entry_hook.unwrap().0, 0x006e51ae);
        assert_eq!(game_init.game_loop.unwrap().0, 0x0006e5450);
        assert_eq!(game_init.scmain_state.unwrap(), ctx.mem32(ctx.constant(0x00FC7FE8)));

        assert_eq!(analysis.font_cache_render_ascii().unwrap().0, 0x008FCFF0);
        assert_eq!(analysis.ttf_cache_character().unwrap().0, 0x009036B0);
        assert_eq!(analysis.ttf_render_sdf().unwrap().0, 0x00907980);
    })
}

#[test]
fn everything_1230a() {
    test_with_extra_checks(Path::new("1230a.exe"), |ctx, analysis| {
        let secondary_order = analysis.step_secondary_order();
        assert_eq!(secondary_order[0], samase_scarf::SecondaryOrderHook::Inlined {
            entry: VirtualAddress(0x005b6c80),
            exit: VirtualAddress(0x005b6d07),
            unit: ctx.register(6),
        });
        let active_hidden = analysis.active_hidden_units();
        assert_eq!(active_hidden.first_active_unit.unwrap(), ctx.mem32(ctx.constant(0xddf144)));
        assert_eq!(active_hidden.first_hidden_unit.unwrap(), ctx.mem32(ctx.constant(0xddf154)));
    })
}

#[test]
fn everything_1230b() {
    test_with_extra_checks(Path::new("1230b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1230c() {
    test_with_extra_checks(Path::new("1230c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1230d() {
    test_with_extra_checks(Path::new("1230d.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1230e() {
    test_with_extra_checks(Path::new("1230e.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1230f() {
    test_with_extra_checks(Path::new("1230f.exe"), |ctx, analysis| {
        let add_overlay_iscript = analysis.add_overlay_iscript();
        assert_eq!(add_overlay_iscript.unwrap().0, 0x00559350);
        let secondary_order = analysis.step_secondary_order();
        assert_eq!(secondary_order[0], samase_scarf::SecondaryOrderHook::Inlined {
            entry: VirtualAddress(0x005b66c0),
            exit: VirtualAddress(0x005b6747),
            unit: ctx.register(6),
        });
    })
}

#[test]
fn everything_1230g() {
    test_with_extra_checks(Path::new("1230g.exe"), |ctx, analysis| {
        let campaigns = analysis.campaigns();
        assert_eq!(campaigns.unwrap(), ctx.constant(0x00DB2138));
        let run_dialog = analysis.run_dialog();
        assert_eq!(run_dialog.unwrap().0, 0x00904F30);
        let ai_update_attack_target = analysis.ai_update_attack_target();
        assert_eq!(ai_update_attack_target.unwrap().0, 0x00581090);
        let map_tile_flags = analysis.map_tile_flags();
        assert_eq!(map_tile_flags.update_visibility_point.unwrap().0, 0x00565E20);
        let sprites = analysis.sprites();
        assert_eq!(sprites.create_lone_sprite.unwrap().0, 0x00565A70);
    })
}

#[test]
fn everything_1230h() {
    test_with_extra_checks(Path::new("1230h.exe"), |ctx, analysis| {
        let step_order_hidden = analysis.step_order_hidden();
        assert_eq!(step_order_hidden[0], samase_scarf::StepOrderHiddenHook::Inlined {
            entry: VirtualAddress(0x005af466),
            exit: VirtualAddress(0x005af555),
            unit: ctx.register(6),
        });
    })
}

#[test]
fn everything_1230i() {
    test_with_extra_checks(Path::new("1230i.exe"), |ctx, analysis| {
        let is_outside_game_screen = analysis.is_outside_game_screen();
        assert_eq!(is_outside_game_screen.unwrap().0, 0x0065E7D0);

        let coords = analysis.game_coord_conversion();
        assert_eq!(coords.screen_x.unwrap(), ctx.mem32(ctx.constant(0x00e4caf4)));
        assert_eq!(coords.screen_y.unwrap(), ctx.mem32(ctx.constant(0x00e4caf8)));
        assert_eq!(coords.scale.unwrap(), ctx.mem32(ctx.constant(0x00d77940)));
    })
}

#[test]
fn everything_1230j() {
    test_with_extra_checks(Path::new("1230j.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1231a() {
    test_with_extra_checks(Path::new("1231a.exe"), |ctx, analysis| {
        let commands = analysis.process_lobby_commands();
        assert_eq!(commands.unwrap().0, 0x00703c50);
        let fow = analysis.fow_sprites();
        assert_eq!(fow.first_active.unwrap(), ctx.constant(0x0E32110));
        assert_eq!(fow.last_active.unwrap(), ctx.constant(0x0E32114));
        assert_eq!(fow.first_free.unwrap(), ctx.constant(0x0E32108));
        assert_eq!(fow.last_free.unwrap(), ctx.constant(0x0E3210C));

        let rng = analysis.rng();
        assert_eq!(rng.seed.unwrap(), ctx.mem32(ctx.constant(0x1030770)));
        assert_eq!(rng.enable.unwrap(), ctx.mem32(ctx.constant(0x1030B80)));
    })
}

#[test]
fn everything_1232a() {
    test_with_extra_checks(Path::new("1232a.exe"), |_ctx, analysis| {
        let results = analysis.firegraft_addresses();
        assert_eq!(results.unit_status_funcs[0].0, 0x00E41128);
        let run_dialog = analysis.run_dialog();
        assert_eq!(run_dialog.unwrap().0, 0x0097cfc0);
        let game_init = analysis.game_init();
        assert_eq!(game_init.mainmenu_entry_hook.unwrap().0, 0x00708C4E);
    })
}

#[test]
fn everything_1232b() {
    test_with_extra_checks(Path::new("1232b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1232c() {
    test_with_extra_checks(Path::new("1232c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1232d() {
    test_with_extra_checks(Path::new("1232d.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1232e() {
    test_with_extra_checks(Path::new("1232e.exe"), |ctx, analysis| {
        let init_map_from_path = analysis.init_map_from_path().unwrap();
        assert_eq!(init_map_from_path.0, 0x006F3030);
        let choose_snp = analysis.choose_snp().unwrap();
        assert_eq!(choose_snp.0, 0x00716C20);

        let start = analysis.single_player_start();
        assert_eq!(start.single_player_start.unwrap().0, 0x00714870);
        assert_eq!(start.local_storm_player_id.unwrap(), ctx.mem32(ctx.constant(0xdff54c)));
        assert_eq!(start.local_unique_player_id.unwrap(), ctx.mem32(ctx.constant(0xdff548)));
        assert_eq!(start.net_player_to_game.unwrap(), ctx.constant(0x106f6a8));
        assert_eq!(start.net_player_to_unique.unwrap(), ctx.constant(0x106f678));
        assert_eq!(start.game_data.unwrap(), ctx.constant(0x1070ce0));
        assert_eq!(start.skins.unwrap(), ctx.constant(0x00E003A0));
        assert_eq!(start.player_skins.unwrap(), ctx.constant(0x0106F6E0));

        let sel = analysis.select_map_entry();
        assert_eq!(sel.select_map_entry.unwrap().0, 0x005FD7F0);
        assert_eq!(sel.is_multiplayer.unwrap(), ctx.mem8(ctx.constant(0x0106F57C)));

        let load = analysis.load_images().unwrap();
        assert_eq!(load.0, 0x00566710);
        let loaded = analysis.images_loaded().unwrap();
        assert_eq!(loaded, ctx.mem8(ctx.constant(0x0104C60A)));
        let local_player_name = analysis.local_player_name().unwrap();
        assert_eq!(local_player_name, ctx.constant(0x106f5b8));

        let step = analysis.step_network();
        assert_eq!(step.step_network.unwrap().0, 0x00722ce0);
        assert_eq!(step.receive_storm_turns.unwrap().0, 0x00713370);
        let val = ctx.and_const(
            ctx.xor(
                ctx.sub(
                    ctx.constant(0x1d3fbab2),
                    ctx.mem32(ctx.constant(0xe5164a)),
                ),
                ctx.mem32(ctx.constant(0x1049cf4)),
            ),
            0xffff_ffff,
        );
        assert_eq!(step.menu_screen_id.clone().unwrap(), val);
        assert_eq!(step.net_player_flags.unwrap(), ctx.constant(0x0106F588));
        assert_eq!(step.player_turns.unwrap(), ctx.constant(0x01071118));
        assert_eq!(step.player_turns_size.unwrap(), ctx.constant(0x01071148));
        assert_eq!(step.network_ready.unwrap(), ctx.mem8(ctx.constant(0x0106F57D)));

        let init = analysis.init_game_network().unwrap();
        assert_eq!(init.0, 0x00713cb0);

        let snp_definitions = analysis.snp_definitions().unwrap();
        assert_eq!(snp_definitions.snp_definitions, ctx.constant(0x00E065E0));

        let lobby_state = analysis.lobby_state();
        assert_eq!(lobby_state.unwrap(), ctx.mem8(ctx.constant(0x0106f475)));
        let init = analysis.init_storm_networking().init_storm_networking.unwrap();
        assert_eq!(init.0, 0x00716F70);
    })
}

#[test]
fn everything_1233a() {
    test_with_extra_checks(Path::new("1233a.exe"), |ctx, analysis| {
        let open_file = analysis.file_hook();
        assert_eq!(open_file[0].0, 0x00544720);

        let init = analysis.init_storm_networking();
        let init_storm = init.init_storm_networking.unwrap();
        assert_eq!(init_storm.0, 0x0073b2e0);
        let load_snps = init.load_snp_list.unwrap();
        assert_eq!(load_snps.0, 0x007A4590);

        let draw_cursor_marker = analysis.draw_cursor_marker();
        assert_eq!(draw_cursor_marker.unwrap(), ctx.mem8(ctx.constant(0x00ee6c21)));

        let misc = analysis.misc_clientside();
        assert_eq!(misc.is_paused.unwrap(), ctx.mem32(ctx.constant(0x00eed95c)));
        assert_eq!(
            misc.is_placing_building.unwrap(),
            ctx.mem32(ctx.constant(0x010e748c)),
        );
        assert_eq!(misc.is_targeting.unwrap(), ctx.mem8(ctx.constant(0x010f54f2)));
    })
}

#[test]
fn everything_1233b() {
    test_with_extra_checks(Path::new("1233b.exe"), |_ctx ,analysis| {
        let spawn_dialog = analysis.spawn_dialog();
        assert_eq!(spawn_dialog.unwrap().0, 0x0097BB60);

        let unit_creation = analysis.unit_creation();
        assert_eq!(unit_creation.create_unit.unwrap().0, 0x005A0720);
        assert_eq!(unit_creation.finish_unit_pre.unwrap().0, 0x005A1110);
        assert_eq!(unit_creation.finish_unit_post.unwrap().0, 0x005A0E20);

        let init_rtl = analysis.init_real_time_lighting().unwrap();
        assert_eq!(init_rtl.0, 0x0056ACD0);
    })
}

#[test]
fn everything_1233c() {
    test_with_extra_checks(Path::new("1233c.exe"), |ctx, analysis| {
        let limits = analysis.limits();
        assert_eq!(limits.set_limits.unwrap().0, 0x00600c60);
        // Sprite array resizing got inlined so it may be a bit weird
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xeaa090), 0, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xeb1750), 1, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xeb1760), 0, 0)));
    })
}

#[test]
fn everything_1233d() {
    test_with_extra_checks(Path::new("1233d.exe"), |ctx, analysis| {
        let sprites = analysis.sprites();
        let (x, _, _) = sprites.sprite_x_position.unwrap();
        let (y, _, _) = sprites.sprite_y_position.unwrap();
        let x_low = ctx.and_const(x, 0xffff);
        let y_low = ctx.and_const(y, 0xffff);
        let low = ctx.and_const(
            ctx.xor(
                ctx.xor(
                    ctx.custom(0),
                    ctx.mem16(ctx.add_const(ctx.mem32(ctx.constant(0x30)), 0x10)),
                ),
                ctx.constant(0xb653),
            ),
            0xffff,
        );
        assert_eq!(x_low, low);
        assert_eq!(y_low, low);
        let x_high = ctx.and_const(ctx.rsh_const(x, 0x10), 0xffff);
        let y_high = ctx.and_const(ctx.rsh_const(y, 0x10), 0xffff);
        let high = ctx.xor(
            ctx.xor(
                ctx.and_const(
                    ctx.xor(
                        ctx.custom(0),
                        ctx.mem16(ctx.add_const(ctx.mem32(ctx.constant(0x30)), 0x10)),
                    ),
                    0xffff,
                ),
                ctx.and_const(
                    ctx.xor(
                        ctx.xor(
                            ctx.xor(
                                ctx.add_const(
                                    ctx.mul_const(
                                        ctx.custom(0),
                                        0x2,
                                    ),
                                    0x8800,
                                ),
                                ctx.mem16(ctx.add_const(ctx.mem32(ctx.constant(0x30)), 0x12)),
                            ),
                            ctx.mem16(ctx.add_const(ctx.mem32(ctx.constant(0x30)), 0x10)),
                        ),
                        ctx.xor(
                            ctx.mem16(ctx.constant(0xead6ab)),
                            ctx.mem16(ctx.constant(0xeada1d)),
                        ),
                    ),
                    0xffff,
                ),
            ),
            ctx.constant(0xf2a1),
        );
        assert_eq!(x_high, high);
        assert_eq!(y_high, high);
    })
}

#[test]
fn everything_1233e() {
    test_with_extra_checks(Path::new("1233e.exe"), |ctx ,analysis| {
        let rng = analysis.rng();
        assert_eq!(rng.seed.unwrap(), ctx.mem32(ctx.constant(0x10A11C0)));
        assert_eq!(rng.enable.unwrap(), ctx.mem32(ctx.constant(0x10A15D0)));

        let fonts = analysis.fonts();
        assert_eq!(fonts.unwrap(), ctx.constant(0x10D1A5C));
    })
}

#[test]
fn everything_1233f() {
    test_with_extra_checks(Path::new("1233f.exe"), |ctx, analysis| {
        let sprite_array = analysis.sprite_array().unwrap().0;
        assert_eq!(sprite_array, ctx.mem32(ctx.constant(0xeb6098)));
        let init_sprites = analysis.init_sprites().unwrap();
        assert_eq!(init_sprites.0, 0x0056C360);
        let serialize = analysis.serialize_sprites().unwrap();
        assert_eq!(serialize.0, 0x0056CE40);
        let deserialize = analysis.deserialize_sprites().unwrap();
        assert_eq!(deserialize.0, 0x0056C5B0);
        let limits = analysis.limits();
        assert_eq!(limits.set_limits.unwrap().0, 0x00601c20);
        assert!(limits.arrays[0].iter().any(|x| *x == (ctx.constant(0xea93d8), 0, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xeb6098), 0, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xebd758), 1, 0)));
        assert!(limits.arrays[1].iter().any(|x| *x == (ctx.constant(0xebd768), 0, 0)));
        assert!(limits.arrays[2].iter().any(|x| *x == (ctx.constant(0xeb69d4), 0, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xeb6b1c), 1, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xeb6b28), 1, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xeb6bc0), 0, 0)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xeb6a1c), 0, 2)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xeb6a28), 0, 2)));
        assert!(limits.arrays[3].iter().any(|x| *x == (ctx.constant(0xea7ef8), 0, 0)));
        assert!(limits.arrays[4].iter().any(|x| *x == (ctx.constant(0xea7f04), 0, 0)));
        assert!(limits.arrays[5].iter().any(|x| *x == (ctx.constant(0xeb5d74), 0, 0)));
        assert!(limits.arrays[6].iter().any(|x| *x == (ctx.constant(0xeb69e4), 0, 0)));

        assert_eq!(analysis.font_cache_render_ascii().unwrap().0, 0x0095d430);
        assert_eq!(analysis.ttf_cache_character().unwrap().0, 0x00963c40);
        assert_eq!(analysis.ttf_render_sdf().unwrap().0, 0x00968010);
        assert_eq!(analysis.ttf_malloc().unwrap().0, 0x00C2A08B);
    })
}

#[test]
fn everything_1233g() {
    test_with_extra_checks(Path::new("1233g.exe"), |_ctx, analysis| {
        let serialize = analysis.serialize_sprites().unwrap();
        assert_eq!(serialize.0, 0x0057F540);
        let deserialize = analysis.deserialize_sprites().unwrap();
        assert_eq!(deserialize.0, 0x0057E8C0);
        let join_game = analysis.join_game().unwrap();
        assert_eq!(join_game.0, 0x0089D2B0);
    })
}

#[test]
fn everything_1233h() {
    test_with_extra_checks(Path::new("1233h.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1233i() {
    test_with_extra_checks(Path::new("1233i.exe"), |ctx, analysis| {
        assert_eq!(analysis.tooltip_draw_func().unwrap(), ctx.mem32(ctx.constant(0xee926c)));
        assert_eq!(analysis.current_tooltip_ctrl().unwrap(), ctx.mem32(ctx.constant(0xee9270)));
        assert_eq!(analysis.graphic_layers().unwrap(), ctx.constant(0x1115f50));
        assert_eq!(analysis.layout_draw_text().unwrap().0, 0x977380);
        assert_eq!(analysis.draw_f10_menu_tooltip().unwrap().0, 0x007a0aa0);
        assert_eq!(analysis.draw_tooltip_layer().unwrap().0, 0x00607150);
        assert_eq!(analysis.draw_graphic_layers().unwrap().0, 0x009738B0);
    })
}

#[test]
fn everything_1234_ptr1() {
    test_with_extra_checks(Path::new("1234_ptr1.exe"), |_ctx, analysis| {
        let run_dialog = analysis.run_dialog();
        assert_eq!(run_dialog.unwrap().0, 0x00979000);
        let results = analysis.firegraft_addresses();
        assert_eq!(results.unit_status_funcs[0].0, 0x00f09ca8);
    })
}

#[test]
fn everything_1234a() {
    test_with_extra_checks(Path::new("1234a.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1234b() {
    test_with_extra_checks(Path::new("1234b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1234c() {
    test_with_extra_checks(Path::new("1234c.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1234d() {
    test_with_extra_checks(Path::new("1234d.exe"), |_ctx, analysis| {
        assert_eq!(analysis.ai_attack_prepare().unwrap().0, 0x006583A0);
        assert_eq!(analysis.ai_step_region().unwrap().0, 0x0065A590);
        let join_game = analysis.join_game().unwrap();
        assert_eq!(join_game.0, 0x0088B6A0);
        let snet_initialize_provider = analysis.snet_initialize_provider().unwrap();
        assert_eq!(snet_initialize_provider.0, 0x0079AE20);
    })
}

#[test]
fn everything_1235a() {
    test_with_extra_checks(Path::new("1235a.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1235b() {
    test_with_extra_checks(Path::new("1235b.exe"), |_ctx, analysis| {
        let load_dat = analysis.load_dat().unwrap();
        assert_eq!(load_dat.0, 0x006CAD30);
    })
}

#[test]
fn everything_1235c() {
    test_with_extra_checks(Path::new("1235c.exe"), |ctx, analysis| {
        let do_attack = analysis.do_attack().unwrap();
        assert_eq!(do_attack.0, 0x00593CB0);
        let do_attack_main = analysis.do_attack_main().unwrap();
        assert_eq!(do_attack_main.0, 0x00593A80);
        assert_eq!(analysis.last_bullet_spawner().unwrap(), ctx.mem32(ctx.constant(0xf823ac)));
    })
}

#[test]
fn everything_1235d() {
    test_with_extra_checks(Path::new("1235d.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1235e() {
    test_with_extra_checks(Path::new("1235e.exe"), |ctx, analysis| {
        assert_eq!(analysis.smem_alloc().unwrap().0, 0x0094d940);
        assert_eq!(analysis.smem_free().unwrap().0, 0x0094d980);
        assert_eq!(analysis.cmdicons_ddsgrp().unwrap(), ctx.constant(0x11b7960));
        assert_eq!(analysis.cmdbtns_ddsgrp().unwrap(), ctx.constant(0x11b7920));
        let mouse_xy = analysis.mouse_xy();
        assert_eq!(mouse_xy.x_func.unwrap().0, 0x006bf090);
        assert_eq!(mouse_xy.y_func.unwrap().0, 0x006bf0a0);
        assert_eq!(analysis.status_screen_mode().unwrap(), ctx.mem8(ctx.constant(0x11b7a0e)));
    })
}

#[test]
fn everything_1235f() {
    test_with_extra_checks(Path::new("1235f.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1235g() {
    test_with_extra_checks(Path::new("1235g.exe"), |ctx, analysis| {
        assert_eq!(analysis.check_unit_requirements().unwrap().0, 0x006627D0);
        assert_eq!(analysis.check_dat_requirements().unwrap().0, 0x00538f80);
        assert_eq!(analysis.dat_requirement_error().unwrap(), ctx.mem32(ctx.constant(0xffaad8)));
        assert_eq!(analysis.cheat_flags().unwrap(), ctx.mem32(ctx.constant(0x1180f74)));
        assert_eq!(analysis.unit_strength().unwrap(), ctx.constant(0xfe8998));

        assert_eq!(analysis.grpwire_grp().unwrap(), ctx.mem32(ctx.constant(0x11cc9a4)));
        assert_eq!(analysis.tranwire_grp().unwrap(), ctx.mem32(ctx.constant(0x11cc9a0)));
        assert_eq!(analysis.grpwire_ddsgrp().unwrap(), ctx.constant(0x11cc9ac));
        assert_eq!(analysis.tranwire_ddsgrp().unwrap(), ctx.constant(0x11cc9b8));
        assert_eq!(analysis.status_screen().unwrap(), ctx.mem32(ctx.constant(0x11cc9a8)));
        assert_eq!(analysis.status_screen_event_handler().unwrap().0, 0x00795590);
        assert_eq!(analysis.init_status_screen().unwrap().0, 0x00795810);
        assert_eq!(analysis.wirefram_ddsgrp().unwrap(), ctx.constant(0x11cd4d4));

        assert_eq!(analysis.trigger_conditions().unwrap().0, 0x00f1b0d8);
        assert_eq!(analysis.trigger_actions().unwrap().0, 0x00f1afe8);
    })
}

fn test(path: &Path) {
    test_with_extra_checks(path, |_, _| {});
}

fn test_with_extra_checks<F>(filename: &Path, f: F)
where F: for<'e> FnOnce(OperandCtx<'e>, &mut samase_scarf::Analysis<'e, ExecutionStateX86<'e>>),
{
    init_stdout_log();
    assert!(samase_scarf::test_assertions());
    let path = Path::new("tests/code_sections").join(filename);
    let mut binary = scarf::parse(path.as_ref()).unwrap();
    let relocs = scarf::analysis::find_relocs::<ExecutionStateX86<'_>>(&binary).unwrap();
    binary.set_relocs(relocs);
    let ctx = &OperandContext::new();
    let mut analysis = samase_scarf::Analysis::new(&binary, ctx);

    f(ctx, &mut analysis);
    test_nongeneric(filename, ctx, &binary, &mut analysis);
}

fn test_nongeneric<'e>(
    filename: &Path,
    ctx: OperandCtx<'e>,
    binary: &'e scarf::BinaryFile<VirtualAddress>,
    analysis: &mut samase_scarf::Analysis<'e, ExecutionStateX86<'e>>,
) {
    let results = analysis.file_hook();
    assert_eq!(results.len(), 1);
    let results = analysis.firegraft_addresses();
    assert_eq!(results.buttonsets.len(), 1);
    assert_eq!(results.unit_status_funcs.len(), 1);
    let filename_str = filename.file_stem().unwrap().to_str().unwrap();
    let minor_version = (&filename_str[1..3]).parse::<u32>().unwrap();
    let is_ptr = filename_str.contains("ptr");
    let (patch_version, revision) = if is_ptr {
        (!0u32, b'a')
    } else {
        if let Ok(o) = (&filename_str[3..]).parse::<u32>() {
            (o, b'a')
        } else {
            let &revision = filename_str.as_bytes().last().unwrap();
            ((&filename_str[3..filename_str.len() - 1]).parse::<u32>().unwrap(), revision)
        }
    };
    let extended_limits = minor_version >= 21;
    let new_codegen = minor_version > 21 || (minor_version == 21 && patch_version >= 2);
    let new_codegen2 = minor_version > 22 || (minor_version == 22 && patch_version >= 1);
    let new_codegen3 = minor_version > 22;
    if minor_version < 21 {
        assert_eq!(results.requirement_table_refs.units.len(), 13);
        assert_eq!(results.requirement_table_refs.upgrades.len(), 4);
        assert_eq!(results.requirement_table_refs.tech_use.len(), 4);
        assert_eq!(results.requirement_table_refs.tech_research.len(), 4);
        assert_eq!(results.requirement_table_refs.orders.len(), 4);
    } else if new_codegen3 {
        assert_eq!(results.requirement_table_refs.units.len(), 13);
        assert_eq!(results.requirement_table_refs.upgrades.len(), 5);
        assert_eq!(results.requirement_table_refs.tech_use.len(), 5);
        assert_eq!(results.requirement_table_refs.tech_research.len(), 5);
        assert_eq!(results.requirement_table_refs.orders.len(), 5);
    } else if new_codegen2 {
        // Assertions enabled
        assert_eq!(results.requirement_table_refs.units.len(), 15);
        assert_eq!(results.requirement_table_refs.upgrades.len(), 7);
        assert_eq!(results.requirement_table_refs.tech_use.len(), 7);
        assert_eq!(results.requirement_table_refs.tech_research.len(), 7);
        assert_eq!(results.requirement_table_refs.orders.len(), 7);
    } else {
        // Different compiler codegen caused one less ref for equivalent code
        if new_codegen {
            assert_eq!(results.requirement_table_refs.units.len(), 13);
        } else {
            assert_eq!(results.requirement_table_refs.units.len(), 14);
        }
        assert_eq!(results.requirement_table_refs.upgrades.len(), 5);
        assert_eq!(results.requirement_table_refs.tech_use.len(), 5);
        assert_eq!(results.requirement_table_refs.tech_research.len(), 5);
        assert_eq!(results.requirement_table_refs.orders.len(), 5);
    }

    let step_secondary_order = analysis.step_secondary_order();
    assert_eq!(step_secondary_order.len(), 1);
    match step_secondary_order[0] {
        samase_scarf::SecondaryOrderHook::Inlined{ .. } => assert!(new_codegen),
        samase_scarf::SecondaryOrderHook::Separate(..) => assert!(!new_codegen),
    }

    let step_order_hidden = analysis.step_order_hidden();
    assert_eq!(step_order_hidden.len(), 1);
    match step_order_hidden[0] {
        samase_scarf::StepOrderHiddenHook::Inlined{ .. } => assert!(new_codegen),
        samase_scarf::StepOrderHiddenHook::Separate(..) => assert!(!new_codegen),
    }

    let aiscript_hook = analysis.aiscript_hook();
    assert!(aiscript_hook.is_some());
    let aiscript_hook = (*aiscript_hook).as_ref().unwrap();
    assert!(op_register_anywidth(aiscript_hook.opcode_operand).is_some());
    assert_ne!(
        aiscript_hook.opcode_operand,
        aiscript_hook.script_operand_at_switch
    );
    let rng = analysis.rng();
    assert!(rng.seed.is_some());
    assert!(rng.enable.is_some());
    check_global(rng.seed.unwrap(), binary, "rng seed");
    check_global(rng.enable.unwrap(), binary, "rng enable");
    assert_ne!(rng.seed.unwrap(), rng.enable.unwrap());
    let step_objects = analysis.step_objects();
    assert!(step_objects.is_some());
    let game = analysis.game();
    assert!(game.is_some());
    check_game(game.unwrap(), binary, "game");
    let player_ai = analysis.player_ai();
    assert!(player_ai.is_some());
    check_global_struct(player_ai.unwrap(), binary, "player ai");
    let regions = analysis.regions();
    assert!(regions.get_region.is_some());
    assert!(regions.ai_regions.is_some());
    assert!(regions.change_ai_region_state.is_some());
    check_global_struct(regions.ai_regions.unwrap(), binary, "ai regions");
    let pathing = analysis.pathing().unwrap();
    check_global(pathing, binary, "pathing");

    let active_hidden_units = analysis.active_hidden_units();
    assert!(active_hidden_units.first_active_unit.is_some());
    assert!(active_hidden_units.first_hidden_unit.is_some());
    check_global(
        active_hidden_units.first_active_unit.unwrap(),
        binary,
        "first active unit",
    );
    check_global(
        active_hidden_units.first_hidden_unit.unwrap(),
        binary,
        "first hidden unit",
    );
    let order_issuing = analysis.order_issuing();
    assert!(order_issuing.prepare_issue_order.is_some());
    assert!(order_issuing.do_next_queued_order.is_some());
    assert!(order_issuing.order_init_arbiter.is_some());

    let commands = analysis.process_commands();
    assert!(commands.process_commands.is_some());
    assert!(commands.storm_command_user.is_some());
    check_global(commands.storm_command_user.unwrap(), binary, "storm_command_user");
    let command_user = analysis.command_user().unwrap();
    check_global(command_user, binary, "command_user");
    let selections = analysis.selections();
    let unique_command_user = selections.unique_command_user.unwrap();
    check_global(unique_command_user, binary, "unique_command_user");
    check_global_struct(selections.selections.unwrap(), binary, "selections");

    let is_replay = analysis.is_replay().unwrap();
    check_global(is_replay, binary, "is_replay");

    let lobby_commands = analysis.process_lobby_commands();
    assert!(lobby_commands.is_some());
    let send_command = analysis.send_command();
    assert!(send_command.is_some());

    let print = analysis.print_text();
    assert!(print.is_some());
    let step_order = analysis.step_order();
    assert!(step_order.is_some());

    let units_size = analysis.dat(DatType::Units).unwrap().entry_size;
    assert_eq!(analysis.dat(DatType::Weapons).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::Flingy).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::Sprites).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::Images).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::Orders).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::Upgrades).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::TechData).unwrap().entry_size, units_size);
    assert_eq!(analysis.dat(DatType::PortData).unwrap().entry_size, units_size);
    if minor_version < 22 {
        assert_eq!(analysis.dat(DatType::SfxData).unwrap().entry_size, units_size);
    } else {
        assert!(analysis.dat(DatType::SfxData).is_none());
    }

    let init_units = analysis.init_units();
    assert!(init_units.is_some());
    let load_dat = analysis.load_dat();
    assert!(load_dat.is_some());
    let init_game = analysis.init_game();
    assert!(init_game.init_game.is_some());
    assert!(init_game.loaded_save.is_some());
    check_global(init_game.loaded_save.unwrap(), binary, "loaded save");

    let command_lengths = analysis.command_lengths();
    assert_eq!(command_lengths[0x37], 7);
    assert!(command_lengths.len() >= 0x59);

    let units = analysis.units().unwrap();
    if extended_limits {
        check_global(units, binary, "units");
    } else {
        check_global_struct(units, binary, "units");
    }

    let rclick = analysis.game_screen_rclick();
    assert!(rclick.game_screen_rclick.is_some());
    check_global_struct(rclick.client_selection.unwrap(), binary, "client selection");

    let first_ai_script = analysis.first_ai_script();
    check_global(first_ai_script.unwrap(), binary, "first ai script");

    let guard_ai = analysis.first_guard_ai();
    check_global_struct(guard_ai.unwrap(), binary, "first guard ai");

    let towns = analysis.player_ai_towns();
    check_global_struct(towns.unwrap(), binary, "towns");

    let iscript = analysis.step_iscript();
    assert!(iscript.step_fn.is_some());
    assert!(iscript.script_operand_at_switch.is_some());
    assert!(iscript.opcode_check.is_some());
    check_global(iscript.iscript_bin.unwrap(), binary, "iscript_bin");

    let sprites = analysis.sprites();
    check_global_struct_opt(sprites.sprite_hlines, binary, "sprite hlines");
    check_global_struct_opt(sprites.sprite_hlines_end, binary, "sprite hlines end");
    check_global_struct_opt(sprites.first_free_sprite, binary, "first free sprite");
    check_global_struct_opt(sprites.last_free_sprite, binary, "last free sprite");
    check_global_struct_opt(sprites.first_lone, binary, "first lone sprite");
    check_global_struct_opt(sprites.last_lone, binary, "last lone sprite");
    check_global_struct_opt(sprites.first_free_lone, binary, "first free lone sprite");
    check_global_struct_opt(sprites.last_free_lone, binary, "first free lone sprite");
    assert!(sprites.create_lone_sprite.is_some());
    let (x, x_off, x_size) = sprites.sprite_x_position.unwrap();
    let (y, y_off, y_size) = sprites.sprite_y_position.unwrap();
    let init_sprites = analysis.init_sprites();
    assert!(init_sprites.is_some());
    let (sprite_array, sprite_size) = analysis.sprite_array().unwrap();
    if extended_limits {
        // Allocated behind a pointer
        check_global(sprite_array, binary, "sprite_array");
    } else {
        // Static array
        check_global_struct(sprite_array, binary, "sprite_array");
    }

    let old_sprite_pos = minor_version < 23 ||
        (minor_version == 23 && patch_version < 3) ||
        filename_str == "1233a" ||
        filename_str == "1233b";
    if old_sprite_pos {
        assert_eq!(x_off, 0x14);
        assert_eq!(y_off, 0x16);
        assert_eq!(x, ctx.custom(0));
        assert_eq!(y, ctx.custom(0));
        assert_eq!(x_size, scarf::MemAccessSize::Mem16);
        assert_eq!(y_size, scarf::MemAccessSize::Mem16);
        assert_eq!(sprite_size, 0x24);
    } else {
        assert_eq!(x_off, 0x14);
        assert_eq!(y_off, 0x18);
        assert_ne!(x, ctx.custom(0));
        assert_ne!(y, ctx.custom(0));
        assert_eq!(x_size, scarf::MemAccessSize::Mem32);
        assert_eq!(y_size, scarf::MemAccessSize::Mem32);
        // These seem to use same key always
        assert_eq!(x, y);
        assert_eq!(sprite_size, 0x28);
    }

    let euds = analysis.eud_table();
    if minor_version < 21 {
        assert_eq!(euds.euds.len(), 0);
    } else if minor_version == 21 {
        // Technically all of 1.21 should have euds but eh
        if patch_version < 3 {
            assert_eq!(euds.euds.len(), 0);
        } else {
            assert_eq!(euds.euds.len(), 698);
        }
    } else if minor_version == 22 {
        if patch_version < 2 {
            assert_eq!(euds.euds.len(), 698);
        } else {
            assert_eq!(euds.euds.len(), 705);
        }
    } else {
        assert_eq!(euds.euds.len(), 702);
    }

    let map_tile_flags = analysis.map_tile_flags();
    check_global(map_tile_flags.map_tile_flags.unwrap(), binary, "map_tile_flags");
    assert!(map_tile_flags.update_visibility_point.is_some());

    let players = analysis.players();
    check_game(players.unwrap(), binary, "players");

    let draw = analysis.draw_image();
    assert!(draw.is_some());
    let vtables = analysis.renderer_vtables();
    let has_prism = (minor_version == 23 && patch_version == 4 && is_ptr) ||
        (minor_version == 23 && patch_version >= 5) ||
        minor_version > 23;
    if minor_version < 22 || has_prism {
        // Older versions had a d3d11 renderer??
        // Newer versions have prism.
        assert_eq!(vtables.len(), 3);
    } else {
        assert_eq!(vtables.len(), 2);
    }

    let local_player_id = analysis.local_player_id();
    check_global(local_player_id.unwrap(), binary, "local_player_id");
    let bullets = analysis.bullet_creation();
    check_global_struct_opt(bullets.first_free_bullet, binary, "first free bullet");
    check_global_struct_opt(bullets.last_free_bullet, binary, "last free bullet");
    check_global_struct_opt(bullets.first_active_bullet, binary, "first active bullet");
    check_global_struct_opt(bullets.last_active_bullet, binary, "last active bullet");
    check_global(bullets.active_iscript_unit.unwrap(), binary, "active iscript unit");
    assert!(bullets.create_bullet.is_some());

    let net_players = analysis.net_players();
    let (players, size) = net_players.net_players.clone().unwrap();
    check_global_struct(players, binary, "net players");
    assert_eq!(size, 0x68, "sizeof NetPlayer");
    assert!(net_players.init_net_player.is_some());
    let play_smk = analysis.play_smk();
    assert!(play_smk.is_some());
    let game_init = analysis.game_init();
    assert!(game_init.sc_main.is_some());
    assert!(game_init.mainmenu_entry_hook.is_some());
    assert!(game_init.game_loop.is_some());
    check_global(game_init.scmain_state.unwrap(), binary, "scmain_state");

    let add_overlay_iscript = analysis.add_overlay_iscript();
    assert!(add_overlay_iscript.is_some());
    let campaigns = analysis.campaigns();
    check_global_struct_opt(campaigns, binary, "campaigns");
    let run_dialog = analysis.run_dialog();
    assert!(run_dialog.is_some());
    let spawn_dialog = analysis.spawn_dialog();
    assert!(spawn_dialog.is_some());
    assert_ne!(run_dialog, spawn_dialog);
    let ai_update_attack_target = analysis.ai_update_attack_target();
    assert!(ai_update_attack_target.is_some());
    let is_outside_game_screen = analysis.is_outside_game_screen();
    assert!(is_outside_game_screen.is_some());

    let coords = analysis.game_coord_conversion();
    check_global(coords.screen_x.unwrap(), binary, "screen_x");
    check_global(coords.screen_y.unwrap(), binary, "screen_y");
    check_global(coords.scale.unwrap(), binary, "ui_scale");

    let fow = analysis.fow_sprites();
    check_global_struct_opt(fow.first_active, binary, "first fow sprite");
    check_global_struct_opt(fow.last_active, binary, "last fow sprite");
    check_global_struct_opt(fow.first_free, binary, "first free fow sprite");
    check_global_struct_opt(fow.last_free, binary, "first free fow sprite");

    let init_map_from_path = analysis.init_map_from_path();
    assert!(init_map_from_path.is_some());
    let choose_snp = analysis.choose_snp();
    assert!(choose_snp.is_some());
    let snet_initialize_provider = analysis.snet_initialize_provider();
    assert!(snet_initialize_provider.is_some());

    let start = analysis.single_player_start();
    assert!(start.single_player_start.is_some());
    check_global(start.local_storm_player_id.unwrap(), binary, "local storm player id");
    check_global(start.local_unique_player_id.unwrap(), binary, "local uniq player id");
    check_global_struct_opt(start.net_player_to_game, binary, "net player to game");
    check_global_struct_opt(start.net_player_to_unique, binary, "net player to uniq");
    check_global_struct_opt(start.game_data, binary, "game data");
    check_global_struct_opt(start.skins, binary, "skins");
    check_global_struct_opt(start.player_skins, binary, "player skins");
    assert_eq!(start.skins_size, 0x15e);

    let sel = analysis.select_map_entry();
    assert!(sel.select_map_entry.is_some());
    check_global(sel.is_multiplayer.unwrap(), binary, "is_multiplayer");

    let load_images = analysis.load_images();
    assert!(load_images.is_some());
    let images_loaded = analysis.images_loaded();
    check_global(images_loaded.unwrap(), binary, "images loaded");
    let init_rtl = analysis.init_real_time_lighting();
    assert!(init_rtl.is_some());
    let local_player_name = analysis.local_player_name();
    check_global_struct_opt(local_player_name, binary, "local player name");

    let step = analysis.step_network();
    assert!(step.step_network.is_some());
    assert!(step.receive_storm_turns.is_some());
    check_game(step.menu_screen_id.unwrap(), binary, "menu_screen_id");
    check_global(step.network_ready.unwrap(), binary, "network ready");
    check_global_struct_opt(step.net_player_flags, binary, "net player flags");
    check_global_struct_opt(step.player_turns, binary, "net player turns");
    check_global_struct_opt(step.player_turns_size, binary, "net player turns size");

    let snp_definitions = analysis.snp_definitions();
    if minor_version < 23 || (minor_version == 23 && patch_version < 3) {
        let snp_definitions = snp_definitions.unwrap();
        check_global_struct(snp_definitions.snp_definitions, binary, "snp definitions");
        assert_eq!(snp_definitions.entry_size, 0x90);
    } else {
        assert!(snp_definitions.is_none());
    }

    let lobby_state = analysis.lobby_state();
    check_global(lobby_state.unwrap(), binary, "lobby state");

    let init_network = analysis.init_game_network();
    assert!(init_network.is_some());
    let init_storm_networking = analysis.init_storm_networking();
    assert!(init_storm_networking.init_storm_networking.is_some());
    assert!(init_storm_networking.load_snp_list.is_some());

    let draw_cursor_marker = analysis.draw_cursor_marker();
    check_global(draw_cursor_marker.unwrap(), binary, "draw cursor marker");

    let misc = analysis.misc_clientside();
    check_global(misc.is_paused.unwrap(), binary, "is_paused");
    check_global(misc.is_placing_building.unwrap(), binary, "is_placing_building");
    check_global(misc.is_targeting.unwrap(), binary, "is_targeting");

    let unit_creation = analysis.unit_creation();
    assert!(unit_creation.create_unit.is_some());
    assert!(unit_creation.finish_unit_pre.is_some());
    assert!(unit_creation.finish_unit_post.is_some());

    assert!(analysis.serialize_sprites().is_some());
    assert!(analysis.deserialize_sprites().is_some());

    let fonts = analysis.fonts();
    check_global_struct_opt(fonts, binary, "fonts");

    let limits = analysis.limits();
    if extended_limits {
        assert!(limits.set_limits.is_some());
        assert!(analysis.smem_alloc().is_some());
        assert!(analysis.smem_free().is_some());
        if minor_version < 21 || (minor_version == 21 && patch_version < 1) {
            assert_eq!(limits.arrays.len(), 7);
            assert_eq!(limits.arrays[0].len(), 1);
            assert_eq!(limits.arrays[1].len(), 3);
            assert_eq!(limits.arrays[2].len(), 1);
            assert_eq!(limits.arrays[3].len(), 6);
            assert_eq!(limits.arrays[4].len(), 1);
            assert_eq!(limits.arrays[5].len(), 0); // Orders weren't extended
            assert_eq!(limits.arrays[6].len(), 1);
        } else {
            assert_eq!(limits.arrays.len(), 7);
            assert_eq!(limits.arrays[0].len(), 1);
            assert_eq!(limits.arrays[1].len(), 3);
            assert_eq!(limits.arrays[2].len(), 1);
            assert_eq!(limits.arrays[3].len(), 6);
            assert_eq!(limits.arrays[4].len(), 1);
            assert_eq!(limits.arrays[5].len(), 1);
            assert_eq!(limits.arrays[6].len(), 1);
        }
    } else {
        assert!(analysis.smem_alloc().is_none());
        assert!(analysis.smem_free().is_none());
        assert!(limits.set_limits.is_none());
        assert_eq!(limits.arrays.len(), 0);
    }

    assert!(analysis.font_cache_render_ascii().is_some());
    assert!(analysis.ttf_cache_character().is_some());
    assert!(analysis.ttf_render_sdf().is_some());
    assert!(analysis.ttf_malloc().is_some());

    let offset = analysis.create_game_dialog_vtbl_on_multiplayer_create().unwrap();
    // 1207a .. 1232e 0xa8
    // 1233a .. 1233f 0xac
    // 1233g .. 0xb0
    if minor_version > 23 ||
        (minor_version == 23 && patch_version > 3) ||
        (minor_version == 23 && patch_version == 3 && revision >= b'g')
    {
        assert_eq!(offset, 0xb0);
    } else if minor_version == 23 && patch_version == 3 {
        assert_eq!(offset, 0xac);
    } else {
        assert_eq!(offset, 0xa8);
    }

    check_global(analysis.tooltip_draw_func().unwrap(), binary, "tooltip_draw_func");
    check_global(analysis.current_tooltip_ctrl().unwrap(), binary, "current_tooltip_ctrl");
    check_global_struct(analysis.graphic_layers().unwrap(), binary, "graphic_layers");
    assert!(analysis.layout_draw_text().is_some());
    assert!(analysis.draw_f10_menu_tooltip().is_some());
    assert!(analysis.draw_tooltip_layer().is_some());
    assert!(analysis.draw_graphic_layers().is_some());

    if has_prism {
        assert_eq!(analysis.prism_vertex_shaders().len(), 0x6);
        assert_eq!(analysis.prism_pixel_shaders().len(), 0x2b);
    } else {
        assert_eq!(analysis.prism_vertex_shaders().len(), 0);
        assert_eq!(analysis.prism_pixel_shaders().len(), 0);
    }

    assert!(analysis.ai_attack_prepare().is_some());
    assert!(analysis.ai_step_region().is_some());

    let join_game = analysis.join_game();
    // 1233g refactored join_game/it's arguments heavily from what used to resemble 1161,
    // this analysis only finds the new format
    if minor_version > 23 ||
        (minor_version == 23 && patch_version > 3) ||
        (minor_version == 23 && patch_version == 3 && revision >= b'g')
    {
        assert!(join_game.is_some());
    } else {
        assert!(join_game.is_none());
    }

    assert!(analysis.do_attack().is_some());
    assert!(analysis.do_attack_main().is_some());
    check_global(analysis.last_bullet_spawner().unwrap(), binary, "last_bullet_spawner");
    check_global_struct(analysis.cmdicons_ddsgrp().unwrap(), binary, "cmdicons_ddsgrp");
    check_global_struct(analysis.cmdbtns_ddsgrp().unwrap(), binary, "cmdbtns_ddsgrp");

    // 1.23.0 added input abstraction
    let mouse_xy = analysis.mouse_xy();
    if minor_version >= 23 {
        assert!(mouse_xy.x_func.is_some());
        assert!(mouse_xy.y_func.is_some());
        assert!(mouse_xy.x_var.is_none());
        assert!(mouse_xy.y_var.is_none());
    } else {
        check_global(mouse_xy.x_var.unwrap(), binary, "mouse x");
        check_global(mouse_xy.y_var.unwrap(), binary, "mouse y");
        assert!(mouse_xy.x_func.is_none());
        assert!(mouse_xy.y_func.is_none());
    }

    check_global(analysis.status_screen_mode().unwrap(), binary, "status_screen_mode");
    assert!(analysis.check_unit_requirements().is_some());
    assert!(analysis.check_dat_requirements().is_some());
    check_global(analysis.dat_requirement_error().unwrap(), binary, "dat_requirement_error");
    check_global(analysis.cheat_flags().unwrap(), binary, "cheat_flags");
    check_global_struct(analysis.unit_strength().unwrap(), binary, "unit_strength");

    check_global(analysis.grpwire_grp().unwrap(), binary, "grpwire_grp");
    check_global(analysis.tranwire_grp().unwrap(), binary, "tranwire_grp");
    check_global_struct(analysis.grpwire_ddsgrp().unwrap(), binary, "grpwire_ddsgrp");
    check_global_struct(analysis.tranwire_ddsgrp().unwrap(), binary, "tranwire_ddsgrp");
    check_global(analysis.status_screen().unwrap(), binary, "status_screen");
    assert!(analysis.status_screen_event_handler().is_some());
    assert!(analysis.init_status_screen().is_some());
    check_global_struct(analysis.wirefram_ddsgrp().unwrap(), binary, "wirefram_ddsgrp");

    assert!(analysis.trigger_conditions().is_some());
    assert!(analysis.trigger_actions().is_some());
}

fn op_register_anywidth(op: Operand<'_>) -> Option<Register> {
    match *op.ty() {
        OperandType::Register(s) => Some(s),
        _ => op.if_and_masked_register().map(|x| x.0)
    }
}

fn check_game<Va: VirtualAddressTrait>(
    op: Operand<'_>,
    binary: &scarf::BinaryFile<Va>,
    name: &str,
) {
    assert!(
        op.if_memory().is_none(),
        "{}: Didn't expect memory immediatly {:#?}", name, op
    );
    let data = binary.section(b".data\0\0\0").unwrap();
    let has_const_mem = op.iter().flat_map(|x| {
        x.if_memory().and_then(|x| x.address.if_constant()).map(|x| Va::from_u64(x))
    }).filter(|&addr| {
        addr >= data.virtual_address && addr < data.virtual_address + data.virtual_size
    }).next().is_some();
    assert!(has_const_mem, "{} didn't have const mem address", name);
}

fn check_global<Va: VirtualAddressTrait>(
    op: Operand<'_>,
    binary: &scarf::BinaryFile<Va>,
    name: &str,
) {
    let mem = op.if_memory().unwrap_or_else(|| {
        panic!("{}: Expected global memory, got {:#?}", name, op)
    });
    let c = mem.address.if_constant().unwrap_or_else(|| {
        panic!("{}: Expected constant address, got {:#?}", name, &mem.address)
    });
    let addr = Va::from_u64(c);
    let data = binary.section(b".data\0\0\0").unwrap();
    assert!(
        addr >= data.virtual_address &&
            addr < data.virtual_address + data.virtual_size,
        "value of {} is invalid: {:x}", name, c,
    );
}

fn check_global_struct_opt<Va: VirtualAddressTrait>(
    op: Option<Operand<'_>>,
    binary: &scarf::BinaryFile<Va>,
    name: &str,
) {
    let op = op.unwrap_or_else(|| {
        panic!("{} not found", name);
    });
    check_global_struct(op, binary, name);
}

fn check_global_struct<Va: VirtualAddressTrait>(
    op: Operand<'_>,
    binary: &scarf::BinaryFile<Va>,
    name: &str,
) {
    // Word-sized values (check_global) are wrapped in Mem[] by default as they
    // may have some additional encryption, assuming that structs cannot have that
    // so they are just plain constant.
    let c = op.if_constant().unwrap_or_else(|| {
        panic!("{}: Expected constant address, got {:#?}", name, &op);
    });
    let addr = Va::from_u64(c);
    let data = binary.section(b".data\0\0\0").unwrap();
    assert!(
        addr >= data.virtual_address &&
            addr < data.virtual_address + data.virtual_size,
        "value of {} is invalid: {:x}", name, c,
    );
}

struct PrintLnLog;
impl log::Log for PrintLnLog {
    fn enabled(&self, _: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        println!("{}", record.args());
    }

    fn flush(&self) {
    }
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
        .level_for("scarf", log::LevelFilter::Trace)
        .level_for("samase_scarf", log::LevelFilter::Trace)
        .chain(Box::new(PrintLnLog) as Box<dyn log::Log>)
        .apply();
}
