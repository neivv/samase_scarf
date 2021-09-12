extern crate fern;
extern crate log;
extern crate samase_scarf;
extern crate scarf;

use std::path::Path;

use scarf::{Operand, OperandType, VirtualAddress, ExecutionStateX86, OperandContext, OperandCtx};
use scarf::exec_state::VirtualAddress as VirtualAddressTrait;
use samase_scarf::{DatType, Eud};

#[test]
fn everything_1207() {
    test_with_extra_checks(Path::new("1207.exe"), |ctx, analysis| {
        assert_eq!(analysis.process_events().unwrap().0, 0x00732760);
        assert_eq!(analysis.next_game_step_tick().unwrap(), ctx.mem32c(0x10f8628));
    })
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

        assert_eq!(analysis.grpwire_grp().unwrap(), ctx.mem32c(0x113e9bc));
        assert_eq!(analysis.tranwire_grp().unwrap(), ctx.mem32c(0x113e9b8));
        assert_eq!(analysis.grpwire_ddsgrp().unwrap(), ctx.constant(0x113e960));
        assert_eq!(analysis.tranwire_ddsgrp().unwrap(), ctx.constant(0x113e96c));
        assert_eq!(analysis.status_screen().unwrap(), ctx.mem32c(0x113e9c0));
        assert_eq!(analysis.status_screen_event_handler().unwrap().0, 0x00813760);
        // This is actually only address of the grp on old versions like 1208;
        // the ddsgrp set doesn't exist here.
        assert_eq!(analysis.wirefram_ddsgrp().unwrap(), ctx.constant(0x113f5d0));

        assert_eq!(analysis.trigger_conditions().unwrap().0, 0x00DC8BB0);
        assert_eq!(analysis.trigger_actions().unwrap().0, 0x00DC8AC0);
        // There's also snet_recv_server_packets for this version that would be confused
        // with snet_recv_packets if it was ordered before.
        assert_eq!(analysis.snet_send_packets().unwrap().0, 0x009ae6a0);
        assert_eq!(analysis.snet_recv_packets().unwrap().0, 0x009b14f0);

        assert_eq!(analysis.menu_swish_in().unwrap().0, 0x0077a7c0);
        assert_eq!(analysis.menu_swish_out().unwrap().0, 0x00779e70);
        assert_eq!(analysis.dialog_return_code().unwrap(), ctx.mem32c(0x115cae4));

        assert_eq!(analysis.unit_update_speed().unwrap().0, 0x006c0570);
        assert_eq!(analysis.unit_update_speed_iscript().unwrap().0, 0x006a4190);
        assert_eq!(analysis.unit_buffed_flingy_speed().unwrap().0, 0x00694c70);
        assert_eq!(analysis.unit_buffed_acceleration().unwrap().0, 0x00694bb0);
        assert_eq!(analysis.unit_buffed_turn_speed().unwrap().0, 0x00694c10);

        assert_eq!(analysis.open_anim_single_file().unwrap().0, 0x006178c0);
        assert_eq!(analysis.open_anim_multi_file().unwrap().0, 0x00617d80);
        assert_eq!(analysis.base_anim_set().unwrap(), ctx.constant(0xe728d8));
        assert_eq!(analysis.first_invisible_unit().unwrap(), ctx.mem32c(0xf35350));
        assert_eq!(analysis.step_network().unwrap().0, 0x007BF740);
        assert_eq!(analysis.render_screen().unwrap().0, 0x009CF170);

        assert_eq!(analysis.first_ai_script().unwrap(), ctx.mem32c(0x00f5df00));

        assert_eq!(analysis.process_commands().unwrap().0, 0x007b84e0);
        assert_eq!(analysis.storm_command_user().unwrap(), ctx.mem32c(0x00dcec10));

        assert_eq!(analysis.map_entry_load_map().unwrap().0, 0x00988510);
        assert_eq!(analysis.map_entry_load_save().unwrap().0, 0x00988060);
        assert_eq!(analysis.map_entry_load_replay().unwrap().0, 0x00987a30);
        assert_eq!(analysis.create_game_multiplayer().unwrap().0, 0x007b0330);
    });
}

#[test]
fn everything_1209() {
    test(Path::new("1209.exe"));
}

#[test]
fn everything_1209b() {
    test_with_extra_checks(Path::new("1209b.exe"), |ctx, analysis| {
        let ais = analysis.aiscript_hook().unwrap();
        assert_eq!(ais.opcode_operand.if_register(), Some(0));
        assert_eq!(ais.switch_loop_address.0, 0x00607ED0);
        assert_eq!(ais.return_address.0, 0x00608F4F);

        let select_map_entry = analysis.select_map_entry();
        let is_multiplayer = analysis.is_multiplayer();
        assert_eq!(select_map_entry.unwrap().0, 0x008A1ED0);
        assert_eq!(is_multiplayer.unwrap(), ctx.mem8c(0x1036D20));

        assert_eq!(analysis.replay_data().unwrap(), ctx.mem32c(0x1039e3c));
    });
}

#[test]
fn everything_12010() {
    test(Path::new("12010.exe"));
}

#[test]
fn everything_12011() {
    test_with_extra_checks(Path::new("12011.exe"), |ctx, analysis| {
        assert_eq!(analysis.first_dying_unit().unwrap(), ctx.mem32c(0xe240bc));
        assert_eq!(analysis.active_iscript_flingy().unwrap(), ctx.mem32c(0xd0891c));
    });
}

#[test]
fn everything_12011b() {
    test_with_extra_checks(Path::new("12011b.exe"), |ctx, analysis| {
        let first_active_unit = analysis.first_active_unit();
        let first_hidden_unit = analysis.first_hidden_unit();
        assert_eq!(first_active_unit.unwrap(), ctx.mem32c(0xf240ac));
        assert_eq!(first_hidden_unit.unwrap(), ctx.mem32c(0xf240c4));
        let prepare_issue_order = analysis.prepare_issue_order();
        let do_next_queued_order = analysis.do_next_queued_order();
        assert_eq!(prepare_issue_order.unwrap().0, 0x006A8FB0);
        assert_eq!(do_next_queued_order.unwrap().0, 0x006A96A0);
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
        let init_net_player = analysis.init_net_player();
        assert_eq!(init_net_player.unwrap().0, 0x006F28E0);
        assert_eq!(net_players.as_ref().unwrap().0, ctx.constant(0x00F31988));

        assert_eq!(analysis.tooltip_draw_func().unwrap(), ctx.mem32c(0xd49148));
        assert_eq!(analysis.current_tooltip_ctrl().unwrap(), ctx.mem32c(0xd4914c));
        assert_eq!(analysis.layout_draw_text().unwrap().0, 0x008d5fd0);

        assert_eq!(analysis.smem_alloc().unwrap().0, 0x0089ead0);
        assert_eq!(analysis.smem_free().unwrap().0, 0x0089eb10);
        assert_eq!(analysis.first_dying_unit().unwrap(), ctx.mem32c(0xd48884));
        assert_eq!(analysis.active_iscript_flingy().unwrap(), ctx.mem32c(0xd3116c));
    });
}

#[test]
fn everything_1211() {
    test_with_extra_checks(Path::new("1211.exe"), |_ctx, analysis| {
        let ais = analysis.aiscript_hook().unwrap();
        assert_eq!(ais.opcode_operand.if_register(), Some(0));
        assert_eq!(ais.script_operand_at_switch.if_register(), Some(6));
        assert_eq!(ais.op_limit_hook_begin.0, 0x007134EB);
        assert_eq!(ais.op_limit_hook_end.0, 0x007134FA);
        assert_eq!(ais.switch_loop_address.0, 0x00714EF9);
    });
}

#[test]
fn everything_1211b() {
    test_with_extra_checks(Path::new("1211b.exe"), |ctx, analysis| {
        assert_eq!(analysis.process_commands().unwrap().0, 0x0072D560);
        assert_eq!(analysis.storm_command_user().unwrap(), ctx.mem32c(0x00D61584));

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
        assert_eq!(analysis.smem_alloc().unwrap().0, 0x00920d50);
        assert_eq!(analysis.smem_free().unwrap().0, 0x00920D90);
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
                    ctx.mem32c(0xd1775e),
                    ctx.constant(2),
                ),
            ),
            ctx.mem32c(0xf25830),
        );
        assert_eq!(players, val);

        let step_iscript = analysis.step_iscript().unwrap();
        let hook = analysis.step_iscript_hook().unwrap();
        let iscript_bin = analysis.iscript_bin().unwrap();
        assert_eq!(step_iscript.0, 0x0054a250);
        assert_eq!(hook.script_operand_at_switch, ctx.register(2));
        assert_eq!(iscript_bin, ctx.mem32c(0xd35994));

        assert_eq!(analysis.vertex_buffer().unwrap(), ctx.constant(0xceede8));
    });
}

#[test]
fn everything_1212b() {
    test_with_extra_checks(Path::new("1212b.exe"), |_ctx, analysis| {
        assert_eq!(analysis.process_commands().unwrap().0, 0x0069ca80);

        assert_eq!(analysis.unit_update_speed(), None);
        assert_eq!(analysis.unit_update_speed_iscript().unwrap().0, 0x0057bad0);
        assert_eq!(analysis.unit_buffed_flingy_speed().unwrap().0, 0x005742f0);
        assert_eq!(analysis.unit_buffed_acceleration().unwrap().0, 0x00574230);
        assert_eq!(analysis.unit_buffed_turn_speed().unwrap().0, 0x00574290);
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

        assert_eq!(analysis.mouse_x().unwrap(), ctx.mem16c(0xea9910));
        assert_eq!(analysis.mouse_y().unwrap(), ctx.mem16c(0xea9914));

        assert_eq!(analysis.vertex_buffer().unwrap(), ctx.constant(0x00c75220));
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
        assert_eq!(analysis.process_commands().unwrap().0, 0x00696d80);

        let init_game = analysis.init_game();
        let loaded_save = analysis.loaded_save();
        assert_eq!(init_game.unwrap().0, 0x00643460);
        assert_eq!(loaded_save.unwrap(), ctx.mem32c(0x00c666dc));

        let command_user = analysis.command_user().unwrap();
        assert_eq!(command_user, ctx.mem32c(0x00c65de4));

        let unique_command_user = analysis.unique_command_user();
        let selections = analysis.selections();
        assert_eq!(unique_command_user.unwrap(), ctx.mem32c(0x00c65de8));
        assert_eq!(selections.unwrap(), ctx.constant(0x00eb4d90));

        let is_replay = analysis.is_replay().unwrap();
        assert_eq!(is_replay, ctx.mem32c(0x00ea9940));

        let units = analysis.units().unwrap();
        assert_eq!(units, ctx.mem32c(0x00CBDB8C));

        let game_screen_rclick = analysis.game_screen_rclick();
        let client_selection = analysis.client_selection();
        assert_eq!(game_screen_rclick.unwrap().0, 0x006b2400);
        assert_eq!(client_selection.unwrap(), ctx.constant(0x00ec3750));
    })
}

#[test]
fn everything_1214() {
    test_with_extra_checks(Path::new("1214.exe"), |ctx, analysis| {
        let script = analysis.first_ai_script().unwrap();
        assert_eq!(script, ctx.mem32c(0x00cee4e8));
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

        let ais = analysis.aiscript_hook().unwrap();
        assert_eq!(ais.return_address.0, 0x005BCB3C);

        let pathing = analysis.pathing().unwrap();
        assert_eq!(pathing, ctx.mem32c(0x00EDFE30));
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
    test_with_extra_checks(Path::new("1220.exe"), |ctx, analysis| {
        assert_eq!(analysis.vertex_buffer().unwrap(), ctx.constant(0x00d7fa08));
        assert_eq!(analysis.base_anim_set().unwrap(), ctx.constant(0x00dce238));
        assert_eq!(analysis.add_asset_change_callback().unwrap().0, 0x0051d430);
        assert_eq!(analysis.anim_asset_change_cb().unwrap().0, 0x00538aa0);
        assert_eq!(analysis.image_grps().unwrap(), ctx.constant(0xdc3890));
        assert_eq!(analysis.image_overlays().unwrap(), ctx.constant(0xdc8380));
        assert_eq!(analysis.fire_overlay_max().unwrap(), ctx.constant(0xdc3470));
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
        let step_iscript = analysis.step_iscript().unwrap();
        let hook = analysis.step_iscript_hook().unwrap();
        assert_eq!(step_iscript.0, 0x005474C0);
        assert_eq!(hook.script_operand_at_switch, ctx.register(2));
    })
}

#[test]
fn everything_1221() {
    test_with_extra_checks(Path::new("1221.exe"), |ctx, analysis| {
        let guard_ai = analysis.first_guard_ai().unwrap();
        assert_eq!(guard_ai, ctx.constant(0x00ee41b8));

        let open_file = analysis.open_file().unwrap();
        assert_eq!(open_file.0, 0x00527860);

        let init_map_from_path = analysis.init_map_from_path().unwrap();
        assert_eq!(init_map_from_path.0, 0x006D7C30);
        let choose_snp = analysis.choose_snp().unwrap();
        assert_eq!(choose_snp.0, 0x006fef60);

        let skins = analysis.skins();
        let player_skins = analysis.player_skins();
        assert_eq!(skins.unwrap(), ctx.constant(0x00E55158));
        assert_eq!(player_skins.unwrap(), ctx.constant(0x010A52A0));

        let select_map_entry = analysis.select_map_entry();
        let is_multiplayer = analysis.is_multiplayer();
        assert_eq!(select_map_entry.unwrap().0, 0x005E7350);
        assert_eq!(is_multiplayer.unwrap(), ctx.mem8c(0x010A5138));

        let load = analysis.load_images().unwrap();
        assert_eq!(load.0, 0x0054D1E0);

        assert_eq!(analysis.ai_step_region().unwrap().0, 0x00619800);
        assert_eq!(analysis.set_unit_player().unwrap().0, 0x0058b8c0);
        assert_eq!(analysis.unit_apply_speed_upgrades().unwrap().0, 0x005af9b0);
        assert_eq!(analysis.unit_update_speed().unwrap().0, 0x005b0230);
        assert_eq!(analysis.unit_update_speed_iscript().unwrap().0, 0x00595160);
        assert_eq!(analysis.unit_buffed_flingy_speed().unwrap().0, 0x0058b690);
        assert_eq!(analysis.unit_buffed_acceleration().unwrap().0, 0x0058b5d0);
        assert_eq!(analysis.unit_buffed_turn_speed().unwrap().0, 0x0058b630);
    })
}

#[test]
fn everything_1221b() {
    test_with_extra_checks(Path::new("1221b.exe"), |ctx, analysis| {
        let init = analysis.init_game_network().unwrap();
        assert_eq!(init.0, 0x006ed550);

        let lobby_state = analysis.lobby_state();
        assert_eq!(lobby_state.unwrap(), ctx.mem8c(0x01060fc5));
        let init = analysis.init_storm_networking().unwrap();
        assert_eq!(init.0, 0x006F0BB0);

        assert_eq!(analysis.chk_init_players().unwrap(), ctx.constant(0x1064330));
        assert_eq!(analysis.replay_data().unwrap(), ctx.mem32c(0x1064310));
        assert_eq!(analysis.ai_spend_money().unwrap().0, 0x005F3E70);
        assert_eq!(analysis.ai_train_military().unwrap().0, 0x0060FD80);
        assert_eq!(analysis.ai_add_military_to_region().unwrap().0, 0x0060e530);

        assert_eq!(analysis.first_player_unit().unwrap(), ctx.constant(0xE6C824));
        assert_eq!(analysis.replay_visions().unwrap(), ctx.mem8c(0x10660C0));
        assert_eq!(
            analysis.replay_show_entire_map().unwrap(),
            ctx.mem32c(0x10660C4),
        );
    })
}

#[test]
fn everything_1221c() {
    test_with_extra_checks(Path::new("1221c.exe"), |ctx, analysis| {
        let step_iscript = analysis.step_iscript().unwrap();
        let hook = analysis.step_iscript_hook().unwrap();
        assert_eq!(step_iscript.0, 0x00546760);
        assert_eq!(hook.script_operand_at_switch, ctx.register(7));

        let sprite_hlines = analysis.sprite_hlines();
        let sprite_hlines_end = analysis.sprite_hlines_end();
        let first_free_sprite = analysis.first_free_sprite();
        let last_free_sprite = analysis.last_free_sprite();
        let first_lone = analysis.first_lone_sprite();
        let last_lone = analysis.last_lone_sprite();
        let first_free_lone = analysis.first_free_lone_sprite();
        let last_free_lone = analysis.last_free_lone_sprite();
        assert_eq!(sprite_hlines.unwrap(), ctx.constant(0x00e7ccc0));
        assert_eq!(sprite_hlines_end.unwrap(), ctx.constant(0x00e7d0c0));
        assert_eq!(first_free_sprite.unwrap(), ctx.mem32c(0x00e7c9a0));
        assert_eq!(last_free_sprite.unwrap(), ctx.mem32c(0x00e7c9a4));
        assert_eq!(first_lone.unwrap(), ctx.mem32c(0x00e7d610));
        assert_eq!(last_lone.unwrap(), ctx.mem32c(0x00e7d614));
        assert_eq!(first_free_lone.unwrap(), ctx.mem32c(0x00e7d608));
        assert_eq!(last_free_lone.unwrap(), ctx.mem32c(0x00e7d60c));
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
        assert_eq!(pathing, ctx.mem32c(0x00ff1274));
        assert_eq!(analysis.add_asset_change_callback().unwrap().0, 0x005238d0);
        assert_eq!(analysis.anim_asset_change_cb().unwrap().0, 0x00550cf0);
        assert_eq!(analysis.step_unit_movement().unwrap().0, 0x0058ec70);
        assert_eq!(analysis.unit_should_reveal_area().unwrap(), ctx.mem32c(0xdf5b8c));
        assert_eq!(analysis.prepare_draw_image().unwrap().0, 0x0054c3b0);
        assert_eq!(analysis.draw_image().unwrap().0, 0x00552810);
        assert_eq!(analysis.cursor_marker().unwrap(), ctx.mem32c(0xdf5898));
    })
}

#[test]
fn everything_1222c() {
    test_with_extra_checks(Path::new("1222c.exe"), |ctx, analysis| {
        assert_eq!(analysis.replay_data().unwrap(), ctx.mem32c(0x10185d8));
    })
}

#[test]
fn everything_1222d() {
    test_with_extra_checks(Path::new("1222d.exe"), |ctx, analysis| {
        let init_game = analysis.init_game();
        let loaded_save = analysis.loaded_save();
        assert_eq!(init_game.unwrap().0, 0x00694330);
        assert_eq!(loaded_save.unwrap(), ctx.mem32c(0x00da61cc));
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
        assert_eq!(map_tile_flags.unwrap(), ctx.mem32c(0xe47004));
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
                ctx.mem32c(0x1020c70),
            ),
            ctx.mem32c(0xe0770d),
        );
        assert_eq!(players, val);

        let sprite_hlines = analysis.sprite_hlines();
        let sprite_hlines_end = analysis.sprite_hlines_end();
        assert_eq!(sprite_hlines.unwrap(), ctx.constant(0x00e287e8));
        assert_eq!(sprite_hlines_end.unwrap(), ctx.constant(0x00e28be8));

        let draw_image = analysis.draw_image().unwrap();
        assert_eq!(draw_image.0, 0x0055CDA0);
        let vtables = analysis.renderer_vtables();
        assert_eq!(vtables.len(), 2);
        assert!(vtables.iter().any(|x| x.0 == 0xca4b94));
        assert!(vtables.iter().any(|x| x.0 == 0xca4b28));

        let local_player_id = analysis.local_player_id().unwrap();
        assert_eq!(local_player_id, ctx.mem32c(0xdc7940));
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
        let step_iscript = analysis.step_iscript().unwrap();
        let hook = analysis.step_iscript_hook().unwrap();
        assert_eq!(step_iscript.0, 0x005409e0);
        assert_eq!(hook.script_operand_at_switch, ctx.register(6));
        assert_eq!(analysis.iscript_bin().unwrap(), ctx.mem32c(0xde75c4));
        assert_eq!(hook.opcode_check, (VirtualAddress(0x00540A2A), 2));
        let first_active_bullet = analysis.first_active_bullet();
        let last_active_bullet = analysis.last_active_bullet();
        let first_free_bullet = analysis.first_free_bullet();
        let last_free_bullet = analysis.last_free_bullet();
        let create_bullet = analysis.create_bullet();
        let active_iscript_unit = analysis.active_iscript_unit();
        assert_eq!(first_active_bullet.unwrap(), ctx.mem32c(0xde60c4));
        assert_eq!(last_active_bullet.unwrap(), ctx.mem32c(0xde60c8));
        assert_eq!(first_free_bullet.unwrap(), ctx.mem32c(0xde6094));
        assert_eq!(last_free_bullet.unwrap(), ctx.mem32c(0xde6098));
        assert_eq!(create_bullet.unwrap().0, 0x531f00);
        assert_eq!(active_iscript_unit.unwrap(), ctx.mem32c(0xde7190));

        let net_players = analysis.net_players();
        let init_net_player = analysis.init_net_player();
        assert_eq!(init_net_player.unwrap().0, 0x00721680);
        assert_eq!(net_players.unwrap().0, ctx.constant(0x00FED8D8));
        let play_smk = analysis.play_smk();
        assert_eq!(play_smk.unwrap().0, 0x00739200);
        let sc_main = analysis.sc_main();
        let mainmenu_entry_hook = analysis.mainmenu_entry_hook();
        let game_loop = analysis.game_loop();
        let scmain_state = analysis.scmain_state();
        assert_eq!(sc_main.unwrap().0, 0x006e4350);
        assert_eq!(mainmenu_entry_hook.unwrap().0, 0x006e51ae);
        assert_eq!(game_loop.unwrap().0, 0x0006e5450);
        assert_eq!(scmain_state.unwrap(), ctx.mem32c(0x00FC7FE8));

        assert_eq!(analysis.font_cache_render_ascii().unwrap().0, 0x008FCFF0);
        assert_eq!(analysis.ttf_cache_character().unwrap().0, 0x009036B0);
        assert_eq!(analysis.ttf_render_sdf().unwrap().0, 0x00907980);

        assert_eq!(analysis.first_free_order().unwrap(), ctx.mem32c(0x0df3f98));
        assert_eq!(analysis.last_free_order().unwrap(), ctx.mem32c(0x0df3f9c));
        assert_eq!(analysis.allocated_order_count().unwrap(), ctx.mem32c(0x0df3fb0));
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
        let first_active_unit = analysis.first_active_unit();
        let first_hidden_unit = analysis.first_hidden_unit();
        assert_eq!(first_active_unit.unwrap(), ctx.mem32c(0xddf144));
        assert_eq!(first_hidden_unit.unwrap(), ctx.mem32c(0xddf154));
        assert_eq!(analysis.player_unit_skins().unwrap(), ctx.constant(0x00fe9b10));
        assert_eq!(analysis.init_skins().unwrap().0, 0x006124b0);
    })
}

#[test]
fn everything_1230b() {
    test_with_extra_checks(Path::new("1230b.exe"), |_ctx, analysis| {
        assert_eq!(analysis.unit_apply_speed_upgrades().unwrap().0, 0x005B7A10);
        assert_eq!(analysis.unit_update_speed().unwrap().0, 0x005B8190);
        assert_eq!(analysis.unit_update_speed_iscript().unwrap().0, 0x005a4b30);
        assert_eq!(analysis.unit_buffed_flingy_speed().unwrap().0, 0x0059b430);
        assert_eq!(analysis.unit_buffed_acceleration().unwrap().0, 0x0059b370);
        assert_eq!(analysis.unit_buffed_turn_speed().unwrap().0, 0x0059b3d0);
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
        let update_visibility_point = analysis.update_visibility_point();
        assert_eq!(update_visibility_point.unwrap().0, 0x00565E20);
        let create_lone_sprite = analysis.create_lone_sprite();
        assert_eq!(create_lone_sprite.unwrap().0, 0x00565A70);
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

        let screen_x = analysis.screen_x();
        let screen_y = analysis.screen_y();
        let zoom = analysis.zoom();
        assert_eq!(screen_x.unwrap(), ctx.mem32c(0x00e4caf4));
        assert_eq!(screen_y.unwrap(), ctx.mem32c(0x00e4caf8));
        assert_eq!(zoom.unwrap(), ctx.mem32c(0x00d77940));
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
        let first_active = analysis.first_fow_sprite();
        let last_active = analysis.last_fow_sprite();
        let first_free = analysis.first_free_fow_sprite();
        let last_free = analysis.last_free_fow_sprite();
        assert_eq!(first_active.unwrap(), ctx.mem32c(0x0E32110));
        assert_eq!(last_active.unwrap(), ctx.mem32c(0x0E32114));
        assert_eq!(first_free.unwrap(), ctx.mem32c(0x0E32108));
        assert_eq!(last_free.unwrap(), ctx.mem32c(0x0E3210C));

        let rng_seed = analysis.rng_seed();
        let rng_enable = analysis.rng_enable();
        assert_eq!(rng_seed.unwrap(), ctx.mem32c(0x1030770));
        assert_eq!(rng_enable.unwrap(), ctx.mem32c(0x1030B80));
    })
}

#[test]
fn everything_1232a() {
    test_with_extra_checks(Path::new("1232a.exe"), |_ctx, analysis| {
        let results = analysis.firegraft_addresses();
        assert_eq!(results.unit_status_funcs[0].0, 0x00E41128);
        let run_dialog = analysis.run_dialog();
        assert_eq!(run_dialog.unwrap().0, 0x0097cfc0);
        let mainmenu_entry_hook = analysis.mainmenu_entry_hook();
        assert_eq!(mainmenu_entry_hook.unwrap().0, 0x00708C4E);
    })
}

#[test]
fn everything_1232b() {
    test_with_extra_checks(Path::new("1232b.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1232c() {
    test_with_extra_checks(Path::new("1232c.exe"), |ctx, analysis| {
        assert_eq!(analysis.first_free_order().unwrap(), ctx.mem32c(0x0e9a850));
        assert_eq!(analysis.last_free_order().unwrap(), ctx.mem32c(0x0e9a854));
        assert_eq!(analysis.allocated_order_count().unwrap(), ctx.mem32c(0x0e9a868));
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

        let single_player_start = analysis.single_player_start();
        let local_storm_player_id = analysis.local_storm_player_id();
        let local_unique_player_id = analysis.local_unique_player_id();
        let net_player_to_game = analysis.net_player_to_game();
        let net_player_to_unique = analysis.net_player_to_unique();
        let game_data = analysis.game_data();
        let skins = analysis.skins();
        let player_skins = analysis.player_skins();
        assert_eq!(single_player_start.unwrap().0, 0x00714870);
        assert_eq!(local_storm_player_id.unwrap(), ctx.mem32c(0xdff54c));
        assert_eq!(local_unique_player_id.unwrap(), ctx.mem32c(0xdff548));
        assert_eq!(net_player_to_game.unwrap(), ctx.constant(0x106f6a8));
        assert_eq!(net_player_to_unique.unwrap(), ctx.constant(0x106f678));
        assert_eq!(game_data.unwrap(), ctx.constant(0x1070ce0));
        assert_eq!(skins.unwrap(), ctx.constant(0x00E003A0));
        assert_eq!(player_skins.unwrap(), ctx.constant(0x0106F6E0));

        let select_map_entry = analysis.select_map_entry();
        let is_multiplayer = analysis.is_multiplayer();
        assert_eq!(select_map_entry.unwrap().0, 0x005FD7F0);
        assert_eq!(is_multiplayer.unwrap(), ctx.mem8c(0x0106F57C));

        let load = analysis.load_images().unwrap();
        assert_eq!(load.0, 0x00566710);
        let loaded = analysis.images_loaded().unwrap();
        assert_eq!(loaded, ctx.mem8c(0x0104C60A));
        let local_player_name = analysis.local_player_name().unwrap();
        assert_eq!(local_player_name, ctx.constant(0x106f5b8));

        assert_eq!(analysis.step_network().unwrap().0, 0x00722ce0);
        assert_eq!(analysis.receive_storm_turns().unwrap().0, 0x00713370);
        let val = ctx.and_const(
            ctx.xor(
                ctx.sub(
                    ctx.constant(0x1d3fbab2),
                    ctx.mem32c(0xe5164a),
                ),
                ctx.mem32c(0x1049cf4),
            ),
            0xffff_ffff,
        );
        assert_eq!(analysis.menu_screen_id().unwrap(), val);
        assert_eq!(analysis.net_player_flags().unwrap(), ctx.constant(0x0106F588));
        assert_eq!(analysis.player_turns().unwrap(), ctx.constant(0x01071118));
        assert_eq!(analysis.player_turns_size().unwrap(), ctx.constant(0x01071148));
        assert_eq!(analysis.network_ready().unwrap(), ctx.mem8c(0x0106F57D));

        let init = analysis.init_game_network().unwrap();
        assert_eq!(init.0, 0x00713cb0);

        let snp_definitions = analysis.snp_definitions().unwrap();
        assert_eq!(snp_definitions.snp_definitions, ctx.constant(0x00E065E0));

        let lobby_state = analysis.lobby_state();
        assert_eq!(lobby_state.unwrap(), ctx.mem8c(0x0106f475));
        let init = analysis.init_storm_networking().unwrap();
        assert_eq!(init.0, 0x00716F70);
    })
}

#[test]
fn everything_1233a() {
    test_with_extra_checks(Path::new("1233a.exe"), |ctx, analysis| {
        let open_file = analysis.open_file().unwrap();
        assert_eq!(open_file.0, 0x00544720);

        let init = analysis.init_storm_networking().unwrap();
        assert_eq!(init.0, 0x0073b2e0);
        let load_snps = analysis.load_snp_list().unwrap();
        assert_eq!(load_snps.0, 0x007A4590);

        let draw_cursor_marker = analysis.draw_cursor_marker();
        assert_eq!(draw_cursor_marker.unwrap(), ctx.mem8c(0x00ee6c21));

        let is_paused = analysis.is_paused();
        let is_placing_building = analysis.is_placing_building();
        let is_targeting = analysis.is_targeting();
        assert_eq!(is_paused.unwrap(), ctx.mem32c(0x00eed95c));
        assert_eq!(is_placing_building.unwrap(), ctx.mem32c(0x010e748c));
        assert_eq!(is_targeting.unwrap(), ctx.mem8c(0x010f54f2));
    })
}

#[test]
fn everything_1233b() {
    test_with_extra_checks(Path::new("1233b.exe"), |_ctx ,analysis| {
        let spawn_dialog = analysis.spawn_dialog();
        assert_eq!(spawn_dialog.unwrap().0, 0x0097BB60);

        let create_unit = analysis.create_unit();
        let finish_unit_pre = analysis.finish_unit_pre();
        let finish_unit_post = analysis.finish_unit_post();
        assert_eq!(create_unit.unwrap().0, 0x005A0720);
        assert_eq!(finish_unit_pre.unwrap().0, 0x005A1110);
        assert_eq!(finish_unit_post.unwrap().0, 0x005A0E20);

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

        assert_eq!(analysis.first_free_order().unwrap(), ctx.mem32c(0x0ea9d60));
        assert_eq!(analysis.last_free_order().unwrap(), ctx.mem32c(0x0ea9d64));
        assert_eq!(analysis.allocated_order_count().unwrap(), ctx.mem32c(0x0ea9d78));
    })
}

#[test]
fn everything_1233d() {
    test_with_extra_checks(Path::new("1233d.exe"), |ctx, analysis| {
        let sprite_x_position = analysis.sprite_x_position();
        let sprite_y_position = analysis.sprite_y_position();
        let (x, _, _) = sprite_x_position.unwrap();
        let (y, _, _) = sprite_y_position.unwrap();
        let x_low = ctx.and_const(x, 0xffff);
        let y_low = ctx.and_const(y, 0xffff);
        let low = ctx.and_const(
            ctx.xor(
                ctx.xor(
                    ctx.custom(0),
                    ctx.mem16(ctx.mem32c(0x30), 0x10),
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
                ctx.xor(
                    ctx.and_const(
                        ctx.rsh_const(
                            ctx.custom(0),
                            0x10,
                        ),
                        0xffff,
                    ),
                    ctx.and_const(
                        ctx.xor(
                            ctx.custom(0),
                            ctx.mem16(ctx.mem32c(0x30), 0x10),
                        ),
                        0xffff,
                    ),
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
                                ctx.mem16(ctx.mem32c(0x30), 0x12),
                            ),
                            ctx.mem16(ctx.mem32c(0x30), 0x10),
                        ),
                        ctx.xor(
                            ctx.mem16c(0xead6ab),
                            ctx.mem16c(0xeada1d),
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
        let rng_seed = analysis.rng_seed();
        let rng_enable = analysis.rng_enable();
        assert_eq!(rng_seed.unwrap(), ctx.mem32c(0x10A11C0));
        assert_eq!(rng_enable.unwrap(), ctx.mem32c(0x10A15D0));

        let fonts = analysis.fonts();
        assert_eq!(fonts.unwrap(), ctx.constant(0x10D1A5C));
    })
}

#[test]
fn everything_1233f() {
    test_with_extra_checks(Path::new("1233f.exe"), |ctx, analysis| {
        let sprite_array = analysis.sprite_array().unwrap().0;
        assert_eq!(sprite_array, ctx.mem32c(0xeb6098));
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

        assert_eq!(analysis.map_entry_load_map().unwrap().0, 0x005fda80);
        assert_eq!(analysis.map_entry_load_save().unwrap().0, 0x005fd5c0);
        assert_eq!(analysis.map_entry_load_replay().unwrap().0, 0x005fcc00);
        assert_eq!(analysis.create_game_multiplayer().unwrap().0, 0x00721030);
    })
}

#[test]
fn everything_1233g() {
    test_with_extra_checks(Path::new("1233g.exe"), |ctx, analysis| {
        let serialize = analysis.serialize_sprites().unwrap();
        assert_eq!(serialize.0, 0x0057F540);
        let deserialize = analysis.deserialize_sprites().unwrap();
        assert_eq!(deserialize.0, 0x0057E8C0);
        let join_game = analysis.join_game().unwrap();
        assert_eq!(join_game.0, 0x0089D2B0);
        assert_eq!(analysis.prepare_draw_image().unwrap().0, 0x005747f0);
        assert_eq!(analysis.draw_image().unwrap().0, 0x0057be50);
        assert_eq!(analysis.cursor_marker().unwrap(), ctx.mem32c(0xed4994));
        assert_eq!(analysis.allocator().unwrap(), ctx.mem32c(0x10fc81c));
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
        assert_eq!(analysis.tooltip_draw_func().unwrap(), ctx.mem32c(0xee926c));
        assert_eq!(analysis.current_tooltip_ctrl().unwrap(), ctx.mem32c(0xee9270));
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
        assert_eq!(analysis.last_bullet_spawner().unwrap(), ctx.mem32c(0xf823ac));
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
        assert_eq!(analysis.get_mouse_x().unwrap().0, 0x006bf090);
        assert_eq!(analysis.get_mouse_y().unwrap().0, 0x006bf0a0);
        assert_eq!(analysis.status_screen_mode().unwrap(), ctx.mem8c(0x11b7a0e));
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
        assert_eq!(analysis.dat_requirement_error().unwrap(), ctx.mem32c(0xffaad8));
        assert_eq!(analysis.cheat_flags().unwrap(), ctx.mem32c(0x1180f74));
        assert_eq!(analysis.unit_strength().unwrap(), ctx.constant(0xfe8998));

        assert_eq!(analysis.grpwire_grp().unwrap(), ctx.mem32c(0x11cc9a4));
        assert_eq!(analysis.tranwire_grp().unwrap(), ctx.mem32c(0x11cc9a0));
        assert_eq!(analysis.grpwire_ddsgrp().unwrap(), ctx.constant(0x11cc9ac));
        assert_eq!(analysis.tranwire_ddsgrp().unwrap(), ctx.constant(0x11cc9b8));
        assert_eq!(analysis.status_screen().unwrap(), ctx.mem32c(0x11cc9a8));
        assert_eq!(analysis.status_screen_event_handler().unwrap().0, 0x00795590);
        assert_eq!(analysis.init_status_screen().unwrap().0, 0x00795810);
        assert_eq!(analysis.wirefram_ddsgrp().unwrap(), ctx.constant(0x11cd4d4));

        assert_eq!(analysis.trigger_conditions().unwrap().0, 0x00f1b0d8);
        assert_eq!(analysis.trigger_actions().unwrap().0, 0x00f1afe8);
        assert_eq!(analysis.trigger_all_units_cache().unwrap(), ctx.constant(0x00FFE028));
        assert_eq!(analysis.trigger_completed_units_cache().unwrap(), ctx.constant(0x00FFB568));
    })
}

#[test]
fn everything_1235h() {
    test_with_extra_checks(Path::new("1235h.exe"), |ctx, analysis| {
        assert_eq!(analysis.snet_send_packets().unwrap().0, 0x007949f0);
        assert_eq!(analysis.snet_recv_packets().unwrap().0, 0x007976e0);
        assert_eq!(analysis.chk_init_players().unwrap(), ctx.constant(0x11d35d8));
        assert_eq!(analysis.original_chk_player_types().unwrap(), ctx.constant(0x11d0474));
        assert_eq!(analysis.give_ai().unwrap().0, 0x00658300);
    })
}

#[test]
fn everything_1236a() {
    test_with_extra_checks(Path::new("1236a.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1236b() {
    test_with_extra_checks(Path::new("1236b.exe"), |ctx, analysis| {
        assert_eq!(analysis.play_sound().unwrap().0, 0x007b03f0);
        assert_eq!(analysis.ai_prepare_moving_to().unwrap().0, 0x005d1d60);
        assert_eq!(
            analysis.ai_transport_reachability_cached_region().unwrap(),
            ctx.constant(0x010237d0),
        );
        assert_eq!(analysis.player_unit_skins().unwrap(), ctx.constant(0x011fbb50));
        let patch = analysis.replay_minimap_unexplored_fog_patch().unwrap();
        assert_eq!(patch.address.0, 0x007423C7);
        assert_eq!(patch.data, &[0x90, 0x90]);
    })
}

#[test]
fn everything_1237a() {
    test_with_extra_checks(Path::new("1237a.exe"), |ctx, analysis| {
        assert_eq!(analysis.step_replay_commands().unwrap().0, 0x00743750);
        assert_eq!(analysis.replay_data().unwrap(), ctx.mem32c(0x011CF5CC));
        assert_eq!(analysis.ai_step_region().unwrap().0, 0x0064fc90);
        assert_eq!(analysis.ai_spend_money().unwrap().0, 0x0062f090);
        assert_eq!(analysis.ai_train_military().unwrap().0, 0x0064e3c0);
        assert_eq!(analysis.ai_add_military_to_region().unwrap().0, 0x0064cf60);
        assert_eq!(analysis.vertex_buffer().unwrap(), ctx.constant(0x00f5fb18));
    })
}

#[test]
fn everything_1238a() {
    test_with_extra_checks(Path::new("1238a.exe"), |_ctx, _analysis| {
    })
}

#[test]
fn everything_1238b() {
    test_with_extra_checks(Path::new("1238b.exe"), |ctx, analysis| {
        let fastfail = analysis.crt_fastfail();
        assert!(fastfail.iter().any(|x| x.0 == 0xcca86f));
        assert!(fastfail.iter().any(|x| x.0 == 0xcca974));
        assert!(fastfail.iter().any(|x| x.0 == 0xccbb25));
        assert!(fastfail.iter().any(|x| x.0 == 0xcd749d));
        assert!(fastfail.iter().any(|x| x.0 == 0xcd8408));
        assert_eq!(analysis.reset_ui_event_handlers().unwrap().0, 0x006D8910);
        assert_eq!(analysis.ui_default_scroll_handler().unwrap().0, 0x006D8880);
        assert_eq!(analysis.global_event_handlers().unwrap(), ctx.constant(0x011D0A60));
        assert_eq!(analysis.clamp_zoom().unwrap().0, 0x00614c40);
        assert_eq!(analysis.draw_minimap_units().unwrap().0, 0x0073D160);
        assert_eq!(analysis.first_player_unit().unwrap(), ctx.constant(0xffd218));
        assert_eq!(analysis.replay_visions().unwrap(), ctx.mem8c(0x11fe330));
        assert_eq!(
            analysis.replay_show_entire_map().unwrap(),
            ctx.mem32c(0x11fe334),
        );
    })
}

#[test]
fn everything_1238c() {
    test_with_extra_checks(Path::new("1238c.exe"), |ctx, analysis| {
        assert_eq!(analysis.run_menus().unwrap().0, 0x006F3590);
        assert_eq!(analysis.set_briefing_music().unwrap().0, 0x006eceb0);
        assert_eq!(analysis.pre_mission_glue().unwrap().0, 0x006996d0);
        assert_eq!(analysis.show_mission_glue().unwrap().0, 0x00699790);
        assert_eq!(analysis.menu_swish_in().unwrap().0, 0x006f44b0);
        assert_eq!(analysis.menu_swish_out().unwrap().0, 0x006f3c20);
        assert_eq!(analysis.dialog_return_code().unwrap(), ctx.mem32c(0x1201ef0));
        assert_eq!(analysis.ai_spell_cast().unwrap().0, 0x0063bbe0);
        assert_eq!(analysis.give_unit().unwrap().0, 0x006623f0);
        assert_eq!(analysis.set_unit_player().unwrap().0, 0x005b8ae0);
        assert_eq!(analysis.remove_from_selections().unwrap().0, 0x00775e30);
        assert_eq!(analysis.remove_from_client_selection().unwrap().0, 0x005b5e00);
        assert_eq!(analysis.clear_build_queue().unwrap().0, 0x00592640);
        assert_eq!(analysis.unit_changing_player().unwrap().0, 0x005b63f0);
        assert_eq!(analysis.unit_apply_speed_upgrades().unwrap().0, 0x005d9490);
        assert_eq!(analysis.unit_update_speed().unwrap().0, 0x005d9c20);
        assert_eq!(analysis.unit_update_speed_iscript().unwrap().0, 0x005c2f40);
        assert_eq!(analysis.unit_buffed_flingy_speed().unwrap().0, 0x005b8600);
        assert_eq!(analysis.unit_buffed_acceleration().unwrap().0, 0x005b8540);
        assert_eq!(analysis.unit_buffed_turn_speed().unwrap().0, 0x005b85a0);
        assert_eq!(analysis.start_udp_server().unwrap().0, 0x007edbc0);
        assert_eq!(analysis.player_gained_upgrade().unwrap().0, 0x005da500);
        assert_eq!(analysis.open_anim_single_file().unwrap().0, 0x00539f70);
        assert_eq!(analysis.open_anim_multi_file().unwrap().0, 0x0053a560);
        assert_eq!(analysis.init_skins().unwrap().0, 0x00649ff0);
        assert_eq!(analysis.add_asset_change_callback().unwrap().0, 0x0054d670);
        assert_eq!(analysis.anim_asset_change_cb().unwrap().0, 0x0057e0a0);
        assert_eq!(analysis.asset_scale().unwrap(), ctx.mem32c(0xf2cd20));
        assert_eq!(analysis.base_anim_set().unwrap(), ctx.constant(0xfd4448));
        assert_eq!(analysis.image_grps().unwrap(), ctx.constant(0xfc9ab0));
        assert_eq!(analysis.image_overlays().unwrap(), ctx.constant(0xfce598));
        assert_eq!(analysis.fire_overlay_max().unwrap(), ctx.constant(0xfc9688));
        assert_eq!(analysis.vision_update_counter().unwrap(), ctx.mem32c(0x11ab1bc));
        assert_eq!(analysis.vision_updated().unwrap(), ctx.mem8c(0x11ab194));
        assert_eq!(analysis.first_dying_unit().unwrap(), ctx.mem32c(0xfd7260));
        assert_eq!(analysis.active_iscript_flingy().unwrap(), ctx.mem32c(0xfc967c));
        assert_eq!(analysis.step_active_unit_frame().unwrap().0, 0x005d8de0);
        assert_eq!(analysis.first_revealer().unwrap(), ctx.mem32c(0xfd7214));
        assert_eq!(analysis.reveal_unit_area().unwrap().0, 0x005a7730);
        assert_eq!(analysis.step_hidden_unit_frame().unwrap().0, 0x005d9130);
        assert_eq!(analysis.first_invisible_unit().unwrap(), ctx.mem32c(0xfd74a8));
        assert_eq!(analysis.step_bullet_frame().unwrap().0, 0x00572100);
        assert_eq!(analysis.active_iscript_bullet().unwrap(), ctx.mem32c(0xfc9680));
        assert_eq!(analysis.step_unit_movement().unwrap().0, 0x005bf660);
        assert_eq!(analysis.unit_should_reveal_area().unwrap(), ctx.mem32c(0xfd7284));
        assert_eq!(analysis.draw_game_layer().unwrap().0, 0x0060EA70);
        assert_eq!(analysis.prepare_draw_image().unwrap().0, 0x0057a990);
        assert_eq!(analysis.draw_image().unwrap().0, 0x005827d0);
        assert_eq!(analysis.cursor_marker().unwrap(), ctx.mem32c(0xfd70ac));
    })
}

#[test]
fn everything_1238d() {
    test_with_extra_checks(Path::new("1238d.exe"), |ctx, analysis| {
        assert_eq!(analysis.font_cache_render_ascii().unwrap().0, 0x009EFC10);
        assert_eq!(analysis.ttf_cache_character().unwrap().0, 0x009F04C0);
        assert_eq!(analysis.ttf_render_sdf().unwrap().0, 0x009F4A20);
        assert_eq!(analysis.init_real_time_lighting().unwrap().0, 0x0083C750);
        assert_eq!(analysis.asset_scale().unwrap(), ctx.mem32c(0xfa76f4));
        assert_eq!(analysis.cmdicons_ddsgrp().unwrap(), ctx.constant(0x1020AA4));
        assert_eq!(analysis.cmdbtns_ddsgrp().unwrap(), ctx.constant(0x1020A64));
        assert_eq!(analysis.wirefram_ddsgrp().unwrap(), ctx.constant(0x10286c8));
        assert_eq!(analysis.allocator().unwrap(), ctx.mem32c(0xfb990c));

        assert_eq!(analysis.step_network().unwrap().0, 0x00819e00);
        assert_eq!(analysis.render_screen().unwrap().0, 0x009ecd00);
        assert_eq!(analysis.load_pcx().unwrap().0, 0x00918d70);
        assert_eq!(analysis.set_music().unwrap().0, 0x00921BE0);
        assert_eq!(analysis.main_palette().unwrap(), ctx.constant(0x010160B8));
        assert_eq!(analysis.palette_set().unwrap(), ctx.constant(0x01380728));
        assert_eq!(analysis.tfontgam().unwrap(), ctx.constant(0x137f0f0));
        assert_eq!(analysis.sync_data().unwrap(), ctx.constant(0x1031f70));
        assert_eq!(analysis.sync_active().unwrap(), ctx.mem32c(0x01030CEC));
    });
}

#[test]
fn everything_1238e() {
    test_with_extra_checks(Path::new("1238e.exe"), |ctx, analysis| {
        assert_eq!(analysis.first_free_order().unwrap(), ctx.mem32c(0x011b5ac0));
        assert_eq!(analysis.last_free_order().unwrap(), ctx.mem32c(0x011b5ac4));
        assert_eq!(analysis.allocated_order_count().unwrap(), ctx.mem32c(0x011b5ad4));
        assert_eq!(analysis.replay_bfix().unwrap(), ctx.constant(0x00F8B790));
        assert_eq!(analysis.replay_gcfg().unwrap(), ctx.constant(0x01009788));

        assert_eq!(analysis.step_game_loop().unwrap().0, 0x00766530);
        assert_eq!(analysis.step_game_logic().unwrap().0, 0x00766860);
        assert_eq!(analysis.process_events().unwrap().0, 0x0075EC90);
        assert_eq!(analysis.continue_game_loop().unwrap(), ctx.mem8c(0x01009A95));
        assert_eq!(analysis.anti_troll().unwrap(), ctx.constant(0x010098F0));
        assert_eq!(analysis.step_game_frames().unwrap(), ctx.mem32c(0x00F8B9D4));
        assert_eq!(analysis.next_game_step_tick().unwrap(), ctx.mem32c(0x1009a90));
        assert_eq!(analysis.replay_seek_frame().unwrap(), ctx.mem32c(0x1007a98));
    });
}

#[test]
fn everything_1238f() {
    test_with_extra_checks(Path::new("1238f.exe"), |_ctx, analysis| {
        assert_eq!(analysis.map_entry_load_map().unwrap().0, 0x005fcfd0);
        assert_eq!(analysis.map_entry_load_save().unwrap().0, 0x005fcba0);
        assert_eq!(analysis.map_entry_load_replay().unwrap().0, 0x005fc2f0);
        assert_eq!(analysis.create_game_multiplayer().unwrap().0, 0x0072fa70);
    });
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
    for addr in samase_scarf::AddressAnalysis::iter() {
        use samase_scarf::AddressAnalysis::*;
        match addr {
            // special handling
            JoinGame | UnitUpdateSpeed | StartUdpServer | InitSkins | StepGameLoop |
                GetMouseX | GetMouseY => continue,
            _ => (),
        }
        let result = analysis.address_analysis(addr);
        assert!(result.is_some(), "Missing {}", addr.name());
    }
    for op in samase_scarf::OperandAnalysis::iter() {
        use samase_scarf::OperandAnalysis::*;
        let result = analysis.operand_analysis(op);
        match op {
            // special handling
            Units | PlayerUnitSkins | VertexBuffer | Sprites | ReplayBfix | ReplayGcfg |
                AntiTroll | MouseX | MouseY => {
                continue;
            }
            Game | Players | MenuScreenId | BnetController => {
                let result = result.unwrap_or_else(|| panic!("Didn't find {}", op.name()));
                check_game(result, binary, op.name());
            }
            Pathing | CommandUser | IsReplay | LocalPlayerId | LobbyState | DrawCursorMarker |
                FirstAiScript | StatusScreenMode | CheatFlags | ReplayData | RngSeed |
                RngEnable | LoadedSave | FirstFreeSprite | LastFreeSprite | FirstLoneSprite |
                LastLoneSprite | FirstFreeLoneSprite | LastFreeLoneSprite | ScreenX | ScreenY |
                Zoom | FirstFowSprite | LastFowSprite | FirstFreeFowSprite | LastFreeFowSprite |
                FirstActiveUnit | FirstHiddenUnit | MapTileFlags | TooltipDrawFunc |
                CurrentTooltipCtrl | IsMultiplayer | FirstFreeBullet | LastFreeBullet |
                FirstActiveBullet | LastActiveBullet | ActiveIscriptUnit | UniqueCommandUser |
                ReplayVisions | ReplayShowEntireMap | ScMainState | LocalStormPlayerId |
                LocalUniquePlayerId | IsPaused | IsPlacingBuilding | IsTargeting |
                DialogReturnCode | AssetScale | ImagesLoaded | VisionUpdateCounter |
                VisionUpdated | FirstDyingUnit | FirstRevealer | FirstInvisibleUnit |
                ActiveIscriptFlingy | ActiveIscriptBullet | UnitShouldRevealArea |
                NetworkReady | LastBulletSpawner | DatRequirementError | CursorMarker |
                SyncActive | IscriptBin | StormCommandUser | FirstFreeOrder | LastFreeOrder |
                AllocatedOrderCount | ContinueGameLoop | StepGameFrames | ReplaySeekFrame |
                NextGameStepTick =>
            {
                check_global_opt(result, binary, op.name());
            }
            LocalPlayerName | FirstGuardAi | PlayerAiTowns | PlayerAi | Campaigns | Fonts |
                UnitStrength | WireframDdsgrp | ChkInitPlayers | OriginalChkPlayerTypes |
                AiTransportReachabilityCachedRegion | SpriteHlines | SpriteHlinesEnd |
                AiRegions | GraphicLayers | Selections | GlobalEventHandlers | FirstPlayerUnit |
                NetPlayers | NetPlayerToGame | NetPlayerToUnique | GameData | Skins |
                PlayerSkins | ClientSelection | BaseAnimSet | ImageGrps | ImageOverlays |
                FireOverlayMax | NetPlayerFlags | PlayerTurns | PlayerTurnsSize | CmdIconsDdsGrp |
                CmdBtnsDdsGrp | SyncData | PaletteSet | MainPalette | TfontGam =>
            {
                check_global_struct_opt(result, binary, op.name());
            }
        }
    }
    let results = analysis.firegraft_addresses();
    assert_eq!(results.buttonsets.len(), 1);
    assert_eq!(results.unit_status_funcs.len(), 1);
    let filename_str = filename.file_stem().unwrap().to_str().unwrap();
    let minor_version = (&filename_str[1..3]).parse::<u32>().unwrap();
    let is_ptr = filename_str.contains("ptr");
    let (patch_version, revision) = if is_ptr {
        ((filename_str[3..4]).parse::<u32>().unwrap(), b'a')
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

    let aiscript_hook = analysis.aiscript_hook().unwrap();
    assert!(op_register_anywidth(aiscript_hook.opcode_operand).is_some());
    assert_ne!(
        aiscript_hook.opcode_operand,
        aiscript_hook.script_operand_at_switch
    );
    assert_ne!(analysis.rng_seed().unwrap(), analysis.rng_enable().unwrap());

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

    let command_lengths = analysis.command_lengths();
    assert_eq!(command_lengths[0x37], 7);
    assert!(command_lengths.len() >= 0x59);

    let units = analysis.units().unwrap();
    if extended_limits {
        check_global(units, binary, "units");
    } else {
        check_global_struct(units, binary, "units");
    }

    assert!(analysis.step_iscript_hook().is_some());

    let sprite_x_position = analysis.sprite_x_position();
    let sprite_y_position = analysis.sprite_y_position();
    let (x, x_off, x_size) = sprite_x_position.unwrap();
    let (y, y_off, y_size) = sprite_y_position.unwrap();
    let (sprite_array, sprite_size) = analysis.sprite_array().unwrap();
    if extended_limits {
        // Allocated behind a pointer
        check_global(sprite_array, binary, "sprite_array");
    } else {
        // Static array
        check_global_struct(sprite_array, binary, "sprite_array");
    }

    let anim_struct_size = analysis.anim_struct_size().unwrap();
    // Size changed in 1.23.5h (Critical section to Srw lock)
    if minor_version < 23 ||
        (minor_version == 23 && patch_version < 5) ||
        (minor_version == 23 && patch_version == 5 && revision < b'h') ||
        filename_str == "1234_ptr1"
    {
        assert_eq!(anim_struct_size, 0x4c);
    } else {
        assert_eq!(anim_struct_size, 0x38);
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
            check_euds(binary, &euds.euds, "698_euds.txt");
        }
    } else if minor_version == 22 {
        if patch_version < 1 && revision < b'e' {
            // 1220 to 1220d, added logic for editing race sounds?
            assert_eq!(euds.euds.len(), 698);
            check_euds(binary, &euds.euds, "698_euds_2.txt");
        } else if patch_version < 2 {
            // Status screen marked as uneditable(?) from 1220e to 1221c
            assert_eq!(euds.euds.len(), 698);
            check_euds(binary, &euds.euds, "698_euds_3.txt");
        } else {
            // 1222 =>
            assert_eq!(euds.euds.len(), 705);
            check_euds(binary, &euds.euds, "705_euds.txt");
        }
    } else {
        // 1230 =>
        // Removed keystate (00596A18)
        // 0068c204, and mouse pos (006cddc4)
        // They probably are now emulated in a different path not detected by this
        assert_eq!(euds.euds.len(), 702);
        check_euds(binary, &euds.euds, "702_euds.txt");
    }

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

    let (_, size) = analysis.net_players().unwrap();
    assert_eq!(size, 0x68, "sizeof NetPlayer");

    let spawn_dialog = analysis.spawn_dialog();
    let run_dialog = analysis.run_dialog();
    assert_ne!(run_dialog, spawn_dialog);

    let skins_size = analysis.skins_size().unwrap();
    assert_eq!(skins_size, 0x15e);

    let images_loaded = analysis.images_loaded();
    check_global(images_loaded.unwrap(), binary, "images loaded");
    let init_rtl = analysis.init_real_time_lighting();
    assert!(init_rtl.is_some());

    let snp_definitions = analysis.snp_definitions();
    if minor_version < 23 || (minor_version == 23 && patch_version < 3) {
        let snp_definitions = snp_definitions.unwrap();
        check_global_struct(snp_definitions.snp_definitions, binary, "snp definitions");
        assert_eq!(snp_definitions.entry_size, 0x90);
    } else {
        assert!(snp_definitions.is_none());
    }

    let limits = analysis.limits();
    // Currently 1238d, 1238e, but not 1238f.
    // Assuming that 1239a or 1240a will be built on that branch too.
    let is_major_2021_patch =
        (minor_version == 23 && patch_version == 8 && revision >= b'd' && revision <= b'e') ||
        (minor_version == 23 && patch_version >= 9) ||
        (minor_version >= 24);
    if extended_limits {
        assert!(limits.set_limits.is_some());
        // 1238d removed (inlined?) SMemAlloc and SMemFree
        let has_smem_alloc = !is_major_2021_patch;
        // Allocator as a virtual struct was added in 1233a
        let has_allocator = minor_version > 23 ||
            (minor_version == 23 && patch_version >= 3);
        if has_smem_alloc {
            assert!(analysis.smem_alloc().is_some());
            assert!(analysis.smem_free().is_some());
        } else {
            assert!(analysis.smem_alloc().is_none());
            assert!(analysis.smem_free().is_none());
        }
        if has_allocator {
            check_global_opt(analysis.allocator(), binary, "allocator");
        } else {
            assert!(analysis.allocator().is_none());
        }
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
        assert!(analysis.allocator().is_none());
        assert!(limits.set_limits.is_none());
        assert_eq!(limits.arrays.len(), 0);
    }

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

    if has_prism {
        assert_eq!(analysis.prism_vertex_shaders().len(), 0x6);
        assert_eq!(analysis.prism_pixel_shaders().len(), 0x2b);
    } else {
        assert_eq!(analysis.prism_vertex_shaders().len(), 0);
        assert_eq!(analysis.prism_pixel_shaders().len(), 0);
    }

    let join_game = analysis.join_game();
    let join_param_variant_type_offset = analysis.join_param_variant_type_offset();
    // 1233g refactored join_game/it's arguments heavily from what used to resemble 1161,
    // this analysis only finds the new format
    let has_join_game = minor_version > 23 ||
        (minor_version == 23 && patch_version > 3) ||
        (minor_version == 23 && patch_version == 3 && revision >= b'g');
    if has_join_game {
        assert!(join_game.is_some());
        if is_major_2021_patch {
            assert_eq!(join_param_variant_type_offset, Some(0x20));
        } else {
            assert_eq!(join_param_variant_type_offset, Some(0));
        }
    } else {
        assert!(join_game.is_none());
        assert!(join_param_variant_type_offset.is_none());
    }

    let unit_update_speed = analysis.unit_update_speed();
    // Some versions inline unit_update_speed
    // The function has randomly trash added to that function which makes inlining fail,
    // and sometimes it's small enough to be inlined.
    match (minor_version, patch_version, revision) {
        (21, 2, b'b') | (22, 0, b'b') | (22, 0, b'e') | (22, 0, b'g') | (22, 0, b'h') |
            (22, 1, b'b') | (22, 2, b'b') | (22, 2, b'c') | (22, 2, b'd') | (22, 3, b'c') |
            (22, 3, b'e') => assert!(unit_update_speed.is_none()),
        _ => assert!(unit_update_speed.is_some()),
    }

    // While udp server exists in older versions, it has different code that
    // isn't caught by this analysis
    let start_udp_server = analysis.start_udp_server();
    if minor_version > 21 ||
        (minor_version == 21 && patch_version > 4) ||
        (minor_version == 21 && patch_version == 4 && revision >= b'b')
    {
        assert!(start_udp_server.is_some());
    } else {
        assert!(start_udp_server.is_none());
    }

    // 1.23.0 added input abstraction
    let x_func = analysis.get_mouse_x();
    let y_func = analysis.get_mouse_y();
    let x_var = analysis.mouse_x();
    let y_var = analysis.mouse_y();
    if minor_version >= 23 {
        assert!(x_func.is_some());
        assert!(y_func.is_some());
        assert!(x_var.is_none());
        assert!(y_var.is_none());
    } else {
        check_global(x_var.unwrap(), binary, "mouse x");
        check_global(y_var.unwrap(), binary, "mouse y");
        assert!(x_func.is_none());
        assert!(y_func.is_none());
    }

    check_global(analysis.grpwire_grp().unwrap(), binary, "grpwire_grp");
    check_global(analysis.tranwire_grp().unwrap(), binary, "tranwire_grp");
    check_global_struct(analysis.grpwire_ddsgrp().unwrap(), binary, "grpwire_ddsgrp");
    check_global_struct(analysis.tranwire_ddsgrp().unwrap(), binary, "tranwire_ddsgrp");
    check_global(analysis.status_screen().unwrap(), binary, "status_screen");
    assert!(analysis.status_screen_event_handler().is_some());
    assert!(analysis.init_status_screen().is_some());

    assert!(analysis.trigger_conditions().is_some());
    assert!(analysis.trigger_actions().is_some());
    check_global_struct_opt(analysis.trigger_all_units_cache(), binary, "all units cache");
    check_global_struct_opt(
        analysis.trigger_completed_units_cache(),
        binary,
        "completed units cache",
    );

    // Became a thing since 1.23.0 (carbot)
    let skins = analysis.player_unit_skins();
    // Technically existed but wasn't similar before carbot
    let init_skins = analysis.init_skins();
    if minor_version >= 23 {
        check_global_struct_opt(skins, binary, "player_unit_skins");
        assert!(init_skins.is_some());
    } else {
        assert!(skins.is_none());
        assert!(init_skins.is_none());
    }

    // The vertex buffer funcs / struct layout changed slightly in 1.21.2,
    // but it's been stable since then.
    let vertex_buffer = analysis.vertex_buffer();
    if minor_version >= 22 || (minor_version == 21 && patch_version >= 2) {
        check_global_struct_opt(vertex_buffer, binary, "vertex_buffer");
    } else {
        assert!(vertex_buffer.is_none());
    }

    let replay_bfix = analysis.replay_bfix();
    let replay_gcfg = analysis.replay_gcfg();
    // Only from 1.23.3e forward
    if minor_version >= 24 ||
        (minor_version == 23 && patch_version >= 4) ||
        (minor_version == 23 && patch_version == 3 && revision >= b'e')
    {
        check_global_struct_opt(replay_bfix, binary, "replay_bfix");
        check_global_struct_opt(replay_gcfg, binary, "replay_gcfg");
    } else {
        assert!(replay_bfix.is_none());
        assert!(replay_gcfg.is_none());
    }

    assert_eq!(analysis.crt_fastfail().len(), 0x5);

    // Exists from 1.22.4 forward
    let anti_troll = analysis.anti_troll();
    if minor_version >= 23 ||
        (minor_version == 22 && patch_version >= 4)
    {
        check_global_struct_opt(anti_troll, binary, "anti_troll");
    } else {
        assert!(anti_troll.is_none());
    }

    // Inlined before 1.22.2
    let step_game_loop = analysis.step_game_loop();
    if minor_version >= 23 ||
        (minor_version == 22 && patch_version >= 2)
    {
        assert!(step_game_loop.is_some());
    } else {
        assert!(step_game_loop.is_none());
    }

    assert_eq!(analysis.bnet_message_vtable_type(), Some(4));
}

fn op_register_anywidth(op: Operand<'_>) -> Option<u8> {
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

fn check_global_opt<Va: VirtualAddressTrait>(
    op: Option<Operand<'_>>,
    binary: &scarf::BinaryFile<Va>,
    name: &str,
) {
    let op = op.unwrap_or_else(|| {
        panic!("{} not found", name);
    });
    check_global(op, binary, name);
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

/// Checks that all euds in `compare_file` (Generated with --dump-euds) exist.
fn check_euds<Va: VirtualAddressTrait>(
    binary: &scarf::BinaryFile<Va>,
    euds: &[Eud],
    compare_file: &str,
) {
    // addr, size, flags
    fn parse_line(line: &str) -> Option<(u32, u32, u32)> {
        let mut tokens = line.split_whitespace();
        let addr_len = tokens.next()?;
        let addr = addr_len.split(":").nth(0)?;
        let addr = u32::from_str_radix(addr, 16).ok()?;
        let len = addr_len.split(":").nth(1).unwrap_or_else(|| panic!("Line {}", line));
        let len = u32::from_str_radix(len, 16).ok()?;
        let _ = tokens.next()?;
        let _ = tokens.next()?;
        let flags = tokens.next()?;
        let flags = flags.get(1..(flags.len() - 1))?;
        let flags = u32::from_str_radix(flags, 16).ok()?;
        Some((addr, len, flags))
    }

    let mut ok = true;
    let data = std::fs::read(&format!("tests/euds/{}", compare_file)).unwrap();
    let data = String::from_utf8_lossy(&data);
    for line in data.lines().filter(|x| !x.trim().is_empty()) {
        let (addr, size, flags) = parse_line(line)
            .unwrap_or_else(|| panic!("Line {}", line));
        let start_index = euds.binary_search_by(|x| match x.address < addr {
            true => std::cmp::Ordering::Less,
            false => std::cmp::Ordering::Greater,
        }).unwrap_or_else(|e| e);
        let index = euds
            .iter()
            .skip(start_index)
            .take_while(|x| x.address == addr)
            .position(|x| x.size == size)
            .map(|x| x + start_index);
        if let Some(idx) = index {
            let eud = &euds[idx];
            if eud.flags != flags {
                println!(
                    "EUD address {:08x} flags mismatch: got {:08x} expected {:08x}",
                    addr, eud.flags, flags,
                );
                ok = false;
            }
            if let Some(c) = eud.operand.if_constant() {
                let c = Va::from_u64(c);
                if !has_section_for_addr(binary, c) {
                    println!("EUD {:08x} operand {} is outside binary bounds", addr, eud.operand);
                    ok = false;
                }
            } else if let Some(mem) = eud.operand.if_memory() {
                if mem.size.bits() != Va::SIZE * 8 {
                    println!("EUD {:08x} operand {} is not word-sized mem", addr, eud.operand);
                    ok = false;
                }
                if let Some(mem_address) = mem.address.if_constant() {
                    let address_ok = binary.read_address(Va::from_u64(mem_address)).ok()
                        .filter(|&x| has_section_for_addr(binary, x))
                        .is_some();
                    if !address_ok {
                        println!(
                            "EUD {:08x} operand {} is outside binary bounds",
                            addr, eud.operand,
                        );
                        ok = false;
                    }
                } else {
                    println!("EUD {:08x} operand {} is outside binary bounds", addr, eud.operand);
                    ok = false;
                }
            } else {
                println!("EUD {:08x} operand {} is unexpected type", addr, eud.operand);
                ok = false;
            }
        } else {
            println!("EUD address {:08x}:{:x} not found", addr, size);
            ok = false;
        }
    }
    if !ok {
        panic!("EUD check failed");
    }
}

pub fn has_section_for_addr<Va: VirtualAddressTrait>(
    binary: &scarf::BinaryFile<Va>,
    address: Va,
) -> bool {
    binary.sections().any(|x| {
        address >= x.virtual_address && address < (x.virtual_address + x.virtual_size)
    })
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
