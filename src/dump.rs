use std::fmt::Write as _;

use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{Analysis, DatType};

/// writeln! that unwraps the result. Since writing to a string won't fail.
macro_rules! out {
    ($($toks:tt)*) => {
        writeln!($($toks)*).expect("Writing failed")
    }
}

pub fn dump<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    filter: Option<&str>,
) -> String {
    let mut out = String::new();
    // Addresses
    let mut lines = Vec::new();
    for address_op in crate::AddressAnalysis::iter() {
        if !check_filter(&filter, address_op.name()) {
            continue;
        }
        let result = analysis.address_analysis(address_op);
        lines.push((address_op.name(), result));
    }
    lines.sort_unstable_by_key(|x| x.0);
    for &(name, val) in &lines {
        if let Some(addr) = val {
            out!(&mut out, "{}: {:08x}", name, addr.as_u64());
        } else {
            out!(&mut out, "{}: None", name);
        }
    }

    // Operands
    let mut lines = Vec::new();
    for op in crate::OperandAnalysis::iter() {
        if !check_filter(&filter, op.name()) {
            continue;
        }
        let result = analysis.operand_analysis(op);
        lines.push((op.name(), result));
    }
    lines.sort_unstable_by_key(|x| x.0);
    for &(name, val) in &lines {
        out!(&mut out, "{}: {}", name, format_op_operand(val));
    }

    if check_filter(&filter, "join_param_variant_type_offset") {
        out!(
            &mut out, "join_param_variant_type_offset: {}",
            analysis.join_param_variant_type_offset()
                .map(|x| format!("{:x}", x))
                .unwrap_or_else(|| String::from("None")),
        );
    }
    if check_filter(&filter, "bnet_message_vtable_type") {
        out!(&mut out, "bnet_message_vtable_type: {:x?}", analysis.bnet_message_vtable_type());
    }
    if check_filter(&filter, "bnet_message_switch") {
        let val = analysis.bnet_message_switch_op();
        out!(&mut out, "bnet_message_switch: {}", format_op_operand(val));
    }

    if filter.is_none() {
        let mut firegraft = (*analysis.firegraft_addresses()).clone();
        firegraft.requirement_table_refs.units.sort_unstable();
        firegraft.requirement_table_refs.upgrades.sort_unstable();
        firegraft.requirement_table_refs.tech_use.sort_unstable();
        firegraft.requirement_table_refs.tech_research.sort_unstable();
        firegraft.requirement_table_refs.orders.sort_unstable();
        out!(&mut out, "Buttonsets: {:?}", firegraft.buttonsets);
        out!(&mut out, "Unit status: {:?}", firegraft.unit_status_funcs);
        out!(
            &mut out,
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
        out!(&mut out, "Aiscript hook: {:#?}", aiscript_hook);
        let step_order_hidden = analysis.step_order_hidden();
        out!(&mut out, "step_order_hidden: {:?}", step_order_hidden);
        let step_secondary = analysis.step_secondary_order();
        out!(&mut out, "step_secondary_order: {:?}", step_secondary);
        let lengths = analysis.command_lengths();
        let lengths = lengths.iter().map(|&x| x as i32).collect::<Vec<_>>();
        out!(&mut out, "command_lengths: len {:x}, {:?}", lengths.len(), lengths);

        let format_dat = |val: &Option<crate::DatTablePtr>| {
            if let Some(x) = val {
                format!("{} (entry size {})", x.address, x.entry_size)
            } else {
                format!("None")
            }
        };
        out!(&mut out, "units.dat: {}", format_dat(&analysis.dat(DatType::Units)));
        out!(&mut out, "weapons.dat: {}", format_dat(&analysis.dat(DatType::Weapons)));
        out!(&mut out, "flingy.dat: {}", format_dat(&analysis.dat(DatType::Flingy)));
        out!(&mut out, "sprites.dat: {}", format_dat(&analysis.dat(DatType::Sprites)));
        out!(&mut out, "images.dat: {}", format_dat(&analysis.dat(DatType::Images)));
        out!(&mut out, "orders.dat: {}", format_dat(&analysis.dat(DatType::Orders)));
        out!(&mut out, "upgrades.dat: {}", format_dat(&analysis.dat(DatType::Upgrades)));
        out!(&mut out, "techdata.dat: {}", format_dat(&analysis.dat(DatType::TechData)));
        out!(&mut out, "sfxdata.dat: {}", format_dat(&analysis.dat(DatType::SfxData)));
        out!(&mut out, "portdata.dat: {}", format_dat(&analysis.dat(DatType::PortData)));
        out!(&mut out, "mapdata.dat: {}", format_dat(&analysis.dat(DatType::MapData)));

        let iscript_hook = analysis.step_iscript_hook();
        out!(&mut out, "step iscript hook: {:?}", iscript_hook);

        let sprite_x_position = analysis.sprite_x_position();
        let sprite_y_position = analysis.sprite_y_position();
        out!(&mut out, "sprite_x: {}", format_op_operand(sprite_x_position.map(|x| x.0)));
        out!(&mut out, "sprite_x_offset: {:x?}", sprite_x_position.map(|x| x.1));
        out!(&mut out, "sprite_x_size: {:x?}", sprite_x_position.map(|x| x.2));
        out!(&mut out, "sprite_y: {}", format_op_operand(sprite_y_position.map(|x| x.0)));
        out!(&mut out, "sprite_y_offset: {:x?}", sprite_y_position.map(|x| x.1));
        out!(&mut out, "sprite_y_size: {:x?}", sprite_x_position.map(|x| x.2));

        let euds = analysis.eud_table();
        out!(&mut out, "{} euds", euds.euds.len());

        let renderer_vtables = analysis.renderer_vtables();
        out!(&mut out, "renderer_vtables: {:?}", renderer_vtables);

        let skins_size = analysis.skins_size().unwrap_or(0);
        out!(&mut out, "skins_size: {:x}", skins_size);

        let snp_definitions = analysis.snp_definitions();
        if let Some(defs) = snp_definitions {
            out!(
                &mut out, "snp_definitions: {}, {:x} bytes",
                defs.snp_definitions, defs.entry_size,
            );
        } else {
            out!(&mut out, "snp_definitions: None");
        }

        let sprite_array = analysis.sprite_array();
        out!(
            &mut out, "sprite_struct_size: {:?}",
            sprite_array.map(|x| format!("0x{:x}", x.1)),
        );
        let anim_struct_size = analysis.anim_struct_size();
        out!(
            &mut out, "anim_struct_size: {:?}",
            anim_struct_size.map(|x| format!("0x{:x}", x)),
        );

        let limits = analysis.limits();
        out!(&mut out, "set_limits: {:?}", limits.set_limits);
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
            out!(&mut out, "limits.{}: {:?}", name, arr);
        }

        let offset = analysis.create_game_dialog_vtbl_on_multiplayer_create();
        out!(&mut out, "CreateGameScreen.on_multiplayer_create offset: {:x?}", offset);

        out!(
            &mut out, "Prism vertex shader sets: 0x{:x}",
            analysis.prism_vertex_shaders().len()
        );
        out!(
            &mut out, "Prism pixel shader sets: 0x{:x}",
            analysis.prism_pixel_shaders().len(),
        );
        out!(
            &mut out, "Prism vertex shaders: {:x?}",
            analysis.prism_vertex_shaders().iter().map(|x| x.as_u64()).collect::<Vec<_>>(),
        );
        out!(
            &mut out, "Prism pixel shaders: {:x?}",
            analysis.prism_pixel_shaders().iter().map(|x| x.as_u64()).collect::<Vec<_>>(),
        );

        out!(
            &mut out, "set_status_screen_tooltip: {:?}",
            analysis.set_status_screen_tooltip(),
        );

        out!(&mut out, "SMemAlloc: {:?}", analysis.smem_alloc());
        out!(&mut out, "SMemFree: {:?}", analysis.smem_free());
        out!(&mut out, "allocator: {}", format_op_operand(analysis.allocator()));

        out!(&mut out, "trigger_conditions: {:?}", analysis.trigger_conditions());
        out!(&mut out, "trigger_actions: {:?}", analysis.trigger_actions());
        out!(
            &mut out, "trigger_all_units_cache: {}",
            format_op_operand(analysis.trigger_all_units_cache()),
        );
        out!(
            &mut out, "trigger_completed_units_cache: {}",
            format_op_operand(analysis.trigger_completed_units_cache()),
        );

        let patch = analysis.replay_minimap_unexplored_fog_patch();
        out!(
            &mut out, "replay_minimap_unexplored_fog_patch: {:x?}",
            patch.as_ref().map(|x| (x.address, &x.data)),
        );

        out!(&mut out, "crt_fastfail: {:?}", analysis.crt_fastfail());
    }
    out
}

pub fn dump_dat_patches<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> String {
    let mut out = String::new();
    if let Some(dat_patches) = analysis.dat_patches_debug_data() {
        let mut vec = dat_patches.tables.into_iter().collect::<Vec<_>>();
        vec.sort_by_key(|x| x.0);
        for (dat, debug) in vec {
            // Since Debug for VirtualAddress has the VirtualAddress(0001233) etc,
            // it's distracting to have that much of it.
            let mapped = debug.entry_counts.iter().map(|x| x.as_u64()).collect::<Vec<_>>();
            out!(&mut out, "{:?} entry count patches: {:x?}", dat, mapped);
            out!(&mut out, "{:?} array patches:", dat);
            let orig_arrays_end = debug.array_patches.iter()
                .take(0x80)
                .rev()
                .position(|x| x.len() != 0)
                .map(|x| debug.array_patches.len().min(0x80) - x)
                .unwrap_or(0);
            let mut print_array = |arr: &[(E::VirtualAddress, i32, u32)], i: usize| {
                let all_offsets_zero = arr.iter().all(|x| x.1 == 0 && x.2 == 0);
                if all_offsets_zero {
                    let mapped = arr.iter().map(|x| x.0.as_u64()).collect::<Vec<_>>();
                    out!(&mut out, "    {:02x}: {:x?}", i, mapped);
                } else {
                    let mapped = arr.iter()
                        .map(|x| format!("{:x}:{:x}+{:x}", x.0.as_u64(), x.1, x.2))
                        .collect::<Vec<_>>();
                    out!(&mut out, "    {:02x}: {:x?}", i, mapped);
                }
            };
            if orig_arrays_end != 0 {
                for (i, arr) in debug.array_patches.iter().enumerate().take(orig_arrays_end) {
                    print_array(&arr, i);
                }
            }
            if debug.array_patches.len() > 0x80 {
                let ext_arrays_start = debug.array_patches.iter().skip(0x80)
                    .position(|x| x.len() != 0)
                    .map(|x| 0x80 + x)
                    .unwrap_or(debug.array_patches.len());
                for (i, arr) in debug.array_patches.iter()
                    .enumerate()
                    .skip(ext_arrays_start)
                {
                    print_array(&arr, i);
                }
            }
        }
        out!(&mut out, "--- Replaces ---");
        for (addr, val) in dat_patches.replaces {
            out!(&mut out, "{:08x} = {:02x?}", addr.as_u64(), &val);
        }
        out!(&mut out, "--- Hooks ---");
        for (addr, skip, val) in dat_patches.hooks {
            out!(&mut out, "{:08x}:{:x} = {:02x?}", addr.as_u64(), skip, val);
        }
        out!(&mut out, "--- Two step hooks ---");
        for (addr, free_space, skip, val) in dat_patches.two_step_hooks {
            out!(
                &mut out, "{:08x}:{:x} = {:02x?} (Free @ {:08x})",
                addr.as_u64(), skip, val, free_space.as_u64(),
            );
        }
        out!(&mut out, "--- Extended array patches ---");
        for (addr, two_step, len, ext_id, operand) in dat_patches.ext_array_patches {
            if let Some(two_step) = two_step {
                out!(
                    &mut out, "{:02x}: {:?}:{:x} (Two step {:?}) = {:?}",
                    ext_id, addr, len, two_step, operand,
                );
            } else {
                out!(&mut out, "{:02x}: {:?}:{:x} = {:?}", ext_id, addr, len, operand);
            }
        }
        out!(&mut out, "--- Extended array arg patches ---");
        for (addr, args) in dat_patches.ext_array_args {
            out!(&mut out, "{:08x}: {:?}", addr.as_u64(), args);
        }
        out!(&mut out, "--- Grp texture hooks ---");
        for (addr, len, dest, base, index) in dat_patches.grp_texture_hooks {
            out!(
                &mut out, "{:08x}:{:x}: {} <= {}, {}",
                addr.as_u64(), len, dest, base, index,
            );
        }
        let mapped = dat_patches.grp_index_hooks.iter()
            .map(|x| format!("{:08x}", x.as_u64()))
            .collect::<Vec<_>>();
        out!(&mut out, "Grp index hooks: {:?}", mapped);
        out!(&mut out, "--- Func replaces ---");
        for (addr, ty) in dat_patches.func_replaces {
            out!(&mut out, "{:08x} = {:?}", addr.as_u64(), ty);
        }
    } else {
        out!(&mut out, "Dat patches analysis failed");
    }
    out
}

pub fn dump_euds<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> String {
    let euds = analysis.eud_table();
    let mut out = String::new();
    for eud in &euds.euds {
        out!(
            &mut out, "{:08x}:{:x} = {} ({:08x})",
            eud.address, eud.size, eud.operand, eud.flags,
        );
    }
    out
}

fn check_filter(filter: &Option<&str>, compare: &str) -> bool {
    if let Some(ref filter) = filter {
        if !compare.contains(filter) {
            return false;
        }
    }
    true
}

fn format_op_operand(op: Option<scarf::Operand>) -> String {
    op.as_ref().map(|x| x.to_string()).unwrap_or_else(|| "None".into())
}

pub fn dump_all<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> String {
    let main = dump(analysis, None);
    let euds = dump_euds(analysis);
    let dat = dump_dat_patches(analysis);
    format!(
        "-- Main --\n\
        {}\n\
        -- Euds --\n\
        {}\n\
        -- Dat patches --\n\
        {}",
        main, euds, dat,
    )
}
