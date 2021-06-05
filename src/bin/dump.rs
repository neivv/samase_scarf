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
    let arg2 = std::env::args_os().nth(2);
    let arg2 = arg2.as_ref();
    let do_dump_shaders = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-shaders";
        Some(()).filter(|()| ok)
    }).is_some();
    let do_dump_vtables = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-vtables";
        Some(()).filter(|()| ok)
    }).is_some();
    let do_dump_dat_patches = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dat-patches";
        Some(()).filter(|()| ok)
    }).is_some();
    let do_dump_euds = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-euds";
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
    if do_dump_euds {
        let euds = analysis.eud_table();
        for eud in &euds.euds {
            println!("{:08x}:{:x} = {} ({:08x})", eud.address, eud.size, eud.operand, eud.flags);
        }
        return;
    }
    if do_dump_dat_patches {
        if let Some(dat_patches) = analysis.dat_patches_debug_data() {
            let mut vec = dat_patches.tables.into_iter().collect::<Vec<_>>();
            vec.sort_by_key(|x| x.0);
            for (dat, debug) in vec {
                // Since Debug for VirtualAddress has the VirtualAddress(0001233) etc,
                // it's distracting to have that much of it.
                let mapped = debug.entry_counts.iter().map(|x| x.as_u64()).collect::<Vec<_>>();
                println!("{:?} entry count patches: {:x?}", dat, mapped);
                println!("{:?} array patches:", dat);
                let orig_arrays_end = debug.array_patches.iter()
                    .take(0x80)
                    .rev()
                    .position(|x| x.len() != 0)
                    .map(|x| debug.array_patches.len().min(0x80) - x)
                    .unwrap_or(0);
                let print_array = |arr: &[(scarf::VirtualAddress, i32, u32)], i: usize| {
                    let all_offsets_zero = arr.iter().all(|x| x.1 == 0 && x.2 == 0);
                    if all_offsets_zero {
                        let mapped = arr.iter().map(|x| x.0.as_u64()).collect::<Vec<_>>();
                        println!("    {:02x}: {:x?}", i, mapped);
                    } else {
                        let mapped = arr.iter()
                            .map(|x| format!("{:x}:{:x}+{:x}", x.0.as_u64(), x.1, x.2))
                            .collect::<Vec<_>>();
                        println!("    {:02x}: {:x?}", i, mapped);
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
            println!("--- Replaces ---");
            for (addr, val) in dat_patches.replaces {
                println!("{:08x} = {:02x?}", addr.as_u64(), &val);
            }
            println!("--- Hooks ---");
            for (addr, skip, val) in dat_patches.hooks {
                println!("{:08x}:{:x} = {:02x?}", addr.as_u64(), skip, val);
            }
            println!("--- Two step hooks ---");
            for (addr, free_space, skip, val) in dat_patches.two_step_hooks {
                println!(
                    "{:08x}:{:x} = {:02x?} (Free @ {:08x})",
                    addr.as_u64(), skip, val, free_space.as_u64(),
                );
            }
            println!("--- Extended array patches ---");
            for (addr, two_step, len, ext_id, operand) in dat_patches.ext_array_patches {
                if let Some(two_step) = two_step {
                    println!(
                        "{:02x}: {:?}:{:x} (Two step {:?}) = {:?}",
                        ext_id, addr, len, two_step, operand,
                    );
                } else {
                    println!("{:02x}: {:?}:{:x} = {:?}", ext_id, addr, len, operand);
                }
            }
            println!("--- Extended array arg patches ---");
            for (addr, args) in dat_patches.ext_array_args {
                println!("{:08x}: {:?}", addr.as_u64(), args);
            }
            println!("--- Grp texture hooks ---");
            for (addr, len, dest, base, index) in dat_patches.grp_texture_hooks {
                println!("{:08x}:{:x}: {} <= {}, {}", addr.as_u64(), len, dest, base, index);
            }
            let mapped = dat_patches.grp_index_hooks.iter()
                .map(|x| format!("{:08x}", x.as_u64()))
                .collect::<Vec<_>>();
            println!("Grp index hooks: {:?}", mapped);
            println!("--- Func replaces ---");
            for (addr, ty) in dat_patches.func_replaces {
                println!("{:08x} = {:?}", addr.as_u64(), ty);
            }
        } else {
            println!("Dat patches analysis failed");
        }
        let elapsed = start_time.elapsed();
        println!("Time taken: {}.{:09} s", elapsed.as_secs(), elapsed.subsec_nanos());
        return;
    }

    let filter = arg2.and_then(|x| x.to_str());

    // Addresses
    let mut lines = Vec::new();
    for address_op in samase_scarf::AddressAnalysis::iter() {
        if let Some(ref filter) = filter {
            if !address_op.name().contains(filter) {
                continue;
            }
        }
        let result = analysis.address_analysis(address_op);
        lines.push((address_op.name(), result));
    }
    lines.sort_unstable_by_key(|x| x.0);
    for &(name, val) in &lines {
        if let Some(addr) = val {
            println!("{}: {:08x}", name, addr.as_u64());
        } else {
            println!("{}: None", name);
        }
    }

    // Operands
    let mut lines = Vec::new();
    for op in samase_scarf::OperandAnalysis::iter() {
        if let Some(ref filter) = filter {
            if !op.name().contains(filter) {
                continue;
            }
        }
        let result = analysis.operand_analysis(op);
        lines.push((op.name(), result));
    }
    lines.sort_unstable_by_key(|x| x.0);
    for &(name, val) in &lines {
        println!("{}: {}", name, format_op_operand(val));
    }

    if filter.is_none() {
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
        let lengths = analysis.command_lengths();
        let lengths = lengths.iter().map(|&x| x as i32).collect::<Vec<_>>();
        println!("command_lengths: len {:x}, {:?}", lengths.len(), lengths);
        let lobby_commands = analysis.process_lobby_commands();
        println!("process_lobby_commands: {:?}", lobby_commands);

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
        println!("portdata.dat: {}", format_dat(&analysis.dat(DatType::PortData)));
        println!("mapdata.dat: {}", format_dat(&analysis.dat(DatType::MapData)));

        let iscript = analysis.step_iscript();
        println!("step_iscript: {:?}", iscript.step_fn);
        println!("step iscript script ptr: {}", format_op_operand(iscript.script_operand_at_switch));
        println!("step iscript switch: {:?}", iscript.switch_table);
        println!("step iscript opcode check: {:?}", iscript.opcode_check);
        println!("iscript_bin: {}", format_op_operand(iscript.iscript_bin));

        let sprite_x_position = analysis.sprite_x_position();
        let sprite_y_position = analysis.sprite_y_position();
        println!("sprite_x: {}", format_op_operand(sprite_x_position.map(|x| x.0)));
        println!("sprite_x_offset: {:x?}", sprite_x_position.map(|x| x.1));
        println!("sprite_x_size: {:x?}", sprite_x_position.map(|x| x.2));
        println!("sprite_y: {}", format_op_operand(sprite_y_position.map(|x| x.0)));
        println!("sprite_y_offset: {:x?}", sprite_y_position.map(|x| x.1));
        println!("sprite_y_size: {:x?}", sprite_x_position.map(|x| x.2));

        let euds = analysis.eud_table();
        println!("{} euds", euds.euds.len());

        let renderer_vtables = analysis.renderer_vtables();
        println!("renderer_vtables: {:?}", renderer_vtables);

        let skins_size = analysis.skins_size().unwrap_or(0);
        println!("skins_size: {:x}", skins_size);

        let snp_definitions = analysis.snp_definitions();
        if let Some(defs) = snp_definitions {
            println!("snp_definitions: {}, {:x} bytes", defs.snp_definitions, defs.entry_size);
        } else {
            println!("snp_definitions: None");
        }

        let sprite_array = analysis.sprite_array();
        println!("sprite_struct_size: {:?}", sprite_array.map(|x| format!("0x{:x}", x.1)));
        let anim_struct_size = analysis.anim_struct_size();
        println!("anim_struct_size: {:?}", anim_struct_size.map(|x| format!("0x{:x}", x)));

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

        let offset = analysis.create_game_dialog_vtbl_on_multiplayer_create();
        println!("CreateGameScreen.on_multiplayer_create offset: {:x?}", offset);

        println!("Prism vertex shader sets: 0x{:x}", analysis.prism_vertex_shaders().len());
        println!("Prism pixel shader sets: 0x{:x}", analysis.prism_pixel_shaders().len());
        println!(
            "Prism vertex shaders: {:x?}",
            analysis.prism_vertex_shaders().iter().map(|x| x.as_u64()).collect::<Vec<_>>(),
        );
        println!(
            "Prism pixel shaders: {:x?}",
            analysis.prism_pixel_shaders().iter().map(|x| x.as_u64()).collect::<Vec<_>>(),
        );

        println!("set_status_screen_tooltip: {:?}", analysis.set_status_screen_tooltip());

        println!("SMemAlloc: {:?}", analysis.smem_alloc());
        println!("SMemFree: {:?}", analysis.smem_free());
        println!("allocator: {:?}", format_op_operand(analysis.allocator()));

        let mouse_xy = analysis.mouse_xy();
        println!("mouse_x: {}", format_op_operand(mouse_xy.x_var));
        println!("mouse_y: {}", format_op_operand(mouse_xy.y_var));
        println!("get_mouse_x: {:?}", mouse_xy.x_func);
        println!("get_mouse_y: {:?}", mouse_xy.y_func);

        println!("grpwire_grp: {}", format_op_operand(analysis.grpwire_grp()));
        println!("grpwire_ddsgrp: {}", format_op_operand(analysis.grpwire_ddsgrp()));
        println!("tranwire_grp: {}", format_op_operand(analysis.tranwire_grp()));
        println!("tranwire_ddsgrp: {}", format_op_operand(analysis.tranwire_ddsgrp()));
        println!("status_screen: {}", format_op_operand(analysis.status_screen()));
        println!("status_screen_event_handler: {:?}", analysis.status_screen_event_handler());
        println!("init_status_screen: {:?}", analysis.init_status_screen());

        println!("trigger_conditions: {:?}", analysis.trigger_conditions());
        println!("trigger_actions: {:?}", analysis.trigger_actions());
        println!("trigger_all_units_cache: {}", format_op_operand(analysis.trigger_all_units_cache()));
        println!(
            "trigger_completed_units_cache: {}",
            format_op_operand(analysis.trigger_completed_units_cache()),
        );

        let patch = analysis.replay_minimap_unexplored_fog_patch();
        println!(
            "replay_minimap_unexplored_fog_patch: {:x?}",
            patch.as_ref().map(|x| (x.address, &x.data)),
        );

        println!("crt_fastfail: {:?}", analysis.crt_fastfail());
    }

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
