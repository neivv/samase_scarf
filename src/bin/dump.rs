extern crate fern;
extern crate log;
extern crate samase_scarf;
extern crate scarf;

use std::io::{self, Write};
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs::read_dir;
use std::path::Path;

use anyhow::{anyhow, Context, Result};
use byteorder::{LittleEndian, ByteOrder};
use rayon::prelude::*;

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, OperandCtx};

use samase_scarf::{Analysis};

/// writeln! that unwraps the result. Since writing to a string won't fail.
macro_rules! out {
    ($($toks:tt)*) => {
        writeln!($($toks)*).expect("Writing failed")
    }
}

struct Args {
    dump_shaders: bool,
    dump_vtables: bool,
    dump_dat_patches: bool,
    dump_euds: bool,
}

fn main() {
    let exe = std::env::args_os().nth(1).unwrap();
    let arg2 = std::env::args_os().nth(2);
    let arg3 = std::env::args_os().nth(3);
    let arg2 = arg2.as_ref();
    let dump_shaders = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-shaders";
        Some(()).filter(|()| ok)
    }).is_some();
    let dump_vtables = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-vtables";
        Some(()).filter(|()| ok)
    }).is_some();
    let dump_dat_patches = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dat-patches";
        Some(()).filter(|()| ok)
    }).is_some();
    let dump_euds = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-euds";
        Some(()).filter(|()| ok)
    }).is_some();
    let should_dump_test_compares = arg2.and_then(|arg| {
        let ok = arg.to_str()? == "--dump-test-compares";
        Some(()).filter(|()| ok)
    }).is_some();
    let no_rtti = arg3.and_then(|arg| {
        let ok = arg.to_str()? == "--no-rtti";
        Some(()).filter(|()| ok)
    }).is_some();

    if should_dump_test_compares {
        let filter = match exe.to_str() {
            Some("-") | None => None,
            Some(s) => Some(s),
        };
        dump_test_compares("tests/code_sections", false, filter).unwrap();
        dump_test_compares("tests/64", true, filter).unwrap();
        return;
    }

    init_stdout_log();
    let args = Args {
        dump_shaders,
        dump_vtables,
        dump_dat_patches,
        dump_euds,
    };

    let start_time;
    if !is_64_bit(Path::new(&exe)) {
        #[cfg(feature = "binaries_32")]
        {
            let binary = get_binary_32(&exe, no_rtti);
            let ctx = &scarf::OperandContext::new();
            start_time = ::std::time::Instant::now();
            let text = dump::<scarf::ExecutionStateX86<'_>>(&binary, ctx, &args);
            println!("{}", text);
        }
        #[cfg(not(feature = "binaries_32"))]
        {
            println!("32-bit support wasn't enabled");
            start_time = ::std::time::Instant::now();
        }
    } else {
        #[cfg(feature = "binaries_64")]
        {
            let binary = get_binary_64(&exe, no_rtti);
            let ctx = &scarf::OperandContext::new();
            start_time = ::std::time::Instant::now();
            let text = dump::<scarf::ExecutionStateX86_64<'_>>(&binary, ctx, &args);
            println!("{}", text);
        }
        #[cfg(not(feature = "binaries_64"))]
        {
            println!("64-bit support wasn't enabled");
            start_time = ::std::time::Instant::now();
        }
    }

    let elapsed = start_time.elapsed();
    println!("Time taken: {}.{:09} s", elapsed.as_secs(), elapsed.subsec_nanos());
}

#[cfg(feature = "binaries_32")]
fn get_binary_32(exe: &OsStr, no_rtti: bool) -> BinaryFile<scarf::VirtualAddress> {
    let mut binary = scarf::parse(&exe).unwrap();
    let relocs =
        scarf::analysis::find_relocs::<scarf::ExecutionStateX86<'_>>(&binary).unwrap();
    binary.set_relocs(relocs);
    if no_rtti {
        let ctx = &scarf::OperandContext::new();
        filter_rtti_pointers::<scarf::ExecutionStateX86<'_>>(&binary, ctx)
    } else {
        binary
    }
}

#[cfg(feature = "binaries_64")]
fn get_binary_64(exe: &OsStr, no_rtti: bool) -> BinaryFile<scarf::VirtualAddress64> {
    let binary = scarf::parse_x86_64(&exe).unwrap();
    if no_rtti {
        let ctx = &scarf::OperandContext::new();
        filter_rtti_pointers::<scarf::ExecutionStateX86_64<'_>>(&binary, ctx)
    } else {
        binary
    }
}

fn filter_rtti_pointers<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
) -> BinaryFile<E::VirtualAddress> {
    let mut analysis = Analysis::<E>::new(binary, ctx);
    let vtables = analysis.vtables();
    let mut sections = binary.sections().map(|s| {
        scarf::BinarySection {
            name: s.name,
            virtual_address: s.virtual_address,
            virtual_size: s.virtual_size,
            data: s.data.clone(),
        }
    }).collect::<Vec<_>>();
    let rdata = sections.iter_mut()
        .find(|x| &x.name == b".rdata\0\0")
        .expect("No .rdata section?");
    for &vtable in &vtables {
        let rtti_address = vtable - E::VirtualAddress::SIZE;
        let index = (rtti_address.as_u64() - rdata.virtual_address.as_u64()) as usize;
        rdata.data[index..][..(E::VirtualAddress::SIZE as usize)].fill(0u8);
    }
    scarf::raw_bin(binary.base(), sections)
}

fn dump<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    args: &Args,
) -> String {
    let mut analysis = Analysis::<E>::new(binary, ctx);

    if args.dump_shaders {
        let path = std::env::args_os().nth(3).unwrap();
        match dump_shaders(&binary, &mut analysis, Path::new(&path)) {
            Ok(()) => return "Shaders dumped".into(),
            Err(e) => {
                eprintln!("Failed to dump shaders: {:?}", e);
                return String::new();
            }
        }
    }
    let mut out = if args.dump_vtables {
        dump_vtables(binary, &mut analysis)
    } else if args.dump_euds {
        samase_scarf::dump::dump_euds(&mut analysis)
    } else if args.dump_dat_patches {
        samase_scarf::dump::dump_dat_patches(&mut analysis, true)
    } else {
        let arg2 = std::env::args_os().nth(2);
        let arg2 = arg2.as_ref();
        let filter = arg2.and_then(|x| x.to_str()).filter(|&x| x != "-");
        samase_scarf::dump::dump(&mut analysis, filter)
    };

    out.push_str("\n");
    let counts = ctx.interned_counts();
    out!(&mut out, "Interned undef count: {}", counts.undefined);
    out!(&mut out, "Interned constant count: {}", counts.constant);
    out!(&mut out, "Interned other count: {}", counts.other);
    out!(&mut out, "Interned total count: {}", counts.total());
    out
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
        #[cfg(windows)]
        d3d_disassemble(path, &name, shader_bin)?;
    }
    Ok(())
}

#[cfg(windows)]
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
) -> String {
    let mut out = String::new();
    let vtables = analysis.vtables();
    out!(&mut out, "{} vtables", vtables.len());
    for vtable in vtables {
        let name = binary.read_address(vtable - E::VirtualAddress::SIZE).ok()
            .and_then(|x| {
                let name_offset = match E::VirtualAddress::SIZE == 4 {
                    true => 0x8,
                    false => 0x10,
                };
                let offset = binary.read_u32(x + 0x4).ok()?;
                let main_name = read_vtable_address(binary, x + 0xc)? + name_offset;
                let inherits = read_vtable_address(binary, x + 0x10)?;
                let inherit_count = binary.read_u32(inherits + 0x8).ok()?;
                let inherit_list = read_vtable_address(binary, inherits + 0xc)?;

                let name = read_cstring(binary, main_name)?;

                let mut inherits = Vec::with_capacity(inherit_count as usize);
                for i in 0..inherit_count {
                    let inherited = read_vtable_address(binary, inherit_list + 4 * i)?;
                    let name = read_vtable_address(binary, inherited)? + name_offset;
                    let name = read_cstring(binary, name)?;
                    let parent_count = binary.read_u32(inherited + 0x4).ok()?;
                    let offset = binary.read_u32(inherited + 0x8).ok()?;
                    inherits.push((name, parent_count, offset));
                }
                Some((name, offset, inherits))
            });
        if let Some((name, offset, inherits)) = name {
            out!(&mut out, "{}: {:08x} @ {:x}", name, vtable.as_u64(), offset);
            for (name, parent_count, offset) in inherits {
                out!(&mut out, "    {}: {:x} @ {:x}", name, parent_count, offset);
            }
        }
    }
    out
}

fn is_64_bit(path: &Path) -> bool {
    let file = std::fs::read(path).unwrap();
    let offset = LittleEndian::read_u32(&file[0x3c..]) as usize;
    LittleEndian::read_u16(&file[offset + 4..]) == 0x8664
}

fn read_cstring<Va: VirtualAddress>(binary: &BinaryFile<Va>, address: Va) -> Option<&str> {
    let slice = binary.slice_from_address_to_end(address).ok()?;
    let end = slice.iter().position(|&x| x == 0)?;
    let name_u8 = &slice[..end];
    std::str::from_utf8(name_u8).ok()
}

fn read_vtable_address<Va: VirtualAddress>(binary: &BinaryFile<Va>, address: Va) -> Option<Va> {
    if Va::SIZE == 4 {
        binary.read_address(address).ok()
    } else {
        binary.read_u32(address).ok().map(|x| binary.base + x)
    }
}

fn dump_test_compares(
    dir: &str,
    is_64: bool,
    filter: Option<&str>,
) -> Result<()> {
    if !is_64 && cfg!(feature = "binaries_32") == false {
        return Ok(());
    }
    if is_64 && cfg!(feature = "binaries_64") == false {
        return Ok(());
    }
    let mut exes = Vec::new();
    for entry in read_dir(dir)? {
        let entry = entry?;
        if !entry.file_type()?.is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().map(|x| x == "exe") != Some(true) {
            continue;
        }
        if let Some(filter) = filter {
            if let Some(stem) = path.file_stem().and_then(|x| x.to_str()) {
                if !stem.contains(filter) {
                    continue;
                }
            }
        }
        exes.push(path);
    }
    exes.into_par_iter().try_for_each(|path| {
        let result = std::panic::catch_unwind(|| {
            let text;
            let start = std::time::Instant::now();
            if !is_64 {
                #[cfg(feature = "binaries_32")]
                {
                    let mut binary = scarf::parse(path.as_os_str()).unwrap();
                    let relocs =
                        scarf::analysis::find_relocs::<scarf::ExecutionStateX86<'_>>(&binary)
                            .unwrap();
                    binary.set_relocs(relocs);
                    let ctx = &scarf::OperandContext::new();
                    let mut analysis = Analysis::<scarf::ExecutionStateX86<'_>>::new(&binary, ctx);
                    text = samase_scarf::dump::dump_all(&mut analysis);
                }
                #[cfg(not(feature = "binaries_32"))] unreachable!();
            } else {
                #[cfg(feature = "binaries_64")]
                {
                    let binary = scarf::parse_x86_64(path.as_os_str()).unwrap();
                    let ctx = &scarf::OperandContext::new();
                    let mut analysis =
                        Analysis::<scarf::ExecutionStateX86_64<'_>>::new(&binary, ctx);
                    text = samase_scarf::dump::dump_all(&mut analysis);
                }
                #[cfg(not(feature = "binaries_64"))] unreachable!();
            }
            let suffix = if !is_64 { "32" } else { "64" };
            let version = path.file_stem().unwrap().to_str().unwrap();
            // Done like this to lock stderr only once, so that
            // the message won't overlap with other threads printing.
            // (Too lazy to do std::io::stderr().lock() etc)
            eprint!("{}", format!("{}-{} done in {:?}\n", suffix, version, start.elapsed()));
            let out_path = format!(
                "tests/compare/{}-{}.txt", version, suffix,
            );
            std::fs::write(out_path, text.as_bytes())?;
            Result::<(), io::Error>::Ok(())
        });
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(e)) => Err(anyhow::Error::from(e)),
            Err(payload) => Err(error_from_panic(payload)),
        }.with_context(|| format!("analysis for {} failed", path.display()))
    })?;
    Ok(())
}

fn error_from_panic(e: Box<dyn std::any::Any + Send + 'static>) -> anyhow::Error {
    match e.downcast::<String>() {
        Ok(s) => anyhow!("An error occured: {}", s),
        Err(e) => match e.downcast::<&'static str>() {
            Ok(s) => anyhow!("An error occured: {}", s),
            _ => anyhow!("An error occured (No other information available)"),
        }
    }
}
