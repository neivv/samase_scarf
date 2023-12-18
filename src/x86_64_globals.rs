use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::RelocValues;
use scarf::exec_state::VirtualAddress;
use scarf::BinaryFile;

use crate::x86_64_instruction_info;

// Checked if 0x1 or 0x2 bit is set, 0x2 means that previous opcode must be 0xf.
// 0xf0 is opcode bit for next opcode (So 0x10 expect 0x30 for 0x0f)
// Everything should have 0x10 bit set since can't know if 0x0f
// from previous byte is 0x0f prefix or just unrelated data
// from previous instruction's end.
static CHECKED_OPCODES: [u8; 0x100] = [
    /* 00 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 08 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x30,
    /* 10 */ 0x12, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 18 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 20 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 28 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 30 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 38 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 40 */ 0x10, 0x10, 0x12, 0x12,  0x12, 0x12, 0x12, 0x12,
    /* 48 */ 0x12, 0x12, 0x10, 0x10,  0x12, 0x12, 0x12, 0x12,
    /* 50 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 58 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 60 */ 0x10, 0x10, 0x10, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 68 */ 0x10, 0x11, 0x10, 0x11,  0x10, 0x10, 0x10, 0x10,
    /* 70 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 78 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 80 */ 0x11, 0x11, 0x10, 0x11,  0x11, 0x11, 0x11, 0x11,
    /* 88 */ 0x11, 0x11, 0x11, 0x11,  0x10, 0x11, 0x10, 0x10,
    /* 90 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* 98 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* a0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* a8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* b0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x12, 0x12,
    /* b8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x12, 0x12,
    /* c0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x11, 0x11,
    /* c8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* d0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* d8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* e0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* e8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x10, 0x10,
    /* f0 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x11, 0x11,
    /* f8 */ 0x10, 0x10, 0x10, 0x10,  0x10, 0x10, 0x11, 0x11,
];

// Note: f6 and f7 have imm sizes 1/4 if `second_byte >> 3` < 2
// The search code will adjust for it when pushing the result.
static IMM_SIZE: [u8; 0x100] = [
    /* 00 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 10 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 20 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 30 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 40 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 50 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 60 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 4, 0, 1,  0, 0, 0, 0,
    /* 70 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 80 */ 1, 4, 0, 1,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 90 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* a0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* b0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* c0 */ 0, 0, 0, 0,  0, 0, 1, 4,  0, 0, 0, 0,  0, 0, 0, 0,
    /* d0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* e0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* f0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
];

// Called only once and not inlining can help register allocation in the hot loop?
#[inline(never)]
pub fn x86_64_globals<Va: VirtualAddress>(binary: &BinaryFile<Va>) -> Vec<RelocValues<Va>> {
    let mut out = Vec::with_capacity(0x20000);
    let text = binary.section(b".text\0\0\0").unwrap();
    let data = binary.section(b".data\0\0\0").unwrap();
    let rdata = binary.section(b".rdata\0\0").unwrap();
    // Magic section "!" for zero initialized part of .data, samase uses that to reduce
    // amount of data that has to be searched for static globals.
    let extra_data = binary.section(b"!\0\0\0\0\0\0\0");
    let global_min = data.virtual_address.min(rdata.virtual_address).min(text.virtual_address);
    let mut global_max = (data.virtual_address + data.virtual_size)
        .max(rdata.virtual_address + rdata.virtual_size)
        .max(text.virtual_address + text.virtual_size);
    if let Some(extra) = extra_data {
        global_max = global_max.max(extra.virtual_address + extra.virtual_size);
    }

    let mut last = Va::from_u64(0);
    let base = binary.base();
    let checked_opcodes: &[u8; 0x100] = &CHECKED_OPCODES;
    let mut opcode_bit = 0x1;
    let text_data = &text.data[..];
    // text_data.windows(8) would be nice but this optimizes better
    // (Even if the get() has one unneeded jump)
    for text_pos in 0usize.. {
        // Check either
        // ModR/M & c7 == 5 (5, d, 15, 1d, 25, 2d, 35, 3d)
        //     for rip rel
        // ModR/M & c7 == 4 (4, c, 14, 1c, 24, 2c, 34, 3c), SIB & 7 == 5
        //     for SIB with disp32 offset
        // ModR/M & c7 == 84 (84, 8c, 94, 9c, a4, ac, b4, bc)
        //     for SIB with disp32 offset (and another register)
        // ModR/M & c0 == 80 (Discounting above c7 == 84)
        //      Single register with disp32 offset
        //      (Rare, even if it matches 0x38 out of 0x100 modrm bytes)
        // Written like this to have 1 branch at start that very likely fails the check.
        // This also lets through ModR/M & c7 == 85, but the amount of false
        // positives it has is low enough (1% of total results) that going
        // to leave them as they are.
        //
        // Considering 3 conditions that must pass:
        //      Edit: Outdated, now also has D for modrm & 0xc0 == 80
        // A = (CHECKED_OPCODES[win[1] as usize])
        //
        // B = (b.wrapping_sub(4) < 2) != 0
        // C = ((b == 5) | (win[3] & 7 == 5) | (modrm & 0x80 != 0))
        // Data from ~50 sample exes shows these rates of condition not passing
        // for a single iteration of the loop:
        // A: 61.1%-61.9%
        // B: 88.8%-89.4%
        // C: 51.6%-52.4%
        // A & B: 96.6%-96.9%
        // A & C: 82.3%-82.9%
        // B & C: 92.6%-93.2%
        // A & B & C: 97.2%-97.5%
        // So checking for A & B first gives already very good accuracy; only
        // about 0.5% of iterations will pass that but fail at condition C.
        // A & B are also less work to calculate than C, and C also can be
        // reduced a bit since definition of `value` depends on whether `b == 5`
        // or not, and `b == 5` is one of the subconditions of C.
        //
        // For future considerations using simd, rate of 16-byte blocks having
        // no byte for which condition does pass:
        // A: 0.931%-1.07%
        // B: 19.8%-21.6%
        // C: 0.525%-0.613%
        // A & B: 62.2%-65.0%
        // A & C: 7.95%-8.62%
        // B & C: 36.8%-39.0%
        // A & B & C: 67.6%-70.4%
        // So about one in three 16-byte blocks needs to be examined further.
        // Evaluating A with simd is not possible without gather instructions
        // (On x86 requires AVX512, and even then there's just i32/i64 sized gathers),
        // so choices are pretty much just checking B, skipping 20% of blocks,
        // or B & C for 40% skip rate. Seems pretty bad for branch predictor,
        // but reduction in instruction counts should still make it worth it?
        // Checking for either variation of `value >= global_min && value < global_max`
        // has ~88% rate of not passing, ~69% if done at 4 values at once.
        // Maybe 4 values at once combined with B / C would be a fine alternative too?

        let win: &[u8; 8] = match text_data.get(..text_pos.wrapping_add(8))
            .and_then(|x| x.get(text_pos..)?.try_into().ok())
        {
            Some(s) => s,
            None => break,
        };
        let opcode = win[0] as usize;
        let modrm = win[1];
        let b = modrm & 0x47;
        let d = (modrm >> 6) == 2;
        let checked_opcodes_data = checked_opcodes[opcode];
        let ok = checked_opcodes_data & opcode_bit != 0 && (d || (b.wrapping_sub(4) < 2));
        opcode_bit = checked_opcodes_data >> 4;
        if ok {
            let value = if b != 4 {
                // No SIB, either RIP-relative or the rare case where
                // `lea [base_reg + constant]` is used
                let offset = LittleEndian::read_u32(&win[2..]);
                if !d {
                    // RIP-relative
                    let end_pos = (text_pos as u32).wrapping_add(6)
                        .wrapping_add(IMM_SIZE[opcode].into());
                    text.virtual_address + end_pos.wrapping_add(offset)
                } else {
                    base + offset
                }
            } else {
                if ((win[2] & 7 == 5) | (modrm & 0x80 != 0)) == false {
                    // condition C didn't pass.
                    continue;
                }
                // SIB offset, assuming that one of registers contains binary base
                let offset = LittleEndian::read_u32(&win[3..]);
                base + offset
            };
            if value >= global_min && value < global_max {
                // Fix f6 / f7 where there can be an immediate depending on modrm byte.
                let value = if opcode.wrapping_sub(0xf6) < 2 && ((modrm >> 3) & 7) < 2 && b != 4 {
                    if opcode & 1 == 0 {
                        value + 1
                    } else {
                        value + 4
                    }
                } else {
                    value
                };
                let offset_pos = if b != 4 { 2 } else { 3 };
                let address = text.virtual_address + text_pos as u32 + offset_pos;
                // Same address can match SIB [reg + reg2 * N + C] first at `text_pos`
                // and [reg + C] at `text_pos + 1` depending on exact bytes.
                // But constant should be same anyway so it would be just a duplicate.
                //
                // Technically it may match RIP-relative and constant offset with
                // both values being valid globals, but hopefully that is too rare
                // to care about..
                // Could change the if condition to `address != last || !d` ?
                if address != last {
                    last = address;
                    out.push(RelocValues {
                        address,
                        value,
                    });
                }
            }
        }
    }
    // Note: Even if the globals_with_values list is sorted again at analysis.rs, sorting
    // here ends up reducing the time spent to sort the full global list a lot.
    out.sort_unstable_by_key(|x| x.value);
    out
}

/// Returns instruction immediate value size, at least sometimes =)
/// (Used by dat patches, and since this uses immediate size array already
/// it could be kinda reused)
pub fn immediate_size_approx(bytes: &[u8; 0x10]) -> u32 {
    let mut is_16bit = false;
    let mut pos = 0;
    loop {
        if x86_64_instruction_info::is_prefix(bytes[pos]) {
            is_16bit |= bytes[pos] == 0x66;
        } else {
            break;
        }
        if pos > 0xc {
            // ???
            return 0;
        }
        pos += 1;
    }
    let opcode = bytes[pos] as usize;
    let size = IMM_SIZE[opcode];
    if opcode == 0xf6 || opcode == 0xf7 {
        let modrm = bytes[pos + 1] as usize;
        if (modrm >> 3) & 7 < 2 {
            if opcode & 1 == 0 {
                1
            } else {
                if is_16bit {
                    2
                } else {
                    4
                }
            }
        } else {
            0
        }
    } else {
        // if is_16bit && size == 4 { 2 } else { size },
        // as it's known that `size` is only 1 or 4.
        let size = size as u32;
        (size >> (is_16bit as u32)) | (size & 1)
    }
}
