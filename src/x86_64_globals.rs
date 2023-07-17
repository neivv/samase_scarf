use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::RelocValues;
use scarf::exec_state::VirtualAddress;
use scarf::BinaryFile;

static CHECKED_OPCODES: [u8; 0x100] = [
    /* 00 */ 1, 1, 1, 1,  0, 0, 0, 0,  1, 1, 1, 1,  0, 0, 0, 0,
    /* 10 */ 1, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 20 */ 1, 1, 1, 1,  0, 0, 0, 0,  1, 1, 1, 1,  0, 0, 0, 0,
    /* 30 */ 1, 1, 1, 1,  0, 0, 0, 0,  1, 1, 1, 1,  0, 0, 0, 0,
    /* 40 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 50 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 60 */ 0, 0, 0, 1,  0, 0, 0, 0,  0, 1, 0, 1,  0, 0, 0, 0,
    /* 70 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* 80 */ 1, 1, 0, 1,  1, 1, 1, 1,  1, 1, 1, 1,  0, 1, 0, 0,
    /* 90 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* a0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* b0 */ 0, 0, 0, 0,  0, 0, 1, 1,  0, 0, 0, 0,  0, 0, 1, 1,
    /* c0 */ 0, 0, 0, 0,  0, 0, 1, 1,  0, 0, 0, 0,  0, 0, 0, 0,
    /* d0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* e0 */ 0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,
    /* f0 */ 0, 0, 0, 0,  0, 0, 1, 1,  0, 0, 0, 0,  0, 0, 1, 1,
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

    let mut text_pos = 0u32;
    for win in text.data.windows(8) {
        // Check either
        // ModR/M & c7 == 5 (5, d, 15, 1d, 25, 2d, 35, 3d)
        //     for rip rel
        // ModR/M & c7 == 4 (4, c, 14, 1c, 24, 2c, 34, 3c), SIB & 7 == 5
        //     for SIB with disp32 offset
        // ModR/M & c7 == 84 (84, 8c, 94, 9c, a4, ac, b4, bc)
        //     for SIB with disp32 offset (and another register)
        // Written like this to have 1 branch at start that very likely fails the check.
        // This also lets through ModR/M & c7 == 85, but the amount of false
        // positives it has is low enough (1% of total results) that going
        // to leave them as they are.
        //
        // Considering 3 conditions that must pass:
        // A = (CHECKED_OPCODES[win[1] as usize])
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
        let modrm = win[2];
        let opcode = win[1] as usize;
        let b = modrm & 0x47;
        let ok = (CHECKED_OPCODES[opcode]) &
            (b.wrapping_sub(4) < 2) as u8;
        if ok != 0 {
            let offset_pos;
            let value = if b == 5 {
                // RIP-relative
                let offset = LittleEndian::read_u32(&win[3..]);
                offset_pos = 3;
                let end_pos = text_pos.wrapping_add(7)
                    .wrapping_add(IMM_SIZE[win[1] as usize].into());
                text.virtual_address + end_pos.wrapping_add(offset)
            } else {
                if ((win[3] & 7 == 5) | (modrm & 0x80 != 0)) == false {
                    // condition C didn't pass.
                    text_pos = text_pos.wrapping_add(1);
                    continue;
                }
                // SIB offset, assuming that one of registers contains binary base
                let offset = LittleEndian::read_u32(&win[4..]);
                offset_pos = 4;
                binary.base() + offset
            };
            if value >= global_min && value < global_max {
                // Fix f6 / f7 where there can be an immediate depending on modrm byte.
                let value = if opcode.wrapping_sub(0xf6) < 2 && (modrm >> 3) < 2 && b == 5 {
                    if opcode & 1 == 0 {
                        value + 1
                    } else {
                        value + 4
                    }
                } else {
                    value
                };
                out.push(RelocValues {
                    address: text.virtual_address + text_pos + offset_pos,
                    value,
                });
            }
        }
        text_pos = text_pos.wrapping_add(1);
    }
    // Note: Even if the globals_with_values list is sorted again at analysis.rs, sorting
    // here ends up reducing the time spent to sort the full global list a lot.
    out.sort_unstable_by_key(|x| x.value);
    out
}
