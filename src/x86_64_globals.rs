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
    /* f0 */ 0, 0, 0, 0,  0, 0, 0, 1,  1, 0, 0, 0,  0, 0, 1, 1,
];

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
    /* f0 */ 0, 0, 0, 0,  0, 0, 0, 1,  4, 0, 0, 0,  0, 0, 0, 0,
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
        let modrm = win[2];
        let b = modrm & 0x47;
        let ok = (CHECKED_OPCODES[win[1] as usize]) &
            (b.wrapping_sub(4) < 2) as u8 &
            ((b == 5) | (win[3] & 7 == 5) | (modrm & 0x80 != 0)) as u8;
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
                // SIB offset, assuming that one of registers contains binary base
                let offset = LittleEndian::read_u32(&win[4..]);
                offset_pos = 4;
                binary.base() + offset
            };
            if value >= global_min && value < global_max {
                out.push(RelocValues {
                    address: text.virtual_address + text_pos + offset_pos,
                    value,
                });
            }
        }
        text_pos = text_pos.wrapping_add(1);
    }
    out.sort_unstable_by_key(|x| x.value);
    out
}
