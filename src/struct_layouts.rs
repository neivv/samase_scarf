use scarf::exec_state::VirtualAddress;
use scarf::{Operand, MemAccessSize};

use crate::{OperandExt};

pub fn sprite_first_overlay<Va: VirtualAddress>(sprite_size: u32) -> Option<u32> {
    match (sprite_size, Va::SIZE) {
        (0x24, 4) => Some(0x1c),
        (0x28, 4) => Some(0x20),
        _ => None,
    }
}

pub fn unit_sprite<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x18,
    }
}

pub fn unit_subunit_linked<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x70,
        false => 0xa0,
    }
}

pub fn unit_player<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x4c,
        false => 0x68,
    }
}

pub fn unit_order<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x4d,
        false => 0x69,
    }
}

pub fn unit_secondary_order<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xa6,
        false => 0xea,
    }
}

pub fn image_iscript<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x18,
    }
}

pub fn if_unit_sprite<'e, Va: VirtualAddress>(op: Operand<'e>) -> Option<Operand<'e>> {
    let word_size = if Va::SIZE == 4 { MemAccessSize::Mem32 } else { MemAccessSize::Mem64 };
    op.if_memory()
        .and_then(|x| {
            if x.size != word_size {
                return None;
            }
            x.address.if_arithmetic_add_const(unit_sprite::<Va>())
        })
}

pub fn ai_script_pos<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn ai_script_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x30,
        false => 0x40,
    }
}
