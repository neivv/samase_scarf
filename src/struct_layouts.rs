use scarf::exec_state::VirtualAddress;
use scarf::{Operand, MemAccessSize};

use crate::{OperandExt};

pub fn sprite_first_overlay<Va: VirtualAddress>(sprite_size: u32) -> Option<u32> {
    match (sprite_size, Va::SIZE) {
        (0x24, 4) => Some(0x1c),
        (0x28, 4) => Some(0x20),
        (0x48, 8) => Some(0x38),
        _ => None,
    }
}

pub fn sprite_visibility_mask<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x14,
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

pub fn unit_related<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x80,
        false => 0xc0,
    }
}

pub fn unit_order_target_pos<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x58,
        false => 0x78,
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

pub fn unit_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x64,
        false => 0x8c,
    }
}

pub fn unit_invisibility_effects<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x96,
        false => 0xda,
    }
}

pub fn unit_secondary_order<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xa6,
        false => 0xea,
    }
}

pub fn unit_current_tech<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc8,
        false => 0x114,
    }
}

pub fn unit_nuke_dot_sprite<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xd0,
        false => 0x128,
    }
}

pub fn unit_current_upgrade<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc9,
        false => 0x115,
    }
}

pub fn unit_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xdc,
        false => 0x140,
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

pub fn ai_script_wait<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x14,
    }
}

pub fn ai_script_player<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x18,
    }
}

pub fn ai_script_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x30,
        false => 0x40,
    }
}

pub fn button_size<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x18,
    }
}

pub fn button_linked<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn bullet_weapon_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x60,
        false => 0x88,
    }
}

pub fn status_screen_stat_dat<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0xc,
    }
}

pub fn control_ptr_value<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x40,
        false => 0x58,
    }
}

pub fn order_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn event_mouse_xy<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x12,
        false => 0x1a,
    }
}

pub fn glyph_set_size<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xa0,
        false => 0xc8,
    }
}
