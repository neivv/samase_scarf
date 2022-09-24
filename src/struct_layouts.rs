use scarf::exec_state::VirtualAddress;
use scarf::{BinaryFile, Operand, MemAccessSize};

use crate::{OperandExt};

pub fn sprite_first_overlay<Va: VirtualAddress>(sprite_size: u32) -> Option<u32> {
    match (sprite_size, Va::SIZE) {
        (0x24, 4) => Some(0x1c),
        (0x28, 4) => Some(0x20),
        (0x38, 8) => Some(0x28),
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

pub fn sprite_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xe,
        false => 0x16,
    }
}

pub fn unit_sprite<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x18,
    }
}

pub fn flingy_next_move_waypoint<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x18,
        false => 0x30,
    }
}

pub fn flingy_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x20,
        false => 0x38,
    }
}

pub fn flingy_facing_direction<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x21,
        false => 0x39,
    }
}

pub fn flingy_movement_type<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x27,
        false => 0x3f,
    }
}

pub fn flingy_pos<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x28,
        false => 0x40,
    }
}

pub fn flingy_exact_pos<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x2c,
        false => 0x44,
    }
}

pub fn flingy_speed<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x38,
        false => 0x50,
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

pub fn unit_order_state<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x4e,
        false => 0x6a,
    }
}

pub fn unit_order_timer<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x54,
        false => 0x70,
    }
}

pub fn unit_order_target_pos<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x58,
        false => 0x78,
    }
}

pub fn unit_target<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x5c,
        false => 0x80,
    }
}

pub fn unit_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x64,
        false => 0x8c,
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

pub fn unit_invisibility_effects<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x96,
        false => 0xda,
    }
}

pub fn unit_movement_state<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x97,
        false => 0xdb,
    }
}

pub fn unit_build_queue<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x98,
        false => 0xdc,
    }
}

pub fn unit_secondary_order<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xa6,
        false => 0xea,
    }
}

pub fn unit_specific<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc0,
        false => 0x108,
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

pub fn unit_secondary_order_state<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xe2,
        false => 0x146,
    }
}

pub fn unit_currently_building<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xec,
        false => 0x158,
    }
}

pub fn unit_next_pylon<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xfc,
        false => 0x178,
    }
}

pub fn unit_lockdown_timer<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x117,
        false => 0x1a3,
    }
}

pub fn unit_stasis_timer<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x119,
        false => 0x1a5,
    }
}

pub fn unit_maelstrom_timer<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x124,
        false => 0x1b4,
    }
}

pub fn unit_acid_spore_count<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x126,
        false => 0x1b6,
    }
}

pub fn unit_ai<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x134,
        false => 0x1c8,
    }
}

pub fn unit_ground_strength<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x13a,
        false => 0x1d2,
    }
}

pub fn if_mul_image_size<'e, Va: VirtualAddress>(op: Operand<'e>) -> Option<Operand<'e>> {
    if Va::SIZE == 4 {
        op.if_arithmetic(scarf::ArithOpType::Lsh)
            .filter(|(_, r)| r.if_constant() == Some(6))
            .map(|x| x.0)
    } else {
        op.if_arithmetic_mul_const(0x58)
    }
}

pub fn image_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn image_iscript<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x18,
    }
}

pub fn image_parent<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x3c,
        false => 0x50,
    }
}

pub fn if_unit_sprite<'e, Va: VirtualAddress>(op: Operand<'e>) -> Option<Operand<'e>> {
    let word_size = if Va::SIZE == 4 { MemAccessSize::Mem32 } else { MemAccessSize::Mem64 };
    op.if_memory()
        .and_then(|x| {
            if x.size != word_size {
                return None;
            }
            x.if_offset(unit_sprite::<Va>())
        })
}

pub fn ai_region_size<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x34,
        false => 0x50,
    }
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

pub fn ai_script_center<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x24,
        false => 0x2c,
    }
}

pub fn ai_script_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x30,
        false => 0x40,
    }
}

pub fn player_ai_size<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x4e8,
        false => 0x6e8,
    }
}

pub fn player_ai_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x218,
        false => 0x410,
    }
}

pub fn player_ai_build_limits<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x3f0,
        false => 0x5e8,
    }
}

pub fn button_set_size<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x18,
    }
}

pub fn button_size<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0x14,
        false => 0x20,
    }
}

pub fn button_action_func<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn button_linked<Va: VirtualAddress>() -> u32 {
    match Va::SIZE == 4 {
        true => 0x8,
        false => 0x10,
    }
}

pub fn button_set_index_to_action<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    button_sets: Va,
    set: u32,
    button: u32,
) -> Option<Va> {
    let set = binary.read_address(
        button_sets + button_set_size::<Va>().wrapping_mul(set).wrapping_add(Va::SIZE)
    ).ok()?;
    binary.read_address(
        set + button_size::<Va>().wrapping_mul(button).wrapping_add(button_action_func::<Va>())
    ).ok()
}

pub fn bullet_weapon_id<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x60,
        false => 0x88,
    }
}

pub fn bullet_flags<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x62,
        false => 0x8a,
    }
}

pub fn bullet_parent<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x64,
        false => 0x90,
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

pub fn event_type<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x18,
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

pub fn graphic_layer_draw_func<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x18,
    }
}

pub fn graphic_layer_size<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x14,
        false => 0x20,
    }
}

pub fn control_draw_funcs<Va: VirtualAddress>() -> &'static [u64] {
    match Va::SIZE == 4 {
        true => &[0x30, 0x48],
        false => &[0x44, 0x68],
    }
}

pub fn control_u16_value<Va: VirtualAddress>() -> &'static [u64] {
    match Va::SIZE == 4 {
        true => &[0x26, 0x3e],
        false => &[0x32, 0x56],
    }
}

pub fn pathing_map_tile_regions<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0xc,
        false => 0x18,
    }
}

pub fn dcreep_list_index<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x12,
        false => 0x22,
    }
}

pub fn dcreep_x<Va: VirtualAddress>() -> u64 {
    match Va::SIZE == 4 {
        true => 0x10,
        false => 0x20,
    }
}
