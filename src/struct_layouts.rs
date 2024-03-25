use scarf::exec_state::VirtualAddress;
use scarf::{BinaryFile, Operand, MemAccessSize};

use crate::util::{OperandExt};

/// Stateless struct that has methods for getting various struct offsets
/// that differ between 32- and 64-bit.
/// The methods used to be just generic functions, but specifying the VirtualAddress generic
/// for them every time when they were called got annoying.
/// Ideally inlining makes them still constants.
#[derive(Copy, Clone)]
pub struct StructLayouts {
    pub is_64bit: bool,
}

impl StructLayouts {
    pub const fn sprite_first_overlay(self, sprite_size: u32) -> Option<u32> {
        match (sprite_size, self.is_64bit) {
            (0x24, false) => Some(0x1c),
            (0x28, false) => Some(0x20),
            (0x38, true) => Some(0x28),
            (0x48, true) => Some(0x38),
            _ => None,
        }
    }

    pub const fn mem_access_size(self) -> MemAccessSize {
        if self.is_64bit {
            MemAccessSize::Mem64
        } else {
            MemAccessSize::Mem32
        }
    }

    #[inline]
    const fn pair(self, val_32: u64, val_64: u64) -> u64 {
        if self.is_64bit {
            val_64
        } else {
            val_32
        }
    }

    pub const fn sprite_visibility_mask(self) -> u64 {
        self.pair(0xc, 0x14)
    }

    pub const fn sprite_flags(self) -> u64 {
        self.pair(0xe, 0x16)
    }

    pub const fn unit_sprite(self) -> u64 {
        self.pair(0xc, 0x18)
    }

    pub const fn flingy_next_move_waypoint(self) -> u64 {
        self.pair(0x18, 0x30)
    }

    pub const fn flingy_flags(self) -> u64 {
        self.pair(0x20, 0x38)
    }

    pub const fn flingy_facing_direction(self) -> u64 {
        self.pair(0x21, 0x39)
    }

    pub const fn flingy_movement_type(self) -> u64 {
        self.pair(0x27, 0x3f)
    }

    pub const fn flingy_pos(self) -> u64 {
        self.pair(0x28, 0x40)
    }

    pub const fn flingy_exact_pos(self) -> u64 {
        self.pair(0x2c, 0x44)
    }

    pub const fn flingy_speed(self) -> u64 {
        self.pair(0x38, 0x50)
    }

    pub const fn unit_player(self) -> u64 {
        self.pair(0x4c, 0x68)
    }

    pub const fn unit_order(self) -> u64 {
        self.pair(0x4d, 0x69)
    }

    pub const fn unit_order_state(self) -> u64 {
        self.pair(0x4e, 0x6a)
    }

    pub const fn unit_order_timer(self) -> u64 {
        self.pair(0x54, 0x70)
    }

    pub const fn unit_order_target_pos(self) -> u64 {
        self.pair(0x58, 0x78)
    }

    pub const fn unit_target(self) -> u64 {
        self.pair(0x5c, 0x80)
    }

    pub const fn unit_id(self) -> u64 {
        self.pair(0x64, 0x8c)
    }

    pub const fn unit_subunit_linked(self) -> u64 {
        self.pair(0x70, 0xa0)
    }

    pub const fn unit_related(self) -> u64 {
        self.pair(0x80, 0xc0)
    }

    pub const fn unit_invisibility_effects(self) -> u64 {
        self.pair(0x96, 0xda)
    }

    pub const fn unit_movement_state(self) -> u64 {
        self.pair(0x97, 0xdb)
    }

    pub const fn unit_build_queue(self) -> u64 {
        self.pair(0x98, 0xdc)
    }

    pub const fn unit_secondary_order(self) -> u64 {
        self.pair(0xa6, 0xea)
    }

    pub const fn unit_remaining_build_time(self) -> u64 {
        self.pair(0xac, 0xf0)
    }

    pub const fn unit_specific(self) -> u64 {
        self.pair(0xc0, 0x108)
    }

    pub const fn unit_current_tech(self) -> u64 {
        self.pair(0xc8, 0x114)
    }

    pub const fn unit_nuke_dot_sprite(self) -> u64 {
        self.pair(0xd0, 0x128)
    }

    pub const fn unit_current_upgrade(self) -> u64 {
        self.pair(0xc9, 0x115)
    }

    pub const fn unit_flags(self) -> u64 {
        self.pair(0xdc, 0x140)
    }

    pub const fn unit_poweurp_bits(self) -> u64 {
        self.pair(0xe0, 0x144)
    }

    pub const fn unit_secondary_order_state(self) -> u64 {
        self.pair(0xe2, 0x146)
    }

    pub const fn unit_currently_building(self) -> u64 {
        self.pair(0xec, 0x158)
    }

    pub const fn unit_next_pylon(self) -> u64 {
        self.pair(0xfc, 0x178)
    }

    pub const fn unit_path(self) -> u64 {
        self.pair(0x100, 0x188)
    }

    pub const fn unit_lockdown_timer(self) -> u64 {
        self.pair(0x117, 0x1a3)
    }

    pub const fn unit_stasis_timer(self) -> u64 {
        self.pair(0x119, 0x1a5)
    }

    pub const fn unit_maelstrom_timer(self) -> u64 {
        self.pair(0x124, 0x1b4)
    }

    pub const fn unit_acid_spore_count(self) -> u64 {
        self.pair(0x126, 0x1b6)
    }

    pub const fn unit_ai(self) -> u64 {
        self.pair(0x134, 0x1c8)
    }

    pub const fn unit_ground_strength(self) -> u64 {
        self.pair(0x13a, 0x1d2)
    }

    pub const fn unit_search_indices(self) -> u64 {
        self.pair(0x13c, 0x1d4)
    }

    pub const fn image_size(self) -> u64 {
        self.pair(0x40, 0x58)
    }

    pub fn if_mul_image_size<'e>(self, op: Operand<'e>) -> Option<Operand<'e>> {
        if !self.is_64bit {
            op.if_arithmetic_lsh_const(0x6)
        } else {
            op.if_arithmetic_mul_const(0x58)
        }
    }

    pub const fn image_id(self) -> u64 {
        self.pair(0x8, 0x10)
    }

    pub const fn image_iscript(self) -> u64 {
        self.pair(0x10, 0x18)
    }

    pub const fn image_grp(self) -> u64 {
        self.pair(0x2c, 0x38)
    }

    pub const fn image_parent(self) -> u64 {
        self.pair(0x3c, 0x50)
    }

    pub fn if_unit_sprite<'e>(self, op: Operand<'e>) -> Option<Operand<'e>> {
        let word_size = if !self.is_64bit { MemAccessSize::Mem32 } else { MemAccessSize::Mem64 };
        op.if_memory()
            .and_then(|x| {
                if x.size != word_size {
                    return None;
                }
                x.if_offset(self.unit_sprite())
            })
    }

    pub const fn ai_region_size(self) -> u64 {
        self.pair(0x34, 0x50)
    }

    pub const fn ai_script_pos(self) -> u64 {
        self.pair(0x8, 0x10)
    }

    pub const fn ai_script_wait(self) -> u64 {
        self.pair(0xc, 0x14)
    }

    pub const fn ai_script_player(self) -> u64 {
        self.pair(0x10, 0x18)
    }

    pub const fn ai_script_center(self) -> u64 {
        self.pair(0x24, 0x2c)
    }

    pub const fn ai_script_flags(self) -> u64 {
        self.pair(0x30, 0x40)
    }

    pub const fn player_ai_size(self) -> u64 {
        self.pair(0x4e8, 0x6e8)
    }

    pub const fn player_ai_flags(self) -> u64 {
        self.pair(0x218, 0x410)
    }

    pub const fn player_ai_build_limits(self) -> u64 {
        self.pair(0x3f0, 0x5e8)
    }

    pub const fn button_set_size(self) -> u32 {
        self.pair(0xc, 0x18) as u32
    }

    pub const fn button_size(self) -> u32 {
        self.pair(0x14, 0x20) as u32
    }

    pub const fn button_condition_func(self) -> u64 {
        self.pair(0x4, 0x8)
    }

    pub const fn button_action_func(self) -> u32 {
        self.pair(0x8, 0x10) as u32
    }

    pub const fn button_condition_param(self) -> u64 {
        self.pair(0xc, 0x18)
    }

    pub const fn button_linked(self) -> u32 {
        self.pair(0x8, 0x10) as u32
    }

    pub const fn bullet_weapon_id(self) -> u64 {
        self.pair(0x60, 0x88)
    }

    pub const fn bullet_flags(self) -> u64 {
        self.pair(0x62, 0x8a)
    }

    pub const fn bullet_parent(self) -> u64 {
        self.pair(0x64, 0x90)
    }

    pub const fn status_screen_stat_dat(self) -> u64 {
        self.pair(0x8, 0xc)
    }

    pub const fn control_ptr_value(self) -> u64 {
        self.pair(0x40, 0x58)
    }

    pub const fn order_id(self) -> u64 {
        self.pair(0x8, 0x10)
    }

    pub const fn event_type(self) -> u64 {
        self.pair(0x10, 0x18)
    }

    pub const fn event_mouse_xy(self) -> u64 {
        self.pair(0x12, 0x1a)
    }

    pub const fn glyph_set_size(self) -> u64 {
        self.pair(0xa0, 0xc8)
    }

    pub const fn graphic_layer_draw_func(self) -> u64 {
        self.pair(0x10, 0x18)
    }

    pub const fn graphic_layer_size(self) -> u64 {
        self.pair(0x14, 0x20)
    }

    pub const fn control_draw_funcs(self) -> &'static [u64] {
        match self.is_64bit {
            false => &[0x30, 0x48],
            true => &[0x44, 0x68],
        }
    }

    pub const fn control_u16_value(self) -> &'static [u64] {
        match self.is_64bit {
            false => &[0x26, 0x3e],
            true => &[0x32, 0x56],
        }
    }

    pub const fn dialog_once_in_frame(self) -> &'static [u64] {
        match self.is_64bit {
            false => &[0x4c, 0x64],
            true => &[0x78, 0xa0],
        }
    }

    pub const fn pathing_map_tile_regions(self) -> u64 {
        self.pair(0xc, 0x18)
    }

    pub const fn dcreep_list_index(self) -> u64 {
        self.pair(0x12, 0x22)
    }

    pub const fn dcreep_x(self) -> u64 {
        self.pair(0x10, 0x20)
    }

    pub const fn building_ai_town(self) -> u64 {
        self.pair(0x14, 0x20)
    }

    pub const fn texture_struct_size(self) -> u64 {
        self.pair(0x10, 0x18)
    }
}

pub fn button_set_index_to_action<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    button_sets: Va,
    set: u32,
    button: u32,
) -> Option<Va> {
    let layouts = StructLayouts {
        is_64bit: Va::SIZE == 8,
    };
    let set = binary.read_address(
        button_sets + layouts.button_set_size().wrapping_mul(set).wrapping_add(Va::SIZE)
    ).ok()?;
    binary.read_address(
        set + layouts.button_size().wrapping_mul(button).wrapping_add(layouts.button_action_func())
    ).ok()
}
