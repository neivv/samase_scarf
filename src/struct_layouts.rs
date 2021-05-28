use scarf::exec_state::VirtualAddress;

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
