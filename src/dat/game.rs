use fxhash::{FxHashSet, FxHashMap};

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{OperandType};
use scarf::{BinaryFile, DestOperand, Operand, Operation};

use crate::{
    Analysis, EntryOf, entry_of_until, OperandExt, OptionExt,
};
use super::{DatPatches, DatPatch, ExtArrayPatch};

pub fn dat_game_analysis<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    result: &mut DatPatches<'e, E::VirtualAddress>,
) -> Option<()> {
    let ctx = analysis.ctx;
    let relocs = analysis.relocs_with_values();
    let text = analysis.binary.section(b".text\0\0\0").unwrap();
    let text_end = text.virtual_address + text.virtual_size;
    let game = analysis.game()?;
    let unit_strength = analysis.unit_strength()?;
    let player_ai = analysis.player_ai()?;
    let game_address = game.iter_no_mem_addr()
        .filter_map(|x| {
            x.if_memory()
                .filter(|x| x.size == E::WORD_SIZE)
                .and_then(|x| x.address.if_constant())
                .map(|x| E::VirtualAddress::from_u64(x))
        })
        .next()?;
    let game_refs = crate::find_functions_using_global(analysis, game_address);
    let mut unchecked_refs =
        FxHashSet::with_capacity_and_hasher(game_refs.len(), Default::default());
    for global in game_refs {
        unchecked_refs.insert(global.use_address);
    }
    let checked_functions =
        FxHashSet::with_capacity_and_hasher(unchecked_refs.len(), Default::default());
    let mut game_ctx = GameContext {
        analysis,
        result,
        unchecked_refs,
        checked_functions,
        game,
        game_address,
        patched_addresses: FxHashMap::with_capacity_and_hasher(128, Default::default()),
        unit_strength,
        ai_build_limit: ctx.add_const(player_ai, 0x3f0),
    };
    game_ctx.do_analysis();
    debug_assert!(game_ctx.unchecked_refs.is_empty());
    let other_globals = [
        unit_strength.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x);
            (start, start + 0xe4 * 4 * 2)
        }),
        player_ai.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x) + 0x3f0;
            (start, start + 0xe4)
        }),
    ];
    for (start, end) in other_globals.iter().flat_map(|&x| x) {
        let start = relocs.binary_search_by(|x| match x.value >= start {
            true => std::cmp::Ordering::Greater,
            false => std::cmp::Ordering::Less,
        }).unwrap_err();
        for i in start.. {
            let reloc = match relocs.get(i) {
                Some(s) if s.value < end => s,
                _ => break,
            };
            let address = reloc.address;
            if address >= text.virtual_address && address < text_end {
                game_ctx.unchecked_refs.insert(address);
            }
        }
    }
    game_ctx.other_global_analysis();
    Some(())
}

pub struct GameContext<'a, 'e, E: ExecutionState<'e>> {
    analysis: &'a mut Analysis<'e, E>,
    result: &'a mut DatPatches<'e, E::VirtualAddress>,
    unchecked_refs: FxHashSet<E::VirtualAddress>,
    checked_functions: FxHashSet<E::VirtualAddress>,
    game: Operand<'e>,
    game_address: E::VirtualAddress,
    patched_addresses: FxHashMap<E::VirtualAddress, (usize, Operand<'e>)>,
    unit_strength: Operand<'e>,
    ai_build_limit: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> GameContext<'a, 'e, E> {
    fn do_analysis(&mut self) {
        let binary = self.analysis.binary;
        let ctx = self.analysis.ctx;
        let functions = self.analysis.functions();
        while let Some(game_ref_addr) = self.unchecked_refs.iter().cloned().next() {
            let result = entry_of_until(binary, &functions, game_ref_addr, |entry| {
                if self.checked_functions.insert(entry) {
                    let mut analyzer = GameAnalyzer {
                        game_ctx: self,
                        binary,
                        game_ref_seen: false,
                        other_globals: false,
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    if self.unchecked_refs.contains(&game_ref_addr) {
                        EntryOf::Retry
                    } else {
                        EntryOf::Ok(())
                    }
                } else {
                    EntryOf::Retry
                }
            }).into_option();
            if result.is_none() {
                self.unchecked_refs.remove(&game_ref_addr);
            }
        }
    }

    fn other_global_analysis(&mut self) {
        let binary = self.analysis.binary;
        let ctx = self.analysis.ctx;
        let functions = self.analysis.functions();
        while let Some(ref_addr) = self.unchecked_refs.iter().cloned().next() {
            let result = entry_of_until(binary, &functions, ref_addr, |entry| {
                if self.checked_functions.insert(entry) {
                    let mut analyzer = GameAnalyzer {
                        game_ctx: self,
                        binary,
                        game_ref_seen: true,
                        other_globals: true,
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    if self.unchecked_refs.contains(&ref_addr) {
                        EntryOf::Retry
                    } else {
                        EntryOf::Ok(())
                    }
                } else {
                    EntryOf::Retry
                }
            }).into_option();
            if result.is_none() {
                self.unchecked_refs.remove(&ref_addr);
            }
        }
    }
}

pub struct GameAnalyzer<'a, 'b, 'e, E: ExecutionState<'e>> {
    game_ctx: &'a mut GameContext<'b, 'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    // Optimization to avoid some work before first game address ref
    game_ref_seen: bool,
    other_globals: bool,
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for GameAnalyzer<'a, 'b, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(ref dest, unres_val, None) => {
                if !self.game_ref_seen {
                    // Any instruction referring to a global must be at least 5 bytes
                    let instruction_len = ctrl.current_instruction_end().as_u64()
                        .wrapping_sub(ctrl.address().as_u64());
                    if instruction_len >= 5 {
                        let const_addr = if_const_or_mem_const::<E>(unres_val)
                            .or_else(|| {
                                if let OperandType::Arithmetic(ref arith) = *unres_val.ty() {
                                    if_const_or_mem_const::<E>(arith.left)
                                        .or_else(|| if_const_or_mem_const::<E>(arith.right))
                                } else {
                                    None
                                }
                            });
                        if let Some(const_addr) = const_addr {
                            if const_addr == self.game_ctx.game_address {
                                self.reached_game_ref(ctrl);
                                self.game_ref_seen = true;
                            }
                        }
                    }
                    return;
                }
                if let Some(mem) = unres_val.if_memory() {
                    self.check_mem_access(ctrl, mem.address);
                } else if let DestOperand::Memory(ref mem) = *dest {
                    self.check_mem_access(ctrl, mem.address);
                } else if let OperandType::Arithmetic(ref arith) = *unres_val.ty() {
                    if let Some(mem) = arith.left.if_memory() {
                        self.check_mem_access(ctrl, mem.address);
                    } else if let Some(mem) = arith.right.if_memory() {
                        self.check_mem_access(ctrl, mem.address);
                    }
                }
            }
            Operation::SetFlags(arith, _size) => {
                if self.game_ref_seen {
                    if let Some(mem) = arith.left.if_memory() {
                        self.check_mem_access(ctrl, mem.address);
                    } if let Some(mem) = arith.right.if_memory() {
                        self.check_mem_access(ctrl, mem.address);
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> GameAnalyzer<'a, 'b, 'e, E> {
    fn add_warning(&mut self, msg: String) {
        warn!("{}", msg);
    }

    fn reached_game_ref(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let mut imm_addr = ctrl.current_instruction_end() - 4;
        while imm_addr > ctrl.address() {
            if let Ok(imm) = self.binary.read_u32(imm_addr) {
                if imm == self.game_ctx.game_address.as_u64() as u32 {
                    self.game_ctx.unchecked_refs.remove(&imm_addr);
                    return;
                }
            }
            imm_addr = imm_addr - 1;
        }
    }

    fn check_mem_access(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        address_unres: Operand<'e>,
    ) {
        let addr = ctrl.resolve(address_unres);
        if self.other_globals {
            let ctx = ctrl.ctx();
            let others = [
                (self.game_ctx.unit_strength, 0xe4 * 4 * 2),
                (self.game_ctx.ai_build_limit, 0xe4),
            ];
            let (base, index) = addr.if_arithmetic_add()
                .map(|x| (x.1, x.0))
                .unwrap_or_else(|| (addr, ctx.const_0()));
            if let Some(c) = base.if_constant() {
                for &(start, len) in &others {
                    if let Some(c2) = start.if_constant() {
                        let offset = c.wrapping_sub(c2);
                        if offset < len {
                            let index = ctx.add_const(index, offset);
                            if start == self.game_ctx.unit_strength {
                                self.patch_unit_strength(ctrl, index);
                            } else if start == self.game_ctx.ai_build_limit {
                                self.patch_ai_unit_limit(ctrl, index);
                            }
                        }
                    }
                }
            }
        } else {
            self.check_game_mem_access(ctrl, addr);
        }
    }

    fn check_game_mem_access(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        addr: Operand<'e>,
    ) {
        let mut terms = match crate::add_terms::collect_arith_add_terms(addr) {
            Some(s) => s,
            None => return,
        };
        if !terms.remove_one(|x, _neg| x == self.game_ctx.game) {
            return;
        }
        let ctx = ctrl.ctx();
        let val = terms.join(ctx);
        let (index, offset) = match val.if_arithmetic_add()
            .and_then(|(l, r)| Some((l, r.if_constant()? as u32)))
            .or_else(|| {
                let c = val.if_constant()? as u32;
                Some((ctx.const_0(), c))
            })
        {
            Some(s) => s,
            None => return,
        };
        match offset {
            // Unit availability
            0x18c ..= 0xc3b => self.patch_unit_array(ctrl, 0x6, true, 1, offset - 0x18c, index),
            // Unit count
            0x3234 ..= 0x5cf3 => {
                self.patch_unit_array(ctrl, 0x7, false, 4, offset - 0x3234, index)
            }
            // Completed unit count
            0x5cf4 ..= 0x87b3 => {
                self.patch_unit_array(ctrl, 0x8, false, 4, offset - 0x5cf4, index)
            }
            // Unit kills
            0x87b4 ..= 0xb273 => {
                self.patch_unit_array(ctrl, 0x9, false, 4, offset - 0x87b4, index)
            }
            // Unit deaths
            0xb274 ..= 0xdd33 => {
                self.patch_unit_array(ctrl, 0xa, false, 4, offset - 0xb274, index)
            }
            // Tech availability sc
            0xdd34 ..= 0xde53 => self.patch_tech_array(ctrl, 3, 0x18, 0, offset - 0xdd34, index),
            // Tech level sc
            0xde54 ..= 0xdf73 => self.patch_tech_array(ctrl, 2, 0x18, 0, offset - 0xde54, index),
            // Upgrade limit sc
            0xdf98 ..= 0xe1bf => self.patch_upgrade_array_sc(ctrl, 1, offset - 0xdf98, index),
            // Upgrade level sc
            0xe1c0 ..= 0xe3e7 => self.patch_upgrade_array_sc(ctrl, 0, offset - 0xe1c0, index),
            // Tech availability bw
            0xff48 => self.patch_tech_array(ctrl, 3, 0x14, 0, 0, index),
            // Tech level bw
            0x10038 => self.patch_tech_array(ctrl, 2, 0x14, 0, 0, index),
            // Upgrade limit bw
            0x1015a => self.patch_upgrade_array_bw(ctrl, 1, 0, 0, index),
            // Upgrade level bw
            0x1020e => self.patch_upgrade_array_bw(ctrl, 0, 0, 0, index),
            // Tech availability bw (Real)
            0xff60 ..= 0x1004f => {
                self.patch_tech_array(ctrl, 3, 0x14, 0x18, offset - 0xff60, index)
            }
            // Tech level bw (Real)
            0x10050 ..= 0x1013f => {
                self.patch_tech_array(ctrl, 3, 0x14, 0x18, offset - 0x10050, index)
            }
            // Tech being researched bits
            0x10140 ..= 0x10187 => self.patch_bit_array(ctrl, 5, 6, offset - 0x10140, index),
            // Upgrade limit bw (Real)
            0x10188 ..= 0x1023b => {
                self.patch_upgrade_array_bw(ctrl, 1, 0x2e, offset - 0x10188, index)
            }
            // Upgrade level bw (Real)
            0x1023c ..= 0x102ef => {
                self.patch_upgrade_array_bw(ctrl, 0, 0x2e, offset - 0x1023c, index)
            }
            // Upgrade being researched bits
            0x102f0 ..= 0x1034f => self.patch_bit_array(ctrl, 4, 8, offset - 0x102f0, index),
            _ => {
            }
        }
    }

    fn add_patch(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        index: Operand<'e>,
    ) {
        let address = ctrl.address();
        // Redo patch if it was already patched, as the second time should give more
        // accurate index (E.g. undefined instead of constant).
        let patches = &mut self.game_ctx.result.patches;
        let &mut (i, old_index) = self.game_ctx.patched_addresses.entry(address)
            .or_insert_with(|| {
                let i = patches.len();
                patches.push(DatPatch::ExtendedArray(ExtArrayPatch {
                    address,
                    instruction_len: 0,
                    ext_array_id: 0,
                    index,
                }));
                (i, index)
            });
        if index != old_index {
            if old_index.if_constant().is_none() || index.if_constant().is_some() {
                return;
            }
        }
        let instruction_len = (ctrl.current_instruction_end().as_u64() - address.as_u64()) as u8;
        self.game_ctx.result.patches[i] = DatPatch::ExtendedArray(ExtArrayPatch {
            address,
            instruction_len,
            ext_array_id,
            index,
        });
    }

    fn patch_upgrade_array_sc(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        byte_offset: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, upgrade) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(0x2e))
        {
            Some(s) => s,
            None => {
                let divisor = ctx.constant(0x2e);
                let player = ctx.div(index, divisor);
                let id = ctx.modulo(index, divisor);
                (player, id)
            }
        };
        let (player, upgrade) = match
            (self.unresolve(ctrl, player), self.unresolve(ctrl, upgrade))
        {
            (Some(a), Some(b)) => (a, b),
            _ => {
                self.add_warning(format!("Unable to find operands for player/upgrade"));
                return;
            }
        };
        let mut index = ctx.add(ctx.mul_const(upgrade, 0xc), player);
        if byte_offset != 0 {
            let player = byte_offset / 0x2e;
            let entry = byte_offset % 0x2e;
            index = ctx.add_const(
                index,
                entry.wrapping_mul(0xc).wrapping_add(player) as u64
            );
        }
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_upgrade_array_bw(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        start_index: u32,
        byte_offset: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, upgrade) = match index.if_arithmetic_sub()
            .and_either(|x| {
                x.if_arithmetic_add()
                    .and_either(|y| y.if_arithmetic_lsh_const(4))
            })
            .and_then(|((p1, u), p2)| {
                if p1 == p2 {
                    Some((p1, u))
                } else {
                    None
                }
            })
        {
            Some(s) => s,
            None => {
                let divisor = ctx.constant(0xf);
                let offset = ctx.sub_const(index, 0x2eu32.wrapping_sub(start_index) as u64);
                let player = ctx.div(offset, divisor);
                let id = ctx.add_const(
                    ctx.modulo(offset, divisor),
                    0x2eu32.wrapping_sub(start_index) as u64,
                );
                (player, id)
            }
        };
        let (player, upgrade) = match
            (self.unresolve(ctrl, player), self.unresolve(ctrl, upgrade))
        {
            (Some(a), Some(b)) => (a, b),
            _ => {
                self.add_warning(format!("Unable to find operands for player/upgrade"));
                return;
            }
        };
        let upgrade = ctx.add_const(upgrade, start_index as u64);
        let mut index = ctx.add(ctx.mul_const(upgrade, 0xc), player);
        if byte_offset != 0 {
            let player = byte_offset / 0xf;
            let entry = byte_offset % 0xf;
            index = ctx.add_const(
                index,
                entry.wrapping_mul(0xc).wrapping_add(player) as u64
            );
        }
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_tech_array(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        array_size: u32,
        start_index: u32,
        byte_offset: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, tech) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(array_size as u64))
        {
            Some(s) => s,
            None => {
                self.add_warning(format!("Couldn't split tech index {}", index));
                return;
            }
        };
        let (player, tech) = match
            (self.unresolve(ctrl, player), self.unresolve(ctrl, tech))
        {
            (Some(a), Some(b)) => (a, b),
            _ => {
                self.add_warning(format!("Unable to find operands for player/tech"));
                return;
            }
        };
        let tech = ctx.add_const(tech, start_index as u64);
        let mut index = ctx.add(ctx.mul_const(tech, 0xc), player);
        if byte_offset != 0 {
            let player = byte_offset / array_size;
            let entry = byte_offset % array_size;
            index = ctx.add_const(
                index,
                entry.wrapping_mul(0xc).wrapping_add(player) as u64
            );
        }
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_bit_array(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        expected_bytes_per_player: u32,
        byte_offset: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        // Bit array index is originally
        // [player_0_bits_0_7, player_0_bits_8_15, ...]
        // index = (player * expected_bytes_per_player) + (id >> 3)
        // It'll be patched to
        // [player_0_bits_0_7, player_1_bits_0_7, ...]
        // index = (id >> 3) * 0xc + player
        let player_id = index.if_arithmetic_add()
            .and_either(|x| Some(x).filter(|x| x.if_arithmetic_rsh_const(3).is_some()))
            .and_then(|(id, other)| {
                let player = other.if_arithmetic_mul_const(expected_bytes_per_player as u64)
                    .or_else(|| {
                        let shift = expected_bytes_per_player.trailing_zeros();
                        other.if_arithmetic_lsh_const(shift as u64)
                    })?;
                Some((player, id))
            });
        let (player, id) = match player_id {
            Some(s) => s,
            None => {
                let divisor = ctx.constant(expected_bytes_per_player as u64);
                let player = ctx.div(index, divisor);
                let id = ctx.modulo(index, divisor);
                (player, id)
            }
        };
        let (player, id) = match (self.unresolve(ctrl, player), self.unresolve(ctrl, id)) {
            (Some(a), Some(b)) => (a, b),
            _ => {
                self.add_warning(format!("Unable to find operands for player/id"));
                return;
            }
        };
        let mut index = ctx.add(ctx.mul_const(id, 0xc), player);
        if byte_offset != 0 {
            let player = byte_offset / expected_bytes_per_player;
            let entry = byte_offset % expected_bytes_per_player;
            index = ctx.add_const(
                index,
                entry.wrapping_mul(0xc).wrapping_add(player) as u64
            );
        }
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_unit_array(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        first_index_is_player: bool,
        value_size: u32,
        byte_offset: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let player_id_from_index = |index| {
            if first_index_is_player {
                // player = index / (0xe4 * value_size)
                // id = (index % (0xe4 * value_size)) / value_size
                let divisor = ctx.constant(0xe4 * value_size as u64);
                let player = ctx.div(
                    index,
                    divisor,
                );
                let id = ctx.div(
                    ctx.modulo(
                        index,
                        divisor,
                    ),
                    ctx.constant(value_size as u64),
                );
                (player, id)
            } else {
                // player = (index % (0xc * value_size)) / value_size
                // id = index / (0xc * value_size)
                let divisor = ctx.constant(0xc * value_size as u64);
                let id = ctx.div(
                    index,
                    divisor,
                );
                let player = ctx.div(
                    ctx.modulo(
                        index,
                        divisor,
                    ),
                    ctx.constant(value_size as u64),
                );
                (player, id)
            }
        };
        let player_id = if first_index_is_player {
            // player * 0xe4 * value_size + id * value_size
            // to
            // id * value_size * 0xc + player * value_size
            index.if_arithmetic_add()
                .and_either(|x| {
                    Some(x).filter(|x| x.if_arithmetic_mul_const(0xe4 * value_size as u64).is_some())
                })
                .and_then(|(player, other)| {
                    if value_size == 1 {
                        Some((player, other))
                    } else {
                        let id = other.if_arithmetic_mul_const(value_size as u64)
                            .or_else(|| {
                                let shift = value_size.trailing_zeros();
                                other.if_arithmetic_lsh_const(shift as u64)
                            })?;
                        Some((player, id))
                    }
                })
        } else {
            // (id * 0xc + player) * value_size
            Some(index)
                .and_then(|x| {
                    if value_size == 1 {
                        Some(x)
                    } else {
                        x.if_arithmetic_mul_const(value_size as u64)
                    }
                })
                .and_then(|x| x.if_arithmetic_add())
                .and_either(|x| x.if_arithmetic_mul_const(0xc))
                .and_then(|(id, other)| {
                    Some((other, id))
                })
        };
        let (player, id) = match player_id {
            Some(s) => s,
            None => player_id_from_index(index),
        };
        let (player, id) = match (self.unresolve(ctrl, player), self.unresolve(ctrl, id)) {
            (Some(a), Some(b)) => (a, b),
            _ => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    player_id_from_index(index_unres)
                } else {
                    self.add_warning(format!("Unable to find operands for player/id"));
                    return;
                }
            }
        };
        let mut index = ctx.mul_const(
            ctx.add(
                ctx.mul_const(id, 0xc),
                player,
            ),
            value_size as u64,
        );
        if byte_offset != 0 {
            let player;
            let entry;
            let entry_offset;
            if first_index_is_player {
                player = byte_offset / (value_size * 0xe4);
                let offset = byte_offset % (value_size * 0xe4);
                entry = offset / value_size;
                entry_offset = offset & (value_size - 1);
            } else {
                entry = byte_offset / (value_size * 0xc);
                let offset = byte_offset % (value_size * 0xc);
                player = offset / value_size;
                entry_offset = offset & (value_size - 1);
            }
            index = ctx.add_const(
                index,
                entry.wrapping_mul(0xc)
                    .wrapping_mul(value_size)
                    .wrapping_add(player.wrapping_mul(value_size))
                    .wrapping_add(entry_offset) as u64,
            );
        }
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_unit_strength(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let id_ground_from_index = |index: Operand<'e>| {
            // index = unit_id * 4 + is_ground * e4 * 4
            // => unit_id = (index / 4) % e4
            //      is_ground = (index / 4) / e4
            index.if_arithmetic_mul_const(4)
                .and_then(|x| x.if_arithmetic_add())
                .and_either(|x| x.if_arithmetic_mul_const(0xe4))
                .map(|(ground, id)| (id, ground))
                .or_else(|| {
                    index.if_arithmetic_add_const(0xe4 * 4)
                        .and_then(|x| x.if_arithmetic_mul_const(4))
                        .map(|x| (x, ctx.const_1()))
                })
                .or_else(|| {
                    index.if_arithmetic_mul_const(0xe4 * 4)
                        .map(|x| (ctx.const_0(), x))
                })
                .or_else(|| {
                    index.if_arithmetic_mul_const(0x4)
                        .map(|x| (x, ctx.const_0()))
                })
                .unwrap_or_else(|| {
                    let dword_index = ctx.div(index, ctx.constant(4));
                    let unit_id = ctx.modulo(dword_index, ctx.constant(0xe4));
                    let is_ground = ctx.div(dword_index, ctx.constant(0xe4));
                    (unit_id, is_ground)
                })
        };
        let (unit_id, is_ground) = id_ground_from_index(index);
        let (unit_id, is_ground) =
            match (self.unresolve(ctrl, unit_id), self.unresolve(ctrl, is_ground))
        {
            (Some(a), Some(b)) => (a, b),
            (Some(unit_id), None) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let is_ground = ctx.div(
                        ctx.sub(
                            index_unres,
                            ctx.mul_const(unit_id, 4),
                        ),
                        ctx.constant(0xe4 * 4),
                    );
                    (unit_id, is_ground)
                } else {
                    self.add_warning(format!("Unable to find operands for is_ground/id"));
                    return;
                }
            }
            (None, Some(is_ground)) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let unit_id = ctx.div(
                        ctx.sub(
                            index_unres,
                            ctx.mul_const(is_ground, 0xe4 * 4),
                        ),
                        ctx.constant(4),
                    );
                    (unit_id, is_ground)
                } else {
                    self.add_warning(format!("Unable to find operands for is_ground/id"));
                    return;
                }
            }
            _ => {
                self.add_warning(format!("Unable to find operands for is_ground/id"));
                return;
            }
        };
        // Convert to (unit_id * 2 + is_ground) * 4
        let index = ctx.add(
            ctx.mul_const(unit_id, 8),
            ctx.mul_const(is_ground, 4),
        );
        self.add_patch(ctrl, 0xb, index);
    }

    fn patch_ai_unit_limit(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        // index = player * 4e8 + unit_id
        //      (The base is already player_ai + 0x3f0)
        // => unit_id = index % 4e8
        //      player = index / 4e8
        let (unit_id, player) = Some(index)
            .and_then(|x| x.if_arithmetic_add())
            .and_either(|x| x.if_arithmetic_mul_const(0x4e8))
            .map(|(player, id)| (id, player))
            .or_else(|| {
                index.if_arithmetic_mul_const(0xe4 * 4)
                    .map(|x| (ctx.const_0(), x))
            })
            .unwrap_or_else(|| {
                let unit_id = ctx.modulo(index, ctx.constant(0x4e8));
                let player = ctx.div(index, ctx.constant(0x4e8));
                (unit_id, player)
            });
        let (unit_id, player) =
            match (self.unresolve(ctrl, unit_id), self.unresolve(ctrl, player))
        {
            (Some(a), Some(b)) => (a, b),
            _ => {
                self.add_warning(format!("Unable to find operands for player/id"));
                return;
            }
        };
        // Convert to (unit_id + player * 0xc)
        let index = ctx.add(
            unit_id,
            ctx.mul_const(player, 0xc),
        );
        self.add_patch(ctrl, 0xc, index);
    }

    fn unresolve(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: Operand<'e>,
    ) -> Option<Operand<'e>> {
        if op.if_constant().is_some() {
            return Some(op);
        }
        let ctx = ctrl.ctx();
        for i in 0..8 {
            let reg = ctx.register(i);
            let val = ctrl.resolve(reg);
            if val == op {
                return Some(reg);
            }
            if let Some((l, r)) = val.if_arithmetic_add() {
                if l == op {
                    if let Some(c) = r.if_constant() {
                        return Some(ctx.sub_const(reg, c));
                    }
                }
            }
        }
        if let Some(mem) = op.if_memory() {
            if let Some(addr) = self.unresolve(ctrl, mem.address) {
                return Some(ctx.mem_variable_rc(mem.size, addr));
            }
        }
        if op.if_register().filter(|r| r.0 == 4).is_some() {
            for i in 4..6 {
                let unres = ctx.register(i);
                let esp = ctrl.resolve(unres);
                if let Some((l, r)) = esp.if_arithmetic_sub() {
                    if l.if_register().filter(|r| r.0 == 4).is_some() {
                        return Some(ctx.add(unres, r));
                    }
                }
            }
        }
        if let OperandType::Arithmetic(ref arith) = *op.ty() {
            if let Some(left) = self.unresolve(ctrl, arith.left) {
                if let Some(right) = self.unresolve(ctrl, arith.right) {
                    return Some(ctx.arithmetic(arith.ty, left, right));
                }
            }
        }
        None
    }
}

fn if_const_or_mem_const<'e, E: ExecutionState<'e>>(
    val: Operand<'e>,
) -> Option<E::VirtualAddress> {
    val.if_constant()
        .or_else(|| {
            val.if_memory()
                .filter(|x| x.size == E::WORD_SIZE)
                .and_then(|x| x.address.if_constant())
        })
        .map(|x| E::VirtualAddress::from_u64(x))
}