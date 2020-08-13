use fxhash::FxHashSet;

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
    let game = analysis.game()?;
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
        patched_addresses: FxHashSet::with_capacity_and_hasher(128, Default::default()),
    };
    game_ctx.do_analysis();
    Some(())
}

pub struct GameContext<'a, 'e, E: ExecutionState<'e>> {
    analysis: &'a mut Analysis<'e, E>,
    result: &'a mut DatPatches<'e, E::VirtualAddress>,
    unchecked_refs: FxHashSet<E::VirtualAddress>,
    checked_functions: FxHashSet<E::VirtualAddress>,
    game: Operand<'e>,
    game_address: E::VirtualAddress,
    patched_addresses: FxHashSet<E::VirtualAddress>,
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
}

pub struct GameAnalyzer<'a, 'b, 'e, E: ExecutionState<'e>> {
    game_ctx: &'a mut GameContext<'b, 'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    // Optimization to avoid some work before first game address ref
    game_ref_seen: bool,
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for GameAnalyzer<'a, 'b, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(ref dest, unres_val, None) => {
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
                            return;
                        }
                    }
                }
                if self.game_ref_seen {
                    if let Some(mem) = unres_val.if_memory() {
                        self.check_game_mem_access(ctrl, mem.address);
                    } else if let DestOperand::Memory(ref mem) = *dest {
                        self.check_game_mem_access(ctrl, mem.address);
                    } else if let OperandType::Arithmetic(ref arith) = *unres_val.ty() {
                        if let Some(mem) = arith.left.if_memory() {
                            self.check_game_mem_access(ctrl, mem.address);
                        } else if let Some(mem) = arith.right.if_memory() {
                            self.check_game_mem_access(ctrl, mem.address);
                        }
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

    fn check_game_mem_access(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        address_unres: Operand<'e>,
    ) {
        let addr = ctrl.resolve(address_unres);
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
            .and_then(|(l, r)| Some((l, r.if_constant()?)))
        {
            Some(s) => s,
            None => return,
        };
        match offset {
            // Tech availability sc
            0xdd34 => self.patch_tech_array_sc(ctrl, 3, index),
            // Tech level sc
            0xde54 => self.patch_tech_array_sc(ctrl, 2, index),
            // Upgrade limit sc
            0xdf98 => self.patch_upgrade_array_sc(ctrl, 1, index),
            // Upgrade level sc
            0xe1c0 => self.patch_upgrade_array_sc(ctrl, 0, index),
            // Tech availability bw
            0xff48 => self.patch_tech_array_bw(ctrl, 3, index),
            // Tech level bw
            0x10038 => self.patch_tech_array_bw(ctrl, 2, index),
            // Upgrade limit bw
            0x1015a => self.patch_upgrade_array_bw(ctrl, 1, index),
            // Upgrade level bw
            0x1020e => self.patch_upgrade_array_bw(ctrl, 0, index),
            _ => (),
        }
    }

    fn add_patch(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        index: Operand<'e>,
    ) {
        let address = ctrl.address();
        if !self.game_ctx.patched_addresses.insert(address) {
            return;
        }
        let instruction_len = (ctrl.current_instruction_end().as_u64() - address.as_u64()) as u8;
        let mut hook_len = instruction_len;
        let mut hook_pos = address + instruction_len as u32;
        while hook_len < 5 {
            match self.instruction_length(hook_pos) {
                Some(l) => {
                    hook_len += l;
                    hook_pos = hook_pos + l as u32;
                }
                None => return,
            }
        }
        self.game_ctx.result.patches.push(DatPatch::ExtendedArray(ExtArrayPatch {
            address,
            instruction_len,
            hook_len,
            ext_array_id,
            index,
        }));
    }

    fn instruction_length(&mut self, address: E::VirtualAddress) -> Option<u8> {
        use lde::Isa;

        let bytes = self.binary.slice_from_address(address, 0x10).ok()?;
        Some(lde::X86::ld(bytes) as u8)
    }

    fn patch_upgrade_array_sc(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, upgrade) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(0x2e))
        {
            Some(s) => s,
            None => {
                self.add_warning(format!("Couldn't split upgrade index {}", index));
                return;
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
        let index = ctx.add(ctx.mul_const(upgrade, 0xc), player);
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_upgrade_array_bw(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
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
                self.add_warning(format!("Couldn't split upgrade index {}", index));
                return;
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
        let index = ctx.add(ctx.mul_const(upgrade, 0xc), player);
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_tech_array_sc(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, tech) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(0x18))
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
        let index = ctx.add(ctx.mul_const(tech, 0xc), player);
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn patch_tech_array_bw(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        ext_array_id: u32,
        index: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let (player, tech) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(0x14))
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
        let index = ctx.add(ctx.mul_const(tech, 0xc), player);
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn unresolve(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: Operand<'e>,
    ) -> Option<Operand<'e>> {
        // Todo, could be a lot better but works for now
        let ctx = ctrl.ctx();
        if let Some(mem) = op.if_memory() {
            if let Some((l, r)) = mem.address.if_arithmetic_add() {
                if l.if_register().filter(|r| r.0 == 4).is_some() {
                    if r.if_constant().is_some() {
                        let esp = self.unresolve(ctrl, l)?;
                        return Some(ctx.mem_variable_rc(mem.size, ctx.add(esp, r)));
                    }
                }
            }
        }
        if op.if_register().filter(|r| r.0 == 4).is_some() {
            for i in 4..6 {
                let esp = ctrl.resolve(ctx.register(i));
                if let Some((l, r)) = esp.if_arithmetic_sub() {
                    if l.if_register().filter(|r| r.0 == 4).is_some() {
                        if r.if_constant().is_some() {
                            return Some(ctx.add(l, r));
                        }
                    }
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
