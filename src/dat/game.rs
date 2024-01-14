use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{OperandType};
use scarf::{BinaryFile, DestOperand, MemAccess, MemAccessSize, Operand, Operation, Rva};

use crate::analysis::{AnalysisCache, AnalysisCtx};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::detect_tail_call::DetectTailCall;
use crate::hash_map::{HashSet, HashMap};
use crate::util::{ExecStateExt, OperandExt, OptionExt, ControlExt};

use super::{
    DatPatches, DatPatch, ExtArrayPatch, RequiredStableAddressesMap, RequiredStableAddresses,
    FunctionHookContext,
};

pub(crate) fn dat_game_analysis<'acx, 'e, E: ExecutionState<'e>>(
    cache: &mut AnalysisCache<'e, E>,
    analysis: &'acx AnalysisCtx<'e, E>,
    required_stable_addresses: &mut RequiredStableAddressesMap<'acx, E::VirtualAddress>,
    result: &mut DatPatches<'e, E::VirtualAddress>,
) -> Option<()> {
    let ctx = analysis.ctx;
    let relocs = cache.globals_with_values();
    let text = analysis.binary_sections.text;
    let text_end = text.virtual_address + text.virtual_size;
    let game = cache.game(analysis)?;
    let unit_strength = cache.unit_strength(analysis)?;
    let player_ai = cache.player_ai(analysis)?;
    let trigger_all_units = cache.trigger_all_units_cache(analysis)?;
    let trigger_completed_units = cache.trigger_completed_units_cache(analysis)?;
    let game_address = game.iter_no_mem_addr()
        .filter_map(|x| {
            x.if_memory()
                .filter(|x| x.size == E::WORD_SIZE)
                .and_then(|x| x.if_constant_address())
                .map(|x| E::VirtualAddress::from_u64(x))
        })
        .next()?;
    let functions = cache.function_finder();
    let unchecked_refs = find_game_refs(analysis, &functions, game_address);
    let checked_functions =
        HashSet::with_capacity_and_hasher(unchecked_refs.len(), Default::default());
    let ai_build_limit_offset = E::struct_layouts().player_ai_build_limits();
    let mut game_ctx = GameContext {
        analysis,
        functions: &functions,
        result,
        unchecked_refs,
        checked_functions,
        game,
        game_address,
        patched_addresses: HashMap::with_capacity_and_hasher(128, Default::default()),
        unit_strength,
        ai_build_limit: ctx.add_const(player_ai, ai_build_limit_offset),
        trigger_all_units,
        trigger_completed_units,
    };
    game_ctx.do_analysis(required_stable_addresses);
    debug_assert!(game_ctx.unchecked_refs.is_empty());
    let other_globals = [
        unit_strength.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x);
            (start, start + 0xe4 * 4 * 2)
        }),
        player_ai.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x) + ai_build_limit_offset as u32;
            (start, start + 0xe4)
        }),
        trigger_all_units.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x);
            (start, start + 0xe4 * 12 * 4)
        }),
        trigger_completed_units.if_constant().map(|x| {
            let start = E::VirtualAddress::from_u64(x);
            (start, start + 0xe4 * 12 * 4)
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
    game_ctx.checked_functions.clear();
    game_ctx.other_global_analysis(required_stable_addresses);
    Some(())
}

fn find_game_refs<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    game_address: E::VirtualAddress,
) -> HashSet<E::VirtualAddress> {
    let game_refs = functions.find_functions_using_global(actx, game_address);
    let mut unchecked_refs =
        HashSet::with_capacity_and_hasher(game_refs.len(), Default::default());
    let text = actx.binary_sections.text;
    for global in game_refs {
        if E::VirtualAddress::SIZE == 4 {
            // For some reason there are dead code branches with
            // movzx x, word/byte [game_address], assume that those can be removed
            // to avoid having to go through fake functions when trying to find them
            // with entry_of_until.
            let ok = Some(()).and_then(|()| {
                let end = global.use_address.as_u64()
                    .checked_sub(text.virtual_address.as_u64())? as usize;
                let start = end.checked_sub(3)?;
                let bytes = text.data.get(start..end)?;
                if bytes[0] == 0x0f && matches!(bytes[1], 0xb6 | 0xb7) && bytes[2] & 7 == 5 {
                    None
                } else {
                    Some(())
                }
            }).is_some();
            if !ok {
                continue;
            }
        }
        unchecked_refs.insert(global.use_address);
    }
    unchecked_refs
}

pub struct GameContext<'a, 'acx, 'e, E: ExecutionState<'e>> {
    analysis: &'acx AnalysisCtx<'e, E>,
    functions: &'a FunctionFinder<'a, 'e, E>,
    result: &'a mut DatPatches<'e, E::VirtualAddress>,
    unchecked_refs: HashSet<E::VirtualAddress>,
    checked_functions: HashSet<E::VirtualAddress>,
    game: Operand<'e>,
    game_address: E::VirtualAddress,
    patched_addresses: HashMap<E::VirtualAddress, (usize, Operand<'e>)>,
    unit_strength: Operand<'e>,
    ai_build_limit: Operand<'e>,
    trigger_all_units: Operand<'e>,
    trigger_completed_units: Operand<'e>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> GameContext<'a, 'acx, 'e, E> {
    fn do_analysis(
        &mut self,
        required_stable_addresses: &mut RequiredStableAddressesMap<'acx, E::VirtualAddress>,
    ) {
        let binary = self.analysis.binary;
        let ctx = self.analysis.ctx;
        let bump = &self.analysis.bump;
        let functions = self.functions.functions();
        let mut function_ends = HashMap::with_capacity_and_hasher(64, Default::default());
        while let Some(game_ref_addr) = self.unchecked_refs.iter().cloned().next() {
            let result = entry_of_until(binary, functions, game_ref_addr, |entry| {
                if self.checked_functions.insert(entry) {
                    let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                    let rsa = required_stable_addresses.get(entry_rva);
                    let mut analyzer = GameAnalyzer {
                        game_ctx: self,
                        binary,
                        game_ref_seen: false,
                        other_globals: false,
                        required_stable_addresses: rsa,
                        switch_table: E::VirtualAddress::from_u64(0),
                        patch_indices: BumpVec::new_in(bump),
                        func_start: entry,
                        greatest_address: entry,
                        detect_tail_call: DetectTailCall::new(entry),
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    analyzer.convert_to_two_step_hooks_where_needed();
                    // Using switch_table as a heuristic for function end.
                    // Some game_ref_addrs are in unreachable code, so assume
                    // that if the function end is after game_ref_addr it's fine
                    if analyzer.switch_table > entry {
                        function_ends.insert(entry, analyzer.switch_table);
                    }
                    if analyzer.switch_table < game_ref_addr &&
                        self.unchecked_refs.contains(&game_ref_addr)
                    {
                        EntryOf::Retry
                    } else {
                        EntryOf::Ok(())
                    }
                } else {
                    let is_inside_analyzed_func = function_ends.get(&entry)
                        .filter(|&&end| end > game_ref_addr)
                        .is_some();
                    if is_inside_analyzed_func {
                        EntryOf::Stop
                    } else {
                        EntryOf::Retry
                    }
                }
            }).into_option();
            if result.is_none() {
                self.unchecked_refs.remove(&game_ref_addr);
            }
        }
    }

    fn other_global_analysis(
        &mut self,
        required_stable_addresses: &mut RequiredStableAddressesMap<'acx, E::VirtualAddress>,
    ) {
        let binary = self.analysis.binary;
        let ctx = self.analysis.ctx;
        let bump = &self.analysis.bump;
        let functions = self.functions.functions();
        while let Some(ref_addr) = self.unchecked_refs.iter().cloned().next() {
            let result = entry_of_until(binary, functions, ref_addr, |entry| {
                if self.checked_functions.insert(entry) {
                    let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                    let rsa = required_stable_addresses.get(entry_rva);
                    let mut analyzer = GameAnalyzer {
                        game_ctx: self,
                        binary,
                        game_ref_seen: true,
                        other_globals: true,
                        required_stable_addresses: rsa,
                        switch_table: E::VirtualAddress::from_u64(0),
                        patch_indices: BumpVec::new_in(bump),
                        func_start: entry,
                        greatest_address: entry,
                        detect_tail_call: DetectTailCall::new(entry),
                    };
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                    analyzer.convert_to_two_step_hooks_where_needed();
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

pub struct GameAnalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    game_ctx: &'a mut GameContext<'b, 'acx, 'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    // Optimization to avoid some work before first game address ref
    game_ref_seen: bool,
    other_globals: bool,
    required_stable_addresses: &'a mut RequiredStableAddresses<'acx, E::VirtualAddress>,
    switch_table: E::VirtualAddress,
    patch_indices: BumpVec<'acx, usize>,
    func_start: E::VirtualAddress,
    greatest_address: E::VirtualAddress,
    detect_tail_call: DetectTailCall<'e, E>,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    GameAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.detect_tail_call.operation(ctrl, op) {
            if self.other_globals {
                self.check_array_call(ctrl, true);
            }
            ctrl.end_branch();
            return;
        }
        let address = ctrl.address();
        if address == self.switch_table {
            // Executed to switch table cases, stop
            ctrl.skip_operation();
            ctrl.end_branch();
            return;
        }
        self.greatest_address = self.greatest_address.max(address);
        match *op {
            Operation::Move(ref dest, unres_val, None) => {
                // Any instruction referring to a global must be at least 5 bytes
                let instruction_len = ctrl.current_instruction_end().as_u64()
                    .wrapping_sub(address.as_u64());
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
                if !self.game_ref_seen {
                    return;
                }
                if let Some(mem) = unres_val.if_memory() {
                    self.check_mem_access(ctrl, mem);
                } else if let DestOperand::Memory(ref mem) = *dest {
                    self.check_mem_access(ctrl, mem);
                } else if let OperandType::Arithmetic(ref arith) = *unres_val.ty() {
                    if let Some(mem) = arith.left.if_memory() {
                        self.check_mem_access(ctrl, mem);
                    } else if let Some(mem) = arith.right.if_memory() {
                        self.check_mem_access(ctrl, mem);
                    }
                }
            }
            Operation::Jump { to, condition } => {
                let ctx = ctrl.ctx();
                let to_op = to;
                if let Some(to) = ctrl.resolve_va(to) {
                    let is_tail_call = condition == ctx.const_1() &&
                        ctrl.resolve_register(4) == ctx.register(4) &&
                        (to < self.func_start || to > self.greatest_address + 0x4000);
                    if is_tail_call {
                        self.operation(ctrl, &Operation::Call(to_op));
                        ctrl.end_branch();
                        return;
                    } else {
                        self.greatest_address = self.greatest_address.max(to);
                    }
                    let binary = self.binary;
                    if let Err(e) = self.required_stable_addresses.add_jump_dest(binary, to) {
                        dat_warn!(
                            self, "Overlapping stable addresses {:?} for jump {:?} -> {:?}",
                            e, address, to,
                        );
                    }
                }
                // A bit hacky fix to register switch table locations to prevent certain
                // noreturn code from executing them.
                // Probably could be better to have analysis to recognize that noreturn
                // function instead of relying control flow from it reaching switch table.
                // NOTE: Copypaste from DatReferringFuncAnalysis
                if let Some(mem) = ctrl.if_mem_word(to) {
                    let mem = ctrl.resolve_mem(mem);
                    let (index, base) = mem.address();
                    let index = index.if_arithmetic_mul_const(E::VirtualAddress::SIZE as u64);
                    if let Some(index) = index {
                        let exec_state = ctrl.exec_state();
                        if exec_state.value_limits(index).0 == 0 {
                            self.switch_table = E::VirtualAddress::from_u64(base);
                        }
                    }
                }
            }
            Operation::Call(_) => {
                if self.other_globals {
                    self.check_array_call(ctrl, false);
                }
            }
            Operation::SetFlags(ref arith) => {
                if self.game_ref_seen {
                    if let Some(mem) = arith.left.if_memory() {
                        self.check_mem_access(ctrl, mem);
                    } if let Some(mem) = arith.right.if_memory() {
                        self.check_mem_access(ctrl, mem);
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> GameAnalyzer<'a, 'b, 'acx, 'e, E> {
    fn reached_game_ref(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let mut imm_addr = ctrl.current_instruction_end() - 4;
        while imm_addr > ctrl.address() {
            if let Ok(imm) = self.binary.read_u32(imm_addr) {
                let imm = if E::VirtualAddress::SIZE == 4 {
                    u64::from(imm)
                } else {
                    ctrl.current_instruction_end().as_u64().wrapping_add(imm as i32 as i64 as u64)
                };
                if imm == self.game_ctx.game_address.as_u64() {
                    self.game_ctx.unchecked_refs.remove(&imm_addr);
                    return;
                }
            }
            imm_addr = imm_addr - 1;
        }
    }

    /// For other_arrays analysis, check memcpy/memset with argument being
    /// one of the trigger unit cache arrays
    fn check_array_call(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, is_tail_call: bool) {
        let arg_cache = &self.game_ctx.analysis.arg_cache;
        let arg1_loc = if !is_tail_call {
            arg_cache.on_call(0)
        } else {
            arg_cache.on_entry(0)
        };
        let arg1 = ctrl.resolve(arg1_loc);
        let ext_array_id = if arg1 == self.game_ctx.trigger_all_units {
            Some(0x0du8)
        } else if arg1 == self.game_ctx.trigger_completed_units {
            Some(0x0e)
        } else {
            None
        };
        if let Some(id) = ext_array_id {
            // Hacky way to reuse the patched addr array
            let dummy = self.game_ctx.game;
            let address = ctrl.address();
            if self.game_ctx.patched_addresses.insert(address, (!0, dummy)).is_some()
            {
                return;
            }
            // Arg2 may be pointer to a game table (if memcpy)
            let arg2_loc = if !is_tail_call {
                arg_cache.on_call(1)
            } else {
                arg_cache.on_entry(1)
            };
            let arg2 = ctrl.resolve(arg2_loc);
            let ext_array2 = arg2.if_arithmetic_add()
                .filter(|x| x.0 == self.game_ctx.game)
                .and_then(|x| x.1.if_constant())
                .and_then(|c| match c {
                    0x3234 => Some(0x07u8),
                    0x5cf4 => Some(0x08),
                    _ => None,
                });
            let args = [
                id.wrapping_add(1),
                ext_array2.map(|x| x.wrapping_add(1)).unwrap_or(0),
                0,
                0,
            ];
            let patches = &mut self.game_ctx.result.patches;
            patches.push(DatPatch::ExtendedArrayArg(address, args));
            if let Err(e) = self.required_stable_addresses.try_add_for_patch(
                self.binary,
                address,
                ctrl.current_instruction_end(),
            ) {
                dat_warn!(
                    self, "Can't add stable address for patch @ {:?}, conflict {:?}",
                    address, e,
                );
            }
        }
    }

    fn check_mem_access(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        mem_unres: &MemAccess<'e>,
    ) {
        let mem = ctrl.resolve_mem(mem_unres);
        if self.other_globals {
            let ctx = ctrl.ctx();
            let others = [
                (self.game_ctx.unit_strength, 0xe4 * 4 * 2),
                (self.game_ctx.ai_build_limit, 0xe4),
                (self.game_ctx.trigger_all_units, 0xe4 * 4 * 12),
                (self.game_ctx.trigger_completed_units, 0xe4 * 4 * 12),
            ];
            let (index, base) = mem.address();
            for &(start, len) in &others {
                if let Some(c2) = start.if_constant() {
                    let offset = base.wrapping_sub(c2);
                    if offset < len {
                        let index = ctx.add_const(index, offset);
                        if start == self.game_ctx.unit_strength {
                            self.patch_unit_strength(ctrl, index, mem_unres);
                        } else if start == self.game_ctx.ai_build_limit {
                            self.patch_ai_unit_limit(ctrl, index);
                        } else if start == self.game_ctx.trigger_all_units ||
                            start == self.game_ctx.trigger_completed_units
                        {
                            let id = if start == self.game_ctx.trigger_all_units {
                                0x0d
                            } else {
                                0x0e
                            };
                            self.patch_unit_counts(ctrl, index, id);
                        }
                    }
                }
            }
        } else {
            self.check_game_mem_access(ctrl, &mem);
        }
    }

    fn check_game_mem_access(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        mem: &MemAccess<'e>,
    ) {
        let ctx = ctrl.ctx();
        let game = self.game_ctx.game;
        let bump = &self.game_ctx.analysis.bump;
        let (base, offset) = mem.address();
        if offset < 0x18c || offset > 0x1034f {
            return;
        }
        let offset = offset as u32;
        let mut terms = crate::add_terms::collect_arith_add_terms(base, bump);
        if !terms.remove_one(|x, _neg| x == game) {
            return;
        }
        let index = terms.join(ctx);
        let index_zero = index == ctx.const_0();
        // If upgrades / tech memaccess isn't byte sized, don't patch it as it
        // won't work out due to switch from [player][upgrade] indexing to [upgrade][player]
        // And it should just be initialization memset.
        let size_byte = mem.size == MemAccessSize::Mem8;
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
            0xdd34 ..= 0xde53 if size_byte => {
                self.patch_tech_array(ctrl, 3, 0x18, 0, offset - 0xdd34, index);
            }
            // Tech level sc
            0xde54 ..= 0xdf73 if size_byte => {
                self.patch_tech_array(ctrl, 2, 0x18, 0, offset - 0xde54, index);
            }
            // Upgrade limit sc
            0xdf98 ..= 0xe1bf if size_byte => {
                self.patch_upgrade_array_sc(ctrl, 1, offset - 0xdf98, index);
            }
            // Upgrade level sc
            0xe1c0 ..= 0xe3e7 if size_byte => {
                self.patch_upgrade_array_sc(ctrl, 0, offset - 0xe1c0, index);
            }
            // Tech availability bw
            0xff48 if !index_zero && size_byte => {
                self.patch_tech_array(ctrl, 3, 0x14, 0, 0, index);
            }
            // Tech level bw
            0x10038 if !index_zero && size_byte => {
                self.patch_tech_array(ctrl, 2, 0x14, 0, 0, index);
            }
            // Upgrade limit bw
            0x1015a if !index_zero && size_byte => {
                self.patch_upgrade_array_bw(ctrl, 1, 0, 0, index);
            }
            // Upgrade level bw
            0x1020e if !index_zero && size_byte => {
                self.patch_upgrade_array_bw(ctrl, 0, 0, 0, index);
            }
            // Tech availability bw (Real)
            0xff60 ..= 0x1004f if size_byte => {
                self.patch_tech_array(ctrl, 3, 0x14, 0x18, offset - 0xff60, index)
            }
            // Tech level bw (Real)
            0x10050 ..= 0x1013f if size_byte => {
                self.patch_tech_array(ctrl, 3, 0x14, 0x18, offset - 0x10050, index)
            }
            // Tech being researched bits
            0x10140 ..= 0x10187 if size_byte => {
                self.patch_bit_array(ctrl, 5, 6, offset - 0x10140, index);
            }
            // Upgrade limit bw (Real)
            0x10188 ..= 0x1023b if size_byte => {
                self.patch_upgrade_array_bw(ctrl, 1, 0x2e, offset - 0x10188, index)
            }
            // Upgrade level bw (Real)
            0x1023c ..= 0x102ef if size_byte => {
                self.patch_upgrade_array_bw(ctrl, 0, 0x2e, offset - 0x1023c, index)
            }
            // Upgrade being researched bits
            0x102f0 ..= 0x1034f if size_byte => {
                self.patch_bit_array(ctrl, 4, 8, offset - 0x102f0, index);
            }
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
        let patch_indices = &mut self.patch_indices;
        let &mut (i, old_index) = self.game_ctx.patched_addresses.entry(address)
            .or_insert_with(|| {
                let i = patches.len();
                patch_indices.push(i);
                patches.push(DatPatch::ExtendedArray(ExtArrayPatch {
                    address,
                    instruction_len: 0,
                    ext_array_id: 0,
                    index,
                    two_step: None,
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
            two_step: None,
        });
    }

    fn player_upgrade_from_index(
        &self,
        index: Operand<'e>,
        byte_offset: u32,
        array_size: u32,
    ) -> (Operand<'e>, Operand<'e>) {
        let ctx = self.game_ctx.analysis.ctx;
        // player = (byte_offset + index) / arr_size
        // upgrade = (byte_offset + index) % arr_size
        let arr_size = ctx.constant(array_size.into());
        let index = ctx.add_const(index, u64::from(byte_offset));
        let player = ctx.div(index, arr_size);
        let upgrade = ctx.modulo(index, arr_size);
        (player, upgrade)
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
            (a, b) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let fallback = self.player_upgrade_from_index(index_unres, byte_offset, 0x2e);
                    let player = a.unwrap_or(fallback.0);
                    let upgrade = b.unwrap_or(fallback.1);
                    (player, upgrade)
                } else {
                    dat_warn!(self, "Unable to find operands for player/upgrade");
                    return;
                }
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
        // originally index = (upgrade - 2e) + player * f
        let (player, upgrade) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(0xf))
        {
            Some(s) => s,
            None => {
                if index.if_constant().is_none() && !index.is_undefined() {
                    // The code below assumes values to be in bounds,
                    // (e.g. never extended upgrades)
                    // Undefined check may still let something incorrectly past
                    // if inlining settings change, but hoping they won't.
                    dat_warn!(self, "Unable to split player/upgrade");
                    return;
                }
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
            (a, b) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let fallback = self.player_upgrade_from_index(index_unres, byte_offset, 0xf);
                    let player = a.unwrap_or(fallback.0);
                    let upgrade = b.unwrap_or(fallback.1);
                    (player, upgrade)
                } else {
                    dat_warn!(self, "Unable to find operands for player/upgrade");
                    return;
                }
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
        let player_tech_from_index = |index| {
            // player = (byte_offset + index) / arr_size
            // tech = (byte_offset + index) % arr_size
            let arr_size = ctx.constant(array_size.into());
            let index = ctx.add_const(index, u64::from(byte_offset));
            let player = ctx.div(index, arr_size);
            let tech = ctx.modulo(index, arr_size);
            (player, tech)
        };

        let (player, tech) = match index.if_arithmetic_add()
            .and_either(|x| x.if_arithmetic_mul_const(array_size as u64))
        {
            Some(s) => s,
            None => {
                dat_warn!(self, "Couldn't split tech index {}", index);
                return;
            }
        };
        let (player, tech) = match
            (self.unresolve(ctrl, player), self.unresolve(ctrl, tech))
        {
            (Some(a), Some(b)) => (a, b),
            (a, b) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let fallback = player_tech_from_index(index_unres);
                    let player = a.unwrap_or(fallback.0);
                    let tech = b.unwrap_or(fallback.1);
                    (player, tech)
                } else {
                    dat_warn!(self, "Unable to find operands for player/tech");
                    return;
                }
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
        let player_id_from_index = |index| {
            // player = index / expected_bytes_per_player
            // id = index % expected_bytes_per_player
            let divisor = ctx.constant(expected_bytes_per_player.into());
            let id = ctx.modulo(
                index,
                divisor,
            );
            let player = ctx.div(
                index,
                divisor,
            );
            (player, id)
        };
        let player_id = index.if_arithmetic_add()
            .and_either(|x| {
                // Accept (id >> 3) and (id >> 3) & 1f, and mask gets used
                // when id is u8(register_arg)
                if x.if_arithmetic_and_const(0x1f).unwrap_or(x)
                    .if_arithmetic_rsh_const(3).is_some()
                {
                    Some(x)
                } else {
                    None
                }
            })
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
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    player_id_from_index(index_unres)
                } else {
                    dat_warn!(
                        self, "Unable to find operands for player {} / id {} @ {:?}",
                        player, id, ctrl.address(),
                    );
                    return;
                }
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
                    dat_warn!(self, "Unable to find operands for player/id");
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
        mem_unres: &MemAccess<'e>,
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

        let (unit_id, is_ground) = if index.if_constant()
            .is_some_and(|c| c == 0 || c == 0xe4 * 4)
        {
            // Hackfix for 64bit unit strength init loop, which does
            //     mov reg, strength_array
            //     mov [reg], result
            //     reg += 4
            // instead of `mov [base + index], result`
            //
            // If index is constant to index 0 or 0xe4 * 4,
            // assume index to be instead an variable based on mem_unres
            let index_unres = ctx.mem_sub_op(mem_unres, self.game_ctx.unit_strength);
            id_ground_from_index(index_unres)
        } else {
            let (unit_id, is_ground) = id_ground_from_index(index);
            match (self.unresolve(ctrl, unit_id), self.unresolve(ctrl, is_ground)) {
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
                        dat_warn!(self, "Unable to find operands for is_ground/id");
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
                        dat_warn!(self, "Unable to find operands for is_ground/id");
                        return;
                    }
                }
                _ => {
                    dat_warn!(self, "Unable to find operands for is_ground/id");
                    return;
                }
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
        let player_ai_size = E::struct_layouts().player_ai_size();
        let (unit_id, player) = Some(index)
            .and_then(|x| x.if_arithmetic_add())
            .and_either(|x| x.if_arithmetic_mul_const(player_ai_size))
            .map(|(player, id)| (id, player))
            .or_else(|| {
                index.if_arithmetic_mul_const(0xe4 * 4)
                    .map(|x| (ctx.const_0(), x))
            })
            .unwrap_or_else(|| {
                let unit_id = ctx.modulo(index, ctx.constant(player_ai_size));
                let player = ctx.div(index, ctx.constant(player_ai_size));
                (unit_id, player)
            });
        let (unit_id, player) =
            match (self.unresolve(ctrl, unit_id), self.unresolve(ctrl, player))
        {
            (Some(a), Some(b)) => (a, b),
            (Some(unit_id), None) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let player = ctx.div(
                        ctx.sub(
                            index_unres,
                            unit_id,
                        ),
                        ctx.constant(player_ai_size),
                    );
                    (unit_id, player)
                } else {
                    dat_warn!(self, "Unable to find operands for player/id");
                    return;
                }
            }
            (None, Some(player)) => {
                if let Some(index_unres) = self.unresolve(ctrl, index) {
                    let unit_id = ctx.sub(
                        index_unres,
                        ctx.mul_const(player, player_ai_size),
                    );
                    (unit_id, player)
                } else {
                    dat_warn!(self, "Unable to find operands for player/id");
                    return;
                }
            }
            _ => {
                dat_warn!(self, "Unable to find operands for player/id");
                return;
            }
        };
        // Convert to (player + unit_id * 0xc)
        let index = ctx.add(
            player,
            ctx.mul_const(unit_id, 0xc),
        );
        self.add_patch(ctrl, 0xc, index);
    }

    fn patch_unit_counts(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        index: Operand<'e>,
        ext_array_id: u32
    ) {
        // No need to change the index =)
        let index = match self.unresolve(ctrl, index) {
            Some(a) => a,
            _ => {
                dat_warn!(self, "Unable to find operands for player/id");
                return;
            }
        };
        self.add_patch(ctrl, ext_array_id, index);
    }

    fn unresolve(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: Operand<'e>,
    ) -> Option<Operand<'e>> {
        let ctx = ctrl.ctx();
        let exec_state = ctrl.exec_state();
        crate::unresolve::unresolve(ctx, exec_state, op)
    }

    fn convert_to_two_step_hooks_where_needed(&mut self) {
        let binary = self.binary;
        for &i in &self.patch_indices {
            let address = match self.game_ctx.result.patches[i] {
                DatPatch::ExtendedArray(ref patch) => Some(patch.address),
                _ => None,
            };
            if let Some(address) = address {
                if let Err(_) = self.required_stable_addresses.try_add_for_patch(
                    binary,
                    address,
                    address + 5,
                ) {
                    if let Err(_) = self.required_stable_addresses.try_add_for_patch(
                        binary,
                        address,
                        address + 2,
                    ) {
                        dat_warn!(self, "Can't fit extended array patch to {:?}", address);
                        continue;
                    }
                    let mut hook_ctx = FunctionHookContext::<E> {
                        result: &mut self.game_ctx.result,
                        required_stable_addresses: self.required_stable_addresses,
                        binary: binary,
                        entry: self.func_start,
                    };
                    if let Some(free_space) = hook_ctx.find_short_jump_hook_space(address) {
                        match self.game_ctx.result.patches[i] {
                            DatPatch::ExtendedArray(ref mut patch) => {
                                patch.two_step = Some(free_space);
                            }
                            _ => (),
                        }
                    } else {
                        dat_warn!(self, "Can't find free space for hook @ {:?}", address);
                    }
                }
            }
        }
    }
}

fn if_const_or_mem_const<'e, E: ExecutionState<'e>>(
    val: Operand<'e>,
) -> Option<E::VirtualAddress> {
    val.if_constant()
        .or_else(|| {
            val.if_memory()
                .filter(|x| x.size == E::WORD_SIZE)
                .and_then(|x| x.if_constant_address())
        })
        .map(|x| E::VirtualAddress::from_u64(x))
}
