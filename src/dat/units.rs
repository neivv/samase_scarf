use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operand, Operation};

use crate::analysis::{AnalysisCache};
use crate::analysis_find::{entry_of_until, EntryOf};
use crate::util::{bumpvec_with_capacity, ControlExt, ExecStateExt, OperandExt};
use super::{DatType, DatPatchContext, DatArrayPatch, reloc_address_of_instruction};

pub(crate) fn init_units_analysis<'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'_, 'e, E>,
    cache: &mut AnalysisCache<'e, E>,
) -> Option<()> {
    let analysis = &dat_ctx.analysis;
    let init_units = cache.init_units(analysis)?;
    let load_dat = cache.load_dat(analysis)?;
    let (units_dat, field_size) = cache.dat_virtual_address(DatType::Units, analysis)?;

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let mut analyzer = InitUnitsAnalyzer {
        dat_ctx,
        load_dat,
        units_dat_target_acq_range: binary.read_address(units_dat + field_size * 0x17).ok()?,
        units_dat_dimensionbox_end:
            binary.read_address(units_dat + field_size * 0x26).ok()? + 0xe4 * 8,
        state: InitUnitsState::WireframeArray,
        inline_depth: 0,
        checked_funcs: bumpvec_with_capacity(32, bump),
        binary,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_units);
    analysis.analyze(&mut analyzer);

    Some(())
}

pub struct InitUnitsAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'acx, 'e, E>,
    load_dat: E::VirtualAddress,
    units_dat_target_acq_range: E::VirtualAddress,
    units_dat_dimensionbox_end: E::VirtualAddress,
    state: InitUnitsState<'e>,
    inline_depth: u8,
    checked_funcs: BumpVec<'acx, E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
#[allow(bad_style)]
enum InitUnitsState<'e> {
    WireframeArray,
    WireframeArray_TargetAcqStored(Operand<'e>),
    UnitSearchInit,
    UnitSearchInit_MemsetSeen,
    Done,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    InitUnitsAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(DestOperand::Memory(ref mem), _) => {
                match self.state {
                    InitUnitsState::WireframeArray => {
                        let dest = ctrl.resolve_mem(mem);
                        let (index, base) = dest.address();
                        let expected_base = self.units_dat_target_acq_range.as_u64();
                        if base == expected_base {
                            self.state = InitUnitsState::WireframeArray_TargetAcqStored(index);
                        }
                    }
                    InitUnitsState::WireframeArray_TargetAcqStored(index) => {
                        let dest = ctrl.resolve_mem(mem);
                        let (dest_index, base) = dest.address();
                        if dest_index == index &&
                            base != self.units_dat_target_acq_range.as_u64()
                        {
                            let ctx = ctrl.ctx();
                            self.dat_ctx.result.unit_wireframe_type = Some(ctx.constant(base));
                            let base = E::VirtualAddress::from_u64(base);
                            let end = base + 0xe4;
                            self.dat_ctx.add_dat_global_refs(
                                DatType::Units,
                                0x41,
                                base,
                                end,
                                0,
                                1,
                                false,
                            );
                            // Also nop the current instruction so that bw no longer
                            // stores anything to the wireframe type array.
                            if self.dat_ctx.patched_addresses.insert(ctrl.address()) {
                                let ins_len = (ctrl.current_instruction_end().as_u64() as usize)
                                    .wrapping_sub(ctrl.address().as_u64() as usize);
                                let nops = [0x90; 0x10];
                                self.dat_ctx.add_replace_patch(ctrl.address(), &nops[..ins_len]);
                            }

                            self.state = InitUnitsState::UnitSearchInit;
                        }
                    }
                    _ => (),
                }
            }
            Operation::Move(_, val)
                if self.state == InitUnitsState::UnitSearchInit_MemsetSeen =>
            {
                if let Some(c) = val.if_constant() {
                    if c == self.units_dat_dimensionbox_end.as_u64() {
                        if let Some(patch_addr) = reloc_address_of_instruction(
                            ctrl,
                            self.binary,
                            self.units_dat_dimensionbox_end,
                        ) {
                            // units_dat_dimensionbox_end is also likely start of another
                            // array, and we can't distinguish that array start from this
                            // array end without this kind of analysis.
                            self.dat_ctx.add_or_override_dat_array_patch(DatArrayPatch {
                                dat: DatType::Units,
                                field_id: 0x26,
                                address: patch_addr,
                                entry: i32::MIN,
                                orig_entry: 0xe4,
                                byte_offset: 0,
                            });
                            self.state = InitUnitsState::Done;
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.state == InitUnitsState::UnitSearchInit {
                        let arg2 = ctrl.resolve_arg(1);
                        let arg3 = ctrl.resolve_arg(2);
                        let is_memset =
                            arg2.if_constant().filter(|&c| c as u8 == 0xff).is_some() &&
                            arg3.if_arithmetic_mul_const(8).is_some();
                        if is_memset {
                            self.state = InitUnitsState::UnitSearchInit_MemsetSeen;
                            return;
                        }
                        if self.inline_depth != 0 {
                            return;
                        }
                    }
                    if dest == self.load_dat {
                        return;
                    }
                    if self.checked_funcs.contains(&dest) {
                        return;
                    }
                    self.checked_funcs.push(dest);
                    self.inline_depth += 1;
                    ctrl.analyze_with_current_state(self, dest);
                    self.inline_depth -= 1;
                    if self.state == InitUnitsState::Done {
                        return;
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn button_use_analysis<'acx, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'acx, 'e, E>,
    cache: &mut AnalysisCache<'e, E>,
    buttons: E::VirtualAddress,
) -> Option<()> {
    // For some reason, button condition param is passed as u8 to the condition function.
    // Widen it to u16.
    let functions = cache.function_finder();
    let analysis = &dat_ctx.analysis;
    let globals = functions.find_functions_using_global(analysis, buttons);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = functions.functions();
    for global in &globals {
        entry_of_until(binary, &functions, global.use_address, |entry| {
            let mut analyzer = ButtonUseAnalyzer {
                dat_ctx,
                use_address: global.use_address,
                result: EntryOf::Retry,
                candidate_instruction: None,
                binary,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        });
    }

    Some(())
}

pub struct ButtonUseAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'acx, 'e, E>,
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    candidate_instruction: Option<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    ButtonUseAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.use_address >= ctrl.address() &&
            self.use_address < ctrl.current_instruction_end()
        {
            self.result = EntryOf::Ok(());
        }
        match *op {
            Operation::Move(_, val) => {
                if let Some(mem) = val.if_mem8() {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.address().1 == E::struct_layouts().button_condition_param() {
                        self.candidate_instruction = Some(ctrl.address());
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(cand) = self.candidate_instruction {
                    let dest = ctrl.resolve(dest);
                    let is_button_cond =
                        ctrl.if_mem_word_offset(dest, E::struct_layouts().button_condition_func())
                            .is_some();
                    if is_button_cond {
                        let arg1 = ctrl.resolve_arg(0);
                        let needs_widen =
                            arg1.if_mem8_offset(E::struct_layouts().button_condition_param())
                                .is_some();
                        if needs_widen {
                            self.widen_instruction(cand);
                            self.result = EntryOf::Ok(());
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        self.candidate_instruction = None;
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> ButtonUseAnalyzer<'a, 'acx, 'e, E> {
    fn widen_instruction(&mut self, address: E::VirtualAddress) {
        // Would be nice if this could be shared with DatReferringFuncAnalysis::widen_instruction,
        // but seems inconvinient to implement..
        // Especially since this does u8 -> u16 conversion
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self.dat_ctx, "Can't widen instruction @ {:?}", address);
                return;
            }
        };
        match *bytes {
            // movzx u8 to movzx u16
            [0x0f, 0xb6, ..] => {
                self.dat_ctx.add_replace_patch(address + 1, &[0xb7]);
            }
            // movzx u8 to movzx u16 (With rex prefix)
            [first, 0x0f, 0xb6, ..] if first & 0xf0 == 0x40 && E::VirtualAddress::SIZE == 8 => {
                self.dat_ctx.add_replace_patch(address + 2, &[0xb7]);
            }
            _ => dat_warn!(self.dat_ctx, "Can't widen instruction @ {:?}", address),
        }
    }
}

pub(crate) fn command_analysis<'acx, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'acx, 'e, E>,
    cache: &mut AnalysisCache<'e, E>,
) -> Option<()> {
    // Remove unit_id <= 105 check from Command_train,
    // unit_id >= 130 && unit_id <= 152 from zerg building morph
    let analysis = &dat_ctx.analysis;
    let switch = cache.process_commands_switch(analysis)?;
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    for &case in &[0x1f, 0x35] {
        let branch = switch.branch(binary, ctx, case)?;

        let mut analyzer = CommandPatch {
            dat_ctx,
            inline_depth: 0,
            done: 0,
            expected_done: if case == 0x1f { 1 } else { 2 },
            half_done: false,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, branch);
        analysis.analyze(&mut analyzer);
        if analyzer.done != analyzer.expected_done {
            dat_warn!(
                dat_ctx, "Did not find all command patches for command {:x} (Found {})",
                case, analyzer.done,
            );
        }
    }

    Some(())
}

pub struct CommandPatch<'a, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'acx, 'e, E>,
    inline_depth: u8,
    done: u8,
    expected_done: u8,
    /// If zerg building morph check is two comparisons for min/max id instead
    /// of `x - 82 > 16`, mark this true for the first comparison.
    half_done: bool,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    CommandPatch<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        ctrl.aliasing_memory_fix(op);
        match *op {
            Operation::Move(ref dest, value) => {
                self.dat_ctx.rdtsc_tracker.check(ctrl, dest, value);
            }
            Operation::Jump { condition, to } => {
                if self.inline_depth == 0 {
                    // Stop at switch jump
                    let ctx = ctrl.ctx();
                    if condition == ctx.const_1() && to.if_constant().is_none() {
                        ctrl.end_branch();
                        return;
                    }
                }
                let condition = ctrl.resolve(condition);
                if let Some(to) = ctrl.resolve_va(to) {
                    if self.dat_ctx.rdtsc_tracker.check_rdtsc_jump(ctrl, condition, to) {
                        return;
                    }
                }
                // Train check
                let mut ok = condition.if_arithmetic_gt()
                    .and_then(|x| {
                        if x.1.if_constant() == Some(0x69) {
                            Some(x.0)
                        } else if x.0.if_constant() == Some(0x6a) {
                            Some(x.1)
                        } else {
                            None
                        }
                    })
                    .and_then(|x| x.if_mem16_offset(1))
                    .is_some();
                if !ok {
                    // Zerg building morph check.
                    // (((Mem16[(x + 1)] - 82) & ffff) > 16)
                    // and
                    // (((unit_id - 82) & ffff) > 16)
                    // ffff mask may not exist depending on codegen details
                    ok = condition.if_arithmetic_gt_const(0x16)
                        .and_then(|l| {
                            let l = l.if_arithmetic_and_const(0xffff).unwrap_or(l);
                            l.if_arithmetic_sub_const(0x82)?;
                            Some(())
                        })
                        .is_some();
                }
                let mut half_done = false;
                if !ok {
                    // Zerg building morph check halves
                    // as 82 > x or x > 98
                    if condition.if_arithmetic_gt_const(0x98).is_some() ||
                        condition.if_arithmetic_gt()
                            .is_some_and(|x| x.0.if_constant() == Some(0x82))
                    {
                        ok = true;
                        half_done = true;
                    }
                }
                if ok {
                    let nops = [0x90; 0x10];
                    let address = ctrl.address();
                    let instruction_len = (ctrl.current_instruction_end().as_u64() as u32)
                        .wrapping_sub(address.as_u64() as u32);
                    if let Some(nops) = nops.get(..(instruction_len as usize)) {
                        if !self.dat_ctx.patched_addresses.insert(address) {
                            return;
                        }
                        self.dat_ctx.add_replace_patch(address, nops);
                    }
                    if half_done {
                        if self.half_done {
                            self.half_done = false;
                            self.done += 1;
                        } else {
                            self.half_done = true;
                        }
                    } else {
                        self.done += 1;
                    }
                    if self.done == self.expected_done {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Call(dest) => {
                if self.inline_depth < 1 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if self.done != 0 {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}
