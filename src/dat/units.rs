use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operand, Operation};

use crate::{DatType, OperandExt, entry_of_until, EntryOf};
use super::{DatPatchContext, DatArrayPatch, reloc_address_of_instruction};

pub(crate) fn init_units_analysis<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, 'e, E>,
) -> Option<()> {
    let analysis = &mut dat_ctx.analysis;
    let init_units = analysis.init_units()?;
    let load_dat = analysis.load_dat()?;
    let (units_dat, field_size) = analysis.dat_virtual_address(DatType::Units)?;

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = InitUnitsAnalyzer {
        dat_ctx,
        load_dat,
        units_dat_target_acq_range: binary.read_address(units_dat + field_size * 0x17).ok()?,
        units_dat_dimensionbox_end:
            binary.read_address(units_dat + field_size * 0x26).ok()? + 0xe4 * 8,
        state: InitUnitsState::WireframeArray,
        inline_depth: 0,
        checked_funcs: Vec::with_capacity(32),
        binary,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, init_units);
    analysis.analyze(&mut analyzer);

    Some(())
}

pub struct InitUnitsAnalyzer<'a, 'b, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
    load_dat: E::VirtualAddress,
    units_dat_target_acq_range: E::VirtualAddress,
    units_dat_dimensionbox_end: E::VirtualAddress,
    state: InitUnitsState<'e>,
    inline_depth: u8,
    checked_funcs: Vec<E::VirtualAddress>,
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

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    InitUnitsAnalyzer<'a, 'b, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(DestOperand::Memory(ref mem), _, None) => {
                match self.state {
                    InitUnitsState::WireframeArray => {
                        let dest = ctrl.resolve(mem.address);
                        let expected_base = self.units_dat_target_acq_range.as_u64();
                        if let Some(index) = dest.if_arithmetic_add_const(expected_base) {
                            self.state = InitUnitsState::WireframeArray_TargetAcqStored(index);
                        }
                    }
                    InitUnitsState::WireframeArray_TargetAcqStored(index) => {
                        let dest = ctrl.resolve(mem.address);
                        if let Some(base) = dest.if_arithmetic_add()
                            .filter(|&(l, _)| l == index)
                            .and_then(|(_, r)| r.if_constant())
                            .filter(|&c| c != self.units_dat_target_acq_range.as_u64())
                        {
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
            Operation::Move(_, val, None)
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
                                entry: i32::min_value(),
                                byte_offset: 0,
                            });
                            self.state = InitUnitsState::Done;
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.state == InitUnitsState::UnitSearchInit {
                        let arg_cache = &self.dat_ctx.analysis.arg_cache;
                        let arg2 = ctrl.resolve(arg_cache.on_call(1));
                        let arg3 = ctrl.resolve(arg_cache.on_call(2));
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

pub(crate) fn button_use_analysis<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, 'e, E>,
    buttons: E::VirtualAddress,
) -> Option<()> {
    // For some reason, button condition param is passed as u8 to the condition function.
    // Widen it to u16.
    let analysis = &mut dat_ctx.analysis;
    let globals = crate::find_functions_using_global(analysis, buttons);
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = analysis.functions();
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

pub struct ButtonUseAnalyzer<'a, 'b, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
    result: EntryOf<()>,
    use_address: E::VirtualAddress,
    candidate_instruction: Option<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    ButtonUseAnalyzer<'a, 'b, 'e, E>
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
            Operation::Move(_, val, None) => {
                if let Some(addr) = val.if_mem8() {
                    let addr = ctrl.resolve(addr);
                    if addr.if_arithmetic_add_const(0xc).is_some() {
                        self.candidate_instruction = Some(ctrl.address());
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(cand) = self.candidate_instruction {
                    let dest = ctrl.resolve(dest);
                    let is_button_cond = ctrl.if_mem_word(dest)
                        .and_then(|x| x.if_arithmetic_add_const(0x4))
                        .is_some();
                    if is_button_cond {
                        let arg_cache = &self.dat_ctx.analysis.arg_cache;
                        let arg1 = ctrl.resolve(arg_cache.on_call(0));
                        let needs_widen = arg1.if_mem8()
                            .and_then(|x| x.if_arithmetic_add_const(0xc))
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

impl<'a, 'b, 'e, E: ExecutionState<'e>> ButtonUseAnalyzer<'a, 'b, 'e, E> {
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
                self.dat_ctx.add_warning(format!("Can't widen instruction @ {:?}", address));
                return;
            }
        };
        match *bytes {
            // movzx u8 to movzx u16
            [0x0f, 0xb6, ..] => {
                self.dat_ctx.add_replace_patch(address + 1, &[0xb7]);
            }
            _ => self.dat_ctx.add_warning(format!("Can't widen instruction @ {:?}", address)),
        }
    }
}
