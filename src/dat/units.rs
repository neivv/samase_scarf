use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, DestOperand, Operand, Operation};

use crate::{DatType, OperandExt };
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
