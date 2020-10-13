use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{ArithOpType, BinaryFile, DestOperand, Operand, Operation};

use crate::{
    AnalysisCtx, ArgCache, DatType, entry_of_until, EntryOf, find_functions_using_global,
    single_result_assign, OperandExt,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckUnitRequirements<'e, Va: VirtualAddress> {
    pub check_unit_requirements: Va,
    pub requirement_error: Operand<'e>,
}

pub(crate) fn check_unit_requirements<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<CheckUnitRequirements<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = analysis.functions();

    let units_dat = analysis.dat(DatType::Units)?;
    let units_dat_address = E::VirtualAddress::from_u64(units_dat.address.if_constant()?);
    let requirement_offsets =
        binary.read_address(units_dat_address + units_dat.entry_size.checked_mul(0x2b)?).ok()?;

    let mut globals = find_functions_using_global(analysis, requirement_offsets);
    globals.sort_unstable_by_key(|x| x.func_entry);
    globals.dedup_by_key(|x| x.func_entry);
    let mut result = None;
    let arg_cache = analysis.arg_cache;
    for global_ref in globals {
        let val = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = UnitReqsAnalyzer::<E> {
                result: EntryOf::Retry,
                global_address: global_ref.use_address,
                requirement_offsets,
                offsets_read: false,
                arg_cache,
            };
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();
        if let Some((addr, requirement_error)) = val {
            let val = CheckUnitRequirements {
                check_unit_requirements: addr,
                requirement_error,
            };
            if single_result_assign(Some(val), &mut result) {
                break;
            }
        }
    }
    result
}

struct UnitReqsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    global_address: E::VirtualAddress,
    requirement_offsets: E::VirtualAddress,
    offsets_read: bool,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitReqsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.global_address > ctrl.address() &&
            self.global_address < ctrl.current_instruction_end()
        {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Move(_, val, None) if !self.offsets_read => {
                let val = ctrl.resolve(val);
                let ok = val.if_mem16()
                    .and_then(|x| x.if_arithmetic_add_const(self.requirement_offsets.as_u64()))
                    .and_then(|x| x.if_arithmetic_mul_const(2))
                    .and_then(|x| {
                        let arg1 = self.arg_cache.on_entry(0);
                        if x == arg1 {
                            return Some(());
                        }
                        match x.if_memory()?.address == arg1.if_memory()?.address {
                            true => Some(()),
                            false => None,
                        }
                    })
                    .is_some();
                if ok {
                    let ctx = ctrl.ctx();
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(
                        &DestOperand::from_oper(val),
                        ctx.const_0(),
                    );
                    self.offsets_read = true;
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val, None) if self.offsets_read => {
                let val = ctrl.resolve(val);
                if val.if_constant() == Some(0x17) {
                    let ctx = ctrl.ctx();
                    let address = ctrl.resolve(mem.address);
                    self.result = EntryOf::Ok(ctx.mem_variable_rc(mem.size, address));
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn check_dat_requirements<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = analysis.functions();

    let techdata_dat = analysis.dat(DatType::TechData)?;
    let techdata_dat_address = E::VirtualAddress::from_u64(techdata_dat.address.if_constant()?);
    let requirement_offsets = binary.read_address(
        techdata_dat_address + techdata_dat.entry_size.checked_mul(0x5)?,
    ).ok()?;

    let mut globals = find_functions_using_global(analysis, requirement_offsets);
    globals.sort_unstable_by_key(|x| x.func_entry);
    globals.dedup_by_key(|x| x.func_entry);
    let mut result = None;
    let arg_cache = analysis.arg_cache;
    for global_ref in globals {
        let val = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = DatReqsAnalyzer::<E> {
                result: EntryOf::Retry,
                global_address: global_ref.use_address,
                requirement_offsets,
                arg_cache,
            };
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

struct DatReqsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<E::VirtualAddress>,
    global_address: E::VirtualAddress,
    requirement_offsets: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for DatReqsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.global_address > ctrl.address() &&
            self.global_address < ctrl.current_instruction_end()
        {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let arg5 = ctrl.resolve(self.arg_cache.on_call(4));
                    let ok = arg5.if_mem16()
                        .and_then(|x| {
                            x.if_arithmetic_add_const(self.requirement_offsets.as_u64())
                        })
                        .and_then(|x| x.if_arithmetic_mul_const(2))
                        .is_some();
                    if ok {
                        self.result = EntryOf::Ok(dest);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn cheat_flags<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let check_dat_reqs = analysis.check_dat_requirements()?;
    let mut analysis = FuncAnalysis::new(binary, ctx, check_dat_reqs);
    let mut analyzer = CheatFlagsAnalyzer::<E> {
        result: None,
        switch_reached: false,
        binary,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct CheatFlagsAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    switch_reached: bool,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CheatFlagsAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::SetFlags(arith, _size) if self.switch_reached => {
                if arith.ty == ArithOpType::And {
                    if ctrl.resolve(arith.right).if_constant() == Some(0x1000) {
                        self.result = Some(ctrl.resolve(arith.left));
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                if to.if_memory().is_some() {
                    let ctx = ctrl.ctx();
                    let new_to = ctx.transform(to, 8, |x| match x.if_mem16() {
                        Some(_) => Some(ctx.constant(0xff0f)),
                        None => None,
                    });
                    let binary = self.binary;
                    let addr = new_to.if_constant()
                        .map(|x| E::VirtualAddress::from_u64(x))
                        .or_else(|| {
                            let addr = new_to.if_memory()?.address.if_constant()?;
                            Some(binary.read_address(E::VirtualAddress::from_u64(addr)).ok()?)
                        });
                    if let Some(addr) = addr {
                        self.switch_reached = true;
                        ctrl.analyze_with_current_state(self, addr);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
