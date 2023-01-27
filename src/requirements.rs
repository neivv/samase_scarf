use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, FlagArith, Operand, Operation};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::switch::CompleteSwitch;
use crate::util::{single_result_assign, OperandExt};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckUnitRequirements<'e, Va: VirtualAddress> {
    pub check_unit_requirements: Va,
    pub requirement_error: Operand<'e>,
}

pub(crate) fn check_unit_requirements<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<CheckUnitRequirements<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let requirement_offsets =
        binary.read_address(units_dat.0 + units_dat.1.checked_mul(0x2b)?).ok()?;

    let mut globals = functions.find_functions_using_global(analysis, requirement_offsets);
    globals.sort_unstable_by_key(|x| x.func_entry);
    globals.dedup_by_key(|x| x.func_entry);
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    let functions = functions.functions();
    for global_ref in globals {
        let val = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            // Move nonzero ptr to arg3 (unit) to avoid assertion checks
            // failing and causing analysis to break.
            let mut state = E::initial_state(ctx, binary);
            let arg3_loc = arg_cache.on_entry(2);
            state.move_resolved(
                &DestOperand::from_oper(arg3_loc),
                ctx.constant(0x1000_0000),
            );

            let mut analysis = FuncAnalysis::with_state(binary, ctx, entry, state);
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
                let ctx = ctrl.ctx();
                let ok = val.if_mem16_offset(self.requirement_offsets.as_u64())
                    .and_then(|x| x.if_arithmetic_mul_const(2))
                    .filter(|&x| {
                        let arg1 = self.arg_cache.on_entry(0);
                        ctx.and_const(x, 0xffff) == ctx.and_const(arg1, 0xffff)
                    })
                    .is_some();
                if ok {
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
                    let dest = ctrl.resolve_mem(mem);
                    self.result = EntryOf::Ok(ctx.memory(&dest));
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn check_dat_requirements<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    techdata_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let requirement_offsets = binary.read_address(
        techdata_dat.0 + techdata_dat.1.checked_mul(0x5)?,
    ).ok()?;

    let mut globals = functions.find_functions_using_global(analysis, requirement_offsets);
    globals.sort_unstable_by_key(|x| x.func_entry);
    globals.dedup_by_key(|x| x.func_entry);
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    let functions = functions.functions();
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
                    let ctx = ctrl.ctx();
                    let arg5 = ctx.and_const(
                        ctrl.resolve(self.arg_cache.on_call(4)),
                        0xffff_ffff,
                    );
                    let ok = arg5.if_mem16_offset(self.requirement_offsets.as_u64())
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
    analysis: &AnalysisCtx<'e, E>,
    check_dat_reqs: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, check_dat_reqs);
    let mut analyzer = CheatFlagsAnalyzer::<E> {
        result: None,
        switch_reached: false,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct CheatFlagsAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    switch_reached: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for CheatFlagsAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::SetFlags(ref arith) if self.switch_reached => {
                if arith.ty == FlagArith::And {
                    if ctrl.resolve(arith.right).if_constant() == Some(0x1000) {
                        self.result = Some(ctrl.resolve(arith.left));
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                if to.if_constant().is_none() {
                    if self.switch_reached {
                        ctrl.end_branch();
                        return;
                    }
                    let binary = ctrl.binary();
                    let ctx = ctrl.ctx();
                    if let Some(switch) = CompleteSwitch::new(to, ctx, ctrl.exec_state()) {
                        if let Some(branch) = switch.branch(binary, ctx, 0xff0f) {
                            ctrl.clear_unchecked_branches();
                            ctrl.end_branch();
                            ctrl.add_branch_with_current_state(branch);
                            self.switch_reached = true;
                            return;
                        }
                    }
                }
            }
            _ => (),
        }
    }
}
