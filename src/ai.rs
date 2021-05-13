use arrayvec::ArrayVec;
use bumpalo::collections::Vec as BumpVec;
use scarf::{
    DestOperand, Operand, Operation, MemAccessSize, OperandCtx, OperandType, BinaryFile, Rva,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState};

use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

use crate::{
    ArgCache, OptionExt, OperandExt, single_result_assign, AnalysisCtx, unwrap_sext,
    entry_of_until, EntryOf, ControlExt, AnalysisCache, FunctionFinder,
};
use crate::hash_map::HashSet;

fn check_step_ai_scripts<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    funcs: &[E::VirtualAddress],
    ctx: OperandCtx<'e>,
    call_pos: E::VirtualAddress,
) -> Option<Operand<'e>> {
    entry_of_until(binary, funcs, call_pos, |entry| {
        let mut analyzer = StepAiScriptsAnalyzer::<E> {
            first_ai_script: None,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        analysis.analyze(&mut analyzer);
        match analyzer.first_ai_script {
            Some(s) => EntryOf::Ok(s),
            None => EntryOf::Retry,
        }
    }).into_option()
}

struct StepAiScriptsAnalyzer<'e, E: ExecutionState<'e>> {
    first_ai_script: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StepAiScriptsAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let cond = ctrl.resolve(condition);
                self.first_ai_script = cond.if_arithmetic_eq()
                    .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                    .and_then(|(c, other)| match c {
                        0 => Some(other),
                        _ => None,
                    })
                    .and_then(|other| {
                        if let Some((l, r)) = other.if_arithmetic_eq() {
                            Operand::either(l, r, |x| x.if_constant())
                                .and_then(|(c, other)| match c {
                                    0 => Some(other.clone()),
                                    _ => None,
                                })
                        } else {
                            Some(other.clone())
                        }
                    });
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

pub(crate) fn ai_update_attack_target<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_computer_return: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    // Order 0xa3 (Computer return) immediately calls ai_update_attack_target

    struct Analyzer<'exec, 'b, E: ExecutionState<'exec>> {
        result: Option<E::VirtualAddress>,
        args: &'b ArgCache<'exec, E>,
    }
    impl<'exec, 'b, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for Analyzer<'exec, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let arg1 = ctrl.resolve(self.args.on_call(0));
                        let arg2 = ctrl.resolve(self.args.on_call(1));
                        let arg3 = ctrl.resolve(self.args.on_call(2));
                        let args_ok = arg1.if_constant() == Some(0) &&
                            arg2.if_constant() == Some(1) &&
                            arg3.if_constant() == Some(0);
                        if args_ok {
                            self.result = Some(E::VirtualAddress::from_u64(dest));
                        }
                    }
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer {
        result: None,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, order_computer_return);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct AiScriptHook<'e, Va: VirtualAddressTrait> {
    pub op_limit_hook_begin: Va,
    pub op_limit_hook_end: Va,
    pub op_limit_ok: Va,
    pub op_limit_fail: Va,
    // Operand that the comparision should be done against.
    pub opcode_operand: Operand<'e>,
    pub script_operand_at_switch: Operand<'e>,
    pub switch_table: Va,
    pub switch_loop_address: Va,
    pub return_address: Va,
}

pub(crate) fn aiscript_hook<'e, E: ExecutionState<'e>>(
    cache: &mut AnalysisCache<'e, E>,
    analysis: &AnalysisCtx<'e, E>,
) -> Option<AiScriptHook<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let switch_tables = cache.switch_tables();
    let functions = cache.function_finder();
    let mut result = switch_tables.iter().filter(|switch| {
        let cases = &switch.cases;
        // Allowing new Blizz opcodes if that ever happens..
        // There aren't many 0x71-sized or larger tables anyways
        cases.len() >= 0x71 &&
            // 3 == 4 && 9 == a && 3e == 46 == 4c
            cases[3] == cases[4] &&
            cases[9] == cases[0xa] &&
            cases[0x3e] == cases[0x46] &&
            cases[0x3e] == cases[0x4c]
    }).flat_map(|switch_table| {
        functions.find_functions_using_global(analysis, switch_table.address)
            .into_iter().map(move |f| (f.func_entry, switch_table.address))
    }).filter_map(|(entry, switch_table)| {
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        let mut analyzer: AiscriptHookAnalyzer<E> = AiscriptHookAnalyzer {
            aiscript_operand: None,
            switch_state: None,
            branch_start: entry,
            best_def_jump: None,
            op_default_jump: None,
        };
        analysis.analyze(&mut analyzer);

        let tp = (analyzer.best_def_jump, analyzer.aiscript_operand, analyzer.switch_state);
        if let (Some(default_jump), Some(script_operand_orig), Some(switch_state)) = tp {
            let (op_limit_ok, op_limit_fail) = match default_jump.jumps_to_default {
                true => (default_jump.branch_end, default_jump.to),
                false => (default_jump.to, default_jump.branch_end),
            };
            switch_state.unresolve(script_operand_orig)
                .and_then(|at_switch| {
                    aiscript_find_switch_loop_and_end::<E>(binary, ctx, switch_table)
                        .map(move |(switch_loop_address, return_address)| {
                            AiScriptHook {
                                op_limit_hook_begin: default_jump.branch_start,
                                op_limit_hook_end: default_jump.address,
                                op_limit_ok,
                                op_limit_fail,
                                opcode_operand: default_jump.opcode,
                                script_operand_at_switch: at_switch,
                                switch_table,
                                switch_loop_address,
                                return_address,
                            }
                        })
                })
        } else {
            None
        }
    });
    let first = result.next();
    if crate::test_assertions() && first.is_some() {
        assert!(result.next().is_none());
    }
    first
}

struct AiscriptHookAnalyzer<'e, E: ExecutionState<'e>> {
    aiscript_operand: Option<Operand<'e>>,
    switch_state: Option<E>,
    branch_start: E::VirtualAddress,
    best_def_jump: Option<BestDefaultJump<'e, E::VirtualAddress>>,
    op_default_jump: Option<OpDefaultJump<'e, E::VirtualAddress>>,
}

struct OpDefaultJump<'e, Va: VirtualAddressTrait> {
    address: Va,
    to: Va,
    jumps_to_default: bool,
    opcode: Operand<'e>,
}

/// Since scarf doesn't have any kind of CFG representation, this'll take care of
/// cases where code like
///      cmp eax, 1
///      jne y:
///      x:
///      mov ecx, 1
///      y:
///      cmp esi, 70
///      ja invalid
/// could hook from `x` instead of `y`
struct BestDefaultJump<'e, Va: VirtualAddressTrait> {
    address: Va,
    to: Va,
    branch_start: Va,
    branch_end: Va,
    jumps_to_default: bool,
    opcode: Operand<'e>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiscriptHookAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, to } => {
                let condition = match condition.if_constant() {
                    Some(_) => None,
                    None => Some(condition),
                };
                let to = ctrl.resolve(to);
                match (condition, to.ty()) {
                    // Check for switch jump
                    (None, &OperandType::Memory(ref mem)) => {
                        // Checking for arith since it could tecnically be a
                        // tail call to fnptr.
                        if let OperandType::Arithmetic(_) = mem.address.ty() {
                            let state = ctrl.exec_state();
                            self.switch_state = Some(state.clone());
                        }
                    }
                    // Check for default case jump
                    (Some(cond), &OperandType::Constant(to)) => {
                        let resolved = ctrl.resolve(cond);
                        let ctx = ctrl.ctx();
                        let state = ctrl.exec_state();
                        let jumps = is_aiscript_switch_jump(ctx, resolved, state);
                        if let Some((jumps_to_default, opcode)) = jumps {
                            trace!("Ais default jump {}", resolved);
                            self.op_default_jump = Some(OpDefaultJump {
                                address: ctrl.address(),
                                to: E::VirtualAddress::from_u64(to),
                                jumps_to_default,
                                opcode,
                            });
                        }
                    }
                    _ => (),
                }
            }
            Operation::Move(ref dest, val, _cond) => {
                // Try to find script->pos += 1
                if self.aiscript_operand.is_none() {
                    if let DestOperand::Memory(ref mem) = dest {
                        let addr = ctrl.resolve(mem.address);
                        if mem.size == MemAccessSize::Mem32 {
                            let val = ctrl.resolve(val);
                            let val_refers_to_dest = val.iter_no_mem_addr().any(|x| {
                                x.if_memory()
                                    .map(|x| x.address == addr)
                                    .unwrap_or(false)
                            });
                            if val_refers_to_dest {
                                self.aiscript_operand = addr.if_arithmetic_add()
                                    .and_then(|(l, r)| {
                                        Operand::either(l, r, |x| x.if_constant())
                                    })
                                    .filter(|&(c, _)| c == 8)
                                    .map(|x| x.1.clone());
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.branch_start = ctrl.address();
        self.op_default_jump = None;
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if let Some(jump) = self.op_default_jump.take() {
            let is_better = self.best_def_jump.as_ref().map(|x| {
                (jump.address.as_u64() - self.branch_start.as_u64()) <
                    (x.address.as_u64() - x.branch_start.as_u64())
            }).unwrap_or(true);
            if is_better {
                self.best_def_jump = Some(BestDefaultJump {
                    address: jump.address,
                    branch_start: self.branch_start,
                    branch_end: ctrl.address(),
                    to: jump.to,
                    jumps_to_default: jump.jumps_to_default,
                    opcode: jump.opcode,
                });
            }
        }
    }
}

/// Check if condition is `Mem8[x] > 0x70` or reverse of it.
/// Return Some(true) if the jump is when x > 0x70,
/// and Some(false) if jump is when x <= 0x70.
///
/// The second value is opcode operand (unresolved)
fn is_aiscript_switch_jump<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    condition: Operand<'e>,
    state: &mut E,
) -> Option<(bool, Operand<'e>)> {
    // The chances of there being another jump with different constresults when Mem8[x]
    // is replaced by 0x70 and 0x71 is low, so use that instead of trying to match all
    // gt/lt/ge/le variations
    let simplified_70 = ctx.transform(condition, 16, |x| match x.if_mem8().is_some() {
        true => Some(ctx.constant(0x70)),
        false => None,
    });
    let const_70 = match simplified_70.if_constant() {
        Some(x) => x,
        _ => return None,
    };
    let simplified_71 = ctx.transform(condition, 16, |x| match x.if_mem8().is_some() {
        true => Some(ctx.constant(0x71)),
        false => None,
    });
    let const_71 = match simplified_71.if_constant() {
        Some(x) => x,
        _ => return None,
    };
    let gt_jump = match (const_70, const_71) {
        (0, x) if x != 0 => true,
        (x, 0) if x != 0 => false,
        _ => return None,
    };
    condition.iter().find(|x| {
        x.if_mem8().is_some()
    }).and_then(|opcode_mem| {
        state.unresolve(opcode_mem)
    }).map(|x| (gt_jump, x))
}

fn aiscript_find_switch_loop_and_end<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    switch_table: E::VirtualAddress,
) -> Option<(E::VirtualAddress, E::VirtualAddress)> {
    let opcode_case = binary.read_u32(switch_table + 0xb * 4).ok()?;
    let second_opcode_case = binary.read_u32(switch_table + 0x2b * 4).ok()?;
    let wait_case = binary.read_u32(switch_table + 0x2 * 4).ok()?;
    let opcode_case = E::VirtualAddress::from_u64(opcode_case as u64);
    let mut analysis = FuncAnalysis::new(binary, ctx, opcode_case);
    let mut analyzer: AiscriptFindSwitchLoop<E> = AiscriptFindSwitchLoop {
        first_op_jumps: ArrayVec::new(),
        first_op: true,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    let second_opcode_case = E::VirtualAddress::from_u64(second_opcode_case as u64);
    let mut analysis = FuncAnalysis::new(binary, ctx, second_opcode_case);
    analyzer.first_op = false;
    analysis.analyze(&mut analyzer);

    let wait_case = E::VirtualAddress::from_u64(wait_case as u64);
    let other = aiscript_find_switch_loop_end::<E>(binary, ctx, wait_case);
    analyzer.result.and_then(|x| other.map(|y| (x, y)))
}

struct AiscriptFindSwitchLoop<'e, E: ExecutionState<'e>> {
    first_op_jumps: ArrayVec<E::VirtualAddress, 4>,
    first_op: bool,
    result: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiscriptFindSwitchLoop<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if condition.if_constant().filter(|&c| c != 0).is_some() {
                    let to = ctrl.resolve(to);
                    if let Some(dest) = to.if_constant() {
                        if self.first_op {
                            self.first_op_jumps.push(E::VirtualAddress::from_u64(dest));
                            if self.first_op_jumps.is_full() {
                                ctrl.end_analysis();
                            }
                        } else {
                            if self.first_op_jumps.iter().any(|&x| x.as_u64() == dest) {
                                self.result = Some(E::VirtualAddress::from_u64(dest));
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

fn aiscript_find_switch_loop_end<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    wait_case: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let mut analysis = FuncAnalysis::new(binary, ctx, wait_case);
    let mut analyzer: AiscriptFindSwitchEnd<E> = AiscriptFindSwitchEnd {
        result: None,
        first_branch: true,
        not_inlined_op_read: false,
        wait_written: false,
        pos_written: false,
        old_base: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AiscriptFindSwitchEnd<'e, E: ExecutionState<'e>> {
    first_branch: bool,
    not_inlined_op_read: bool,
    wait_written: bool,
    pos_written: bool,
    old_base: Option<Operand<'e>>,
    result: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiscriptFindSwitchEnd<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ok = (self.pos_written && self.wait_written) ||
            (self.wait_written && self.not_inlined_op_read);
        if ok {
            self.result = Some(ctrl.address());
            ctrl.end_analysis();
        }
        match *op {
            Operation::Call(..) => {
                if self.first_branch {
                    self.not_inlined_op_read = true;
                }
            }
            Operation::Move(ref dest, val, _) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem32 {
                        let addr = ctrl.resolve(mem.address);
                        let c_write = addr.if_arithmetic_add()
                            .and_either(|x| x.if_constant());
                        if let Some((offset, base)) = c_write {
                            let old_ok = self.old_base.map(|x| x == base).unwrap_or(true);
                            if old_ok {
                                if offset == 0x8 {
                                    let val = ctrl.resolve(val);
                                    let ok = val.if_arithmetic_add()
                                        .and_then(|(l, r)| {
                                            Operand::either(l, r, |x| x.if_constant())
                                        })
                                        .filter(|&(c, _)| c == 2)
                                        .is_some();
                                    if ok {
                                        self.pos_written = true;
                                        self.old_base = Some(base.clone());
                                    }
                                } else if offset == 0xc {
                                    let val = ctrl.resolve(val);
                                    let ok = val.if_memory()
                                        .filter(|mem| mem.size == MemAccessSize::Mem16)
                                        .and_then(|mem| mem.address.if_arithmetic_add())
                                        .is_some();
                                    if self.not_inlined_op_read || ok {
                                        self.wait_written = true;
                                        self.old_base = Some(base.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        self.pos_written = false;
        self.wait_written = false;
        self.old_base = None;
    }

    fn branch_end(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        self.first_branch = false;
    }
}

pub(crate) fn first_ai_script<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_hook: &AiScriptHook<'e, E::VirtualAddress>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let funcs = functions.functions();
    let hook_start = aiscript_hook.op_limit_hook_begin;

    let result = entry_of_until(binary, &funcs, hook_start, |entry| {
        let mut result = None;
        let callers = functions.find_callers(analysis, entry);
        for caller in callers {
            let new = check_step_ai_scripts::<E>(binary, funcs, ctx, caller);
            if single_result_assign(new, &mut result) {
                break;
            }
        }
        if let Some(res) = result {
            EntryOf::Ok(res)
        } else {
            EntryOf::Retry
        }
    }).into_option();
    result
}

pub(crate) fn first_guard_ai<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    units_dat: (E::VirtualAddress, u32),
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    // There's a function referring build times and looping through all guard ais,
    // guard ais are the first memaccess
    let funcs = &functions.functions();
    let build_time_refs = {
        let (dat, dat_table_size) = units_dat;
        let times = binary.read_address(dat + 0x2a * dat_table_size)
            .unwrap_or_else(|_| E::VirtualAddress::from_u64(0));
        BumpVec::from_iter_in(
            functions.find_functions_using_global(analysis, times)
                .into_iter()
                .map(|global_ref| global_ref.use_address),
            bump,
        )
    };
    let mut result = None;
    // Since the guard ai should be first memaccess, and there are several unrelated
    // functions checking unit build time, try just first entry suggestion for each
    // use at first, and if that doesn't work then run through all of them.
    'outer: for &retry in &[false, true] {
        for &use_address in &build_time_refs {
            let new = entry_of_until(binary, &funcs, use_address, |entry| {
                let mut analyzer = GuardAiAnalyzer::<E> {
                    result: if retry { EntryOf::Retry } else { EntryOf::Stop },
                    phantom: Default::default(),
                    jump_limit: 5,
                    use_address,
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                analyzer.result
            }).into_option();
            if single_result_assign(new, &mut result) {
                break 'outer;
            }
        }
    }
    result
}

struct GuardAiAnalyzer<'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    jump_limit: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
    use_address: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for GuardAiAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let use_address = self.use_address;
        if ctrl.address() >= use_address && ctrl.current_instruction_end() < use_address {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Call(..) | Operation::Jump { .. } => {
                self.jump_limit -= 1;
                if self.jump_limit == 0 {
                    ctrl.end_analysis();
                }
            }
            Operation::Move(_, val, _) => {
                let val = ctrl.resolve(val);
                let ctx = ctrl.ctx();
                let result = val.if_mem32()
                    .and_then(|address| address.if_arithmetic_add())
                    .and_either(|x| x.if_arithmetic_mul())
                    .and_then(|((l, r), base)| {
                        Some((l, r))
                            .and_either(|x| x.if_constant().filter(|&c| c == 8))
                            .map(|_| base)
                    })
                    .map(|val| ctx.sub(val, ctx.constant(4)));
                if let Some(result) = result {
                    self.result = EntryOf::Ok(result);
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn player_ai_towns<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_switch_table: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let addr_size = E::VirtualAddress::SIZE;
    let start_town = binary.read_address(aiscript_switch_table + 0x3 * addr_size).ok()?;

    let state = AiTownState {
        jump_count: 0,
    };
    let exec_state = E::initial_state(ctx, binary);
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, start_town, exec_state, state);
    let mut analyzer = AiTownAnalyzer {
        result: None,
        inlining: false,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

#[derive(Clone, Copy)]
struct AiTownState {
    jump_count: u32,
}

impl analysis::AnalysisState for AiTownState {
    fn merge(&mut self, new: AiTownState) {
        self.jump_count = self.jump_count.max(new.jump_count);
    }
}

struct AiTownAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiTownAnalyzer<'e, E> {
    type State = AiTownState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let mut jump_check = false;
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        let old_jump_count = ctrl.user_state().jump_count;
                        ctrl.user_state().jump_count = 0;
                        ctrl.analyze_with_current_state(self, dest);
                        ctrl.user_state().jump_count = old_jump_count;
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    jump_check = true;
                }
            }
            Operation::Move(_, val, _cond) => {
                let res = self.ai_towns_check(val, ctrl);
                if single_result_assign(res, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            Operation::Jump { to, .. } => {
                if to.if_constant().is_none() {
                    ctrl.end_analysis();
                    return;
                }
                jump_check = true;
            }
            _ => (),
        }
        if jump_check {
            let state = ctrl.user_state();
            state.jump_count += 1;
            if self.inlining && state.jump_count > 5 {
                ctrl.end_analysis();
            } else if !self.inlining && state.jump_count > 2 {
                ctrl.end_branch();
            }
        }
    }
}

impl<'e, E: ExecutionState<'e>> AiTownAnalyzer<'e, E> {
    fn ai_towns_check(
        &self,
        val: Operand<'e>,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> Option<Operand<'e>> {
        let ctx = ctrl.ctx();
        let val = ctrl.resolve(val);
        // aiscript_start_town accesses player's first ai town
        if let Some(mem) = val.if_memory() {
            mem.address.if_arithmetic_add()
                .and_either(|x| x.if_arithmetic_mul())
                .and_then(|((l, r), other)| {
                    Operand::either(l, r, |x| x.if_constant())
                        .filter(|&(c, _)| c == 8)
                        .map(|_| ctx.sub(other, ctx.const_4()))
                })
        } else {
            None
        }
    }
}

pub(crate) fn player_ai<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript: &AiScriptHook<'e, E::VirtualAddress>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let addr_size = E::VirtualAddress::SIZE;
    let farms_notiming = binary.read_address(aiscript.switch_table + 0x32 * addr_size).ok()?;

    // Set script->player to 0
    let mut state = E::initial_state(ctx, binary);
    let player_offset = if addr_size == 4 { 0x10 } else { 0x18 };
    let player = ctx.mem32(ctx.add(
        aiscript.script_operand_at_switch,
        ctx.constant(player_offset),
    ));
    state.move_to(&DestOperand::from_oper(player), ctx.const_0());
    let mut analysis = FuncAnalysis::with_state(
        binary,
        ctx,
        farms_notiming,
        state,
    );
    let mut analyzer = PlayerAiAnalyzer {
        result: None,
        inlining: false,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct PlayerAiAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for PlayerAiAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(ref dest, val, _cond) => {
                if let DestOperand::Memory(mem) = dest {
                    let dest = ctrl.resolve(mem.address);
                    let val = ctrl.resolve(val);
                    let ctx = ctrl.ctx();
                    let result = val.if_arithmetic_or()
                        .and_either_other(|x| x.if_memory().filter(|mem| mem.address == dest))
                        .and_then(|y| y.if_constant())
                        .filter(|&c| c == 0x10)
                        .map(|_| ctx.sub(dest, ctx.constant(0x218)));
                    if single_result_assign(result, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { .. } => {
                if !self.inlining {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn attack_prepare<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_switch_table: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let addr_size = E::VirtualAddress::SIZE;
    let attack_prepare = binary.read_address(aiscript_switch_table + 0xd * addr_size).ok()?;

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, attack_prepare);
    let mut analyzer = AttackPrepareAnalyzer {
        result: None,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AttackPrepareAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AttackPrepareAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ok = Some(())
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                    .and_then(|x| x.if_mem32_offset(0x10))
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                    .and_then(|x| x.if_mem32_offset(0x24))
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                    .and_then(|x| x.if_mem32_offset(0x28))
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
                    .filter(|x| x.if_constant() == Some(1))
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(4)))
                    .filter(|x| x.if_constant() == Some(0))
                    .is_some();
                if ok {
                    self.result = ctrl.resolve(dest)
                        .if_constant()
                        .map(|x| E::VirtualAddress::from_u64(x));
                }
                ctrl.end_analysis();
            }
            Operation::Jump { .. } => {
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct AiStepFrameFuncs<Va: VirtualAddressTrait> {
    pub ai_step_region: Option<Va>,
    pub ai_spend_money: Option<Va>,
}

pub(crate) fn step_frame_funcs<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_objects: E::VirtualAddress,
    ai_regions: Operand<'e>,
    game: Operand<'e>,
) -> AiStepFrameFuncs<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = AiStepFrameFuncs {
        ai_step_region: None,
        ai_spend_money: None,
    };

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    let mut analyzer = StepRegionAnalyzer {
        result: &mut result,
        arg_cache,
        inline_depth: 0,
        checked_functions: HashSet::with_capacity_and_hasher(0x40, Default::default()),
        binary,
        ai_regions,
        game,
        searching_spend_money: false,
        game_seconds_checked: false,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct StepRegionAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut AiStepFrameFuncs<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    checked_functions: HashSet<Rva>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ai_regions: Operand<'e>,
    game: Operand<'e>,
    searching_spend_money: bool,
    game_seconds_checked: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for StepRegionAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) if !self.searching_spend_money => {
                if self.inline_depth < 3 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let relative = dest.as_u64().checked_sub(self.binary.base.as_u64());
                        if let Some(relative) = relative {
                            let rva = Rva(relative as u32);
                            if self.checked_functions.insert(rva) {
                                self.inline_depth += 1;
                                let ctx = ctrl.ctx();
                                let mut analysis = FuncAnalysis::new(self.binary, ctx, dest);
                                analysis.analyze(self);
                                self.inline_depth -= 1;
                                if let Some(result) = self.result.ai_step_region {
                                    if result.as_u64() == 0 {
                                        self.result.ai_step_region = Some(dest);
                                    }
                                    // ai_spend_money is expected to be at inline depth 1
                                    if self.inline_depth > 1 {
                                        ctrl.end_analysis();
                                    } else {
                                        self.searching_spend_money = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Operation::Call(dest) if self.searching_spend_money => {
                if self.game_seconds_checked {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.result.ai_spend_money = Some(dest);
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Jump { .. } if self.game_seconds_checked => {
                // No jumps expected after game second check
                ctrl.end_analysis();
            }
            Operation::Move(DestOperand::Memory(mem), val, None)
                if self.searching_spend_money && mem.size == MemAccessSize::Mem32 =>
            {
                // Search for ai_spend_money by checking for a global store
                // global = game.seconds < 4500 ? 7 : 0x25
                let val = ctrl.resolve(val);
                if val.iter_no_mem_addr()
                    .any(|x| {
                        // Checking for 4500 > Mem32[game.seconds]
                        x.if_arithmetic_gt()
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 4500))
                            .filter(|&x| is_game_seconds(self.game, x))
                            .is_some()
                    })
                {
                    self.game_seconds_checked = true;
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None) => {
                // step_objects has `counter = counter - 1`
                // instruction which is after step_ai, so we can stop
                // if that is reached.
                if self.inline_depth == 0 && mem.size == MemAccessSize::Mem32 {
                    let val = ctrl.resolve(val);
                    let dest = ctrl.resolve(mem.address);
                    let stop = val.if_arithmetic_sub_const(1)
                        .and_then(|x| x.if_mem32())
                        .filter(|&x| x == dest)
                        .is_some();
                    if stop {
                        ctrl.end_analysis();
                    }
                }
                if self.inline_depth != 0 {
                    // First branch of ai_step_region always clears flag 0x4
                    // region = ai_regions[arg1] + arg2 * region_size;
                    // region.flags &= !0x4;
                    //Mem8[
                    //  Mem32[((Mem32[(rsp + 4)] * 4) + ee8c64)] + (Mem32[(rsp + 8)] * 34) + 8
                    //  ]
                    let val = ctrl.resolve(val);
                    let dest = ctrl.resolve(mem.address);
                    let ok = val.if_arithmetic_and_const(0xfb)
                        .and_then(|x| x.if_mem8())
                        .filter(|&x| x == dest)
                        .and_then(|x| x.if_arithmetic_add_const(8)) // flag offset
                        .and_then(|x| x.if_arithmetic_add()) // addition for regions base + index
                        .and_either(|x| {
                            // One is arg2 * region_size (0x34),
                            // other is ai_regions[arg1], that is, Mem32[ai_regions + arg1 * 4]
                            // Check for just ai_regions[arg1]
                            x.if_memory()
                                .map(|x| x.address)
                                .and_then(|x| x.if_arithmetic_add())
                                .and_either_other(|x| Some(()).filter(|()| x == self.ai_regions))
                                .and_then(|x| x.if_arithmetic_mul())
                                .filter(|&(l, _r)| l == self.arg_cache.on_entry(0))
                        })
                        .is_some();
                    if ok {
                        self.result.ai_step_region = Some(E::VirtualAddress::from_u64(0));
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn give_ai<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    actions: E::VirtualAddress,
    units_dat: (E::VirtualAddress, u32),
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let action_create_unit = binary.read_address(actions + E::VirtualAddress::SIZE * 0x2c).ok()?;
    let units_dat_group_flags = binary.read_address(units_dat.0 + 0x2c * units_dat.1).ok()?;
    let units_dat_ai_flags = binary.read_address(units_dat.0 + 0x15 * units_dat.1).ok()?;

    let arg_cache = &analysis.arg_cache;
    let exec_state = E::initial_state(ctx, binary);
    let state = GiveAiState::SearchingSwitchJump;
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, action_create_unit, exec_state, state);
    let mut analyzer = GiveAiAnalyzer {
        result: None,
        arg_cache,
        inline_depth: 0,
        units_dat_group_flags,
        units_dat_ai_flags,
        stop_on_first_branch: false,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct GiveAiAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    units_dat_group_flags: E::VirtualAddress,
    units_dat_ai_flags: E::VirtualAddress,
    stop_on_first_branch: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum GiveAiState {
    // At inline depth 0 or 1, there's a switch jump checking trigegr.current_player.
    // Follow default case.
    SearchingSwitchJump,
    // Search for call to map_create_unit
    SearchingMapCreateUnit,
    // Wait for check against units_dat_group_flags[id]
    SearchingRaceCheck,
    // Search for GiveAi
    RaceCheckSeen,
    Stop,
}

impl analysis::AnalysisState for GiveAiState {
    fn merge(&mut self, new: GiveAiState) {
        if *self != new {
            if matches!(*self, GiveAiState::SearchingRaceCheck | GiveAiState::RaceCheckSeen) &&
                matches!(new, GiveAiState::SearchingRaceCheck | GiveAiState::RaceCheckSeen)
            {
                *self = GiveAiState::RaceCheckSeen;
            } else {
                *self = GiveAiState::Stop;
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for GiveAiAnalyzer<'a, 'e, E> {
    type State = GiveAiState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *ctrl.user_state() {
            GiveAiState::SearchingSwitchJump => {
                match *op {
                    Operation::Jump { condition, to } => {
                        let condition = ctrl.resolve(condition);
                        // Trigger.current_player = Mem32[arg1 + 10]
                        let is_switch_default_case = condition
                            .if_arithmetic_gt_const(0xd)
                            .and_then(|x| x.if_arithmetic_sub_const(0xd))
                            .and_then(|x| x.if_mem32())
                            .and_then(|x| x.if_arithmetic_add_const(0x10))
                            .filter(|&x| x == self.arg_cache.on_entry(0))
                            .is_some();
                        if is_switch_default_case {
                            if let Some(to) = ctrl.resolve(to).if_constant() {
                                let to = E::VirtualAddress::from_u64(to);
                                let mut analysis = FuncAnalysis::custom_state(
                                    ctrl.binary(),
                                    ctx,
                                    to,
                                    ctrl.exec_state().clone(),
                                    GiveAiState::SearchingMapCreateUnit,
                                );
                                analysis.analyze(self);
                                if self.result.is_some() {
                                    ctrl.end_analysis();
                                } else {
                                    ctrl.end_branch();
                                }
                            }
                        }
                    }
                    Operation::Call(dest) if self.inline_depth == 0 => {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                            self.inline_depth = match self.inline_depth.checked_sub(1) {
                                Some(s) => s,
                                None => {
                                    ctrl.end_branch();
                                    return;
                                }
                            };
                        }
                    }
                    _ => (),
                }
            }
            GiveAiState::SearchingMapCreateUnit => {
                fn is_sdiv_2(op: Operand<'_>) -> bool {
                    // Just check for x sar 1
                    // ((x >> 1) & 7fff_ffff) | (... & 8000_0000)
                    op.if_arithmetic_or()
                        .and_either(|x| x.if_arithmetic_and_const(0x7fff_ffff))
                        .and_then(|x| x.0.if_arithmetic_rsh_const(1))
                        .is_some()
                }
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            // Arg 1 = unit id (Mem16[arg1] + 18)
                            // Arg 2 = x ((location.left + location.right) sdiv 2)
                            // Arg 3 = y ((location.top + location.bottom) sdiv 2)
                            let ok = Some(())
                                .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                                .and_then(|x| x.if_mem16()?.if_arithmetic_add_const(0x18))
                                .filter(|&x| x == self.arg_cache.on_entry(0))
                                .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                                .filter(|&x| is_sdiv_2(x))
                                .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                                .filter(|&x| is_sdiv_2(x))
                                .is_some();
                            if ok {
                                self.inline_depth = 0;
                                *ctrl.user_state() = GiveAiState::SearchingRaceCheck;
                                ctrl.analyze_with_current_state(self, dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                    _ => (),
                }
            }
            GiveAiState::SearchingRaceCheck => {
                match *op {
                    Operation::Call(dest) if self.inline_depth == 0 => {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inline_depth = 1;
                            self.stop_on_first_branch = true;
                            ctrl.inline(self, dest);
                            self.stop_on_first_branch = false;
                            self.inline_depth = 0;
                        }
                    }
                    Operation::Jump { condition, .. } => {
                        let condition = ctrl.resolve(condition);
                        // Mem8[units_dat_group_flags + unit.id] & flag == 0
                        let ok = crate::if_arithmetic_eq_neq(condition)
                            .and_then(|x| x.0.if_arithmetic_and())
                            .filter(|x| x.1.if_constant().is_some())
                            .and_then(|x| x.0.if_mem8())
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either_other(|x| {
                                x.if_constant()
                                    .filter(|&c| c == self.units_dat_group_flags.as_u64())
                            })
                            .is_some();
                        if ok {
                            self.stop_on_first_branch = false;
                            *ctrl.user_state() = GiveAiState::RaceCheckSeen;
                        }
                        if self.stop_on_first_branch {
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
            GiveAiState::RaceCheckSeen => {
                match *op {
                    Operation::Call(dest) if self.inline_depth == 0 => {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.is_some() {
                                self.result = Some(dest);
                                ctrl.end_analysis();
                            }
                            self.inline_depth = 0;
                        }
                    }
                    Operation::Jump { condition, .. } if self.inline_depth == 1 => {
                        // Recognize give_ai from it checking units_dat_ai_flags & 0x2
                        let condition = ctrl.resolve(condition);
                        let ok = crate::if_arithmetic_eq_neq(condition)
                            .and_then(|x| x.0.if_arithmetic_and_const(0x2))
                            .and_then(|x| x.if_mem8())
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either_other(|x| {
                                x.if_constant()
                                    .filter(|&c| c == self.units_dat_ai_flags.as_u64())
                            })
                            .is_some();
                        if ok {
                            // Caller fixes this
                            self.result = Some(E::VirtualAddress::from_u64(0));
                            ctrl.end_analysis();
                        }
                    }
                    _ => (),
                }
            }
            GiveAiState::Stop => {
                ctrl.end_branch();
            }
        }
    }
}

pub(crate) fn ai_prepare_moving_to<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_move: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // Check for order_move, state 0, target 0
    // It calls change_move_target_pos(this, x, y), which does
    // if (this.ai != null) {
    //   ai_prepare_moving_to(this, x, y);
    // }
    let arg_cache = &analysis.arg_cache;
    let mut exec_state = E::initial_state(ctx, binary);
    let order_state = ctx.mem8(
        ctx.add_const(
            ctx.register(1),
            0x4e,
        ),
    );
    let target = ctx.mem32(
        ctx.add_const(
            ctx.register(1),
            0x5c,
        ),
    );
    exec_state.move_to(&DestOperand::from_oper(order_state), ctx.const_0());
    exec_state.move_to(&DestOperand::from_oper(target), ctx.const_0());
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, order_move, exec_state, Default::default());
    let mut analyzer = AiPrepareMovingToAnalyzer {
        result: None,
        arg_cache,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AiPrepareMovingToAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for AiPrepareMovingToAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Jump { condition, to } => {
                if self.inline_depth == 255 {
                    ctrl.end_branch();
                    return;
                }
                // Check for this.ai == null or this.ai != null
                let condition = ctrl.resolve(condition);
                let jump_on_null = crate::if_arithmetic_eq_neq(condition)
                    .and_then(|x| {
                        Some((x.0, x.1))
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 0))?
                            .if_mem32()?
                            .if_arithmetic_add_const(0x134)?
                            .if_register()
                            .filter(|r| r.0 == 1)?;
                        Some(x.2)
                    });
                let jump_on_null = match jump_on_null {
                    Some(s) => s,
                    None => return,
                };
                let ai_nonzero_branch = match jump_on_null {
                    true => ctrl.current_instruction_end(),
                    false => match to.if_constant() {
                        Some(s) => E::VirtualAddress::from_u64(s),
                        None => return,
                    },
                };
                let old_inline_depth = self.inline_depth;
                self.inline_depth = 255;
                let exec = ctrl.exec_state().clone();
                let binary = ctrl.binary();
                let mut analysis = FuncAnalysis::custom_state(
                    binary,
                    ctx,
                    ai_nonzero_branch,
                    exec,
                    Default::default(),
                );
                analysis.analyze(self);
                self.inline_depth = old_inline_depth;
                ctrl.end_analysis();
            }
            Operation::Call(dest) if self.inline_depth < 3 || self.inline_depth == 255 => {
                // Inline to f(this, this.order_target.x, this.order_target.y)
                let ecx = ctrl.resolve(ctx.register(1));
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                if ecx != ctx.register(1) {
                    return;
                }
                let ok = unwrap_sext(arg1).if_mem16()
                    .and_then(|x| x.if_arithmetic_add_const(0x58))
                    .filter(|&x| x == ecx)
                    .is_some();
                if !ok {
                    return;
                }
                let ok = unwrap_sext(arg2).if_mem16()
                    .and_then(|x| x.if_arithmetic_add_const(0x5a))
                    .filter(|&x| x == ecx)
                    .is_some();
                if !ok {
                    return;
                }
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.inline_depth == 255 {
                        // First matching call on branch where this.ai != null
                        // is ai_prepare_moving_to
                        self.result = Some(dest);
                        ctrl.end_analysis();
                        return;
                    } else {
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                        self.inline_depth = self.inline_depth.saturating_sub(1);
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn ai_transport_reachability_cached_region<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    prepare_moving: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;

    let mut analysis = FuncAnalysis::new(binary, ctx, prepare_moving);
    let mut analyzer = TransportReachabilityAnalyzer {
        result: None,
        arg_cache,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct TransportReachabilityAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    TransportReachabilityAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                // Check for unit_region == Mem32[array + player * 4]
                // (Or maybe it's comparing dest_region?)
                let result = condition.if_arithmetic_eq()
                    .and_either(|x| {
                        x.if_mem32()
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either_other(|x| {
                                x.if_arithmetic_mul_const(4)?
                                    .if_mem8()?
                                    .if_arithmetic_add_const(0x4c)?
                                    .if_register()
                                    .filter(|r| r.0 == 1)
                            })
                    })
                    .map(|x| x.0);
                if single_result_assign(result, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            Operation::Call(dest) if self.inline_depth < 3 => {
                // Inline to f(this, this.order_target.x, this.order_target.y)
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                let mut do_inline = false;
                if self.inline_depth == 0 {
                    // Inline to cdecl f(this, arg1, arg2) at depth 0
                    // ("ai_are_on_connected_regions")
                    do_inline = arg1 == ctx.register(1) &&
                        arg2 == self.arg_cache.on_entry(0) &&
                        arg3 == self.arg_cache.on_entry(1);
                }
                if !do_inline {
                    // Also inline to f(this.player, unit_region, dest_region)
                    // ("ai_region_reachable_without_transport")
                    // Only checking for player now
                    do_inline = arg1.if_mem8()
                        .and_then(|x| x.if_arithmetic_add_const(0x4c))
                        .and_then(|x| x.if_register())
                        .filter(|r| r.0 == 1)
                        .is_some();
                }
                if do_inline {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                        self.inline_depth = self.inline_depth.saturating_sub(1);
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn train_military<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    spend_money: E::VirtualAddress,
    game: Operand<'e>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // ai_spend_money calls ai_train_military after checking game_second >= 10
    let exec_state = E::initial_state(ctx, binary);
    let state = TrainMilitaryState {
        seconds_checked: false,
    };
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, spend_money, exec_state, state);
    let mut analyzer = TrainMilitaryAnalyzer::<E> {
        result: None,
        game,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct TrainMilitaryAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    game: Operand<'e>,
}

#[derive(Copy, Clone)]
struct TrainMilitaryState {
    seconds_checked: bool,
}

impl analysis::AnalysisState for TrainMilitaryState {
    fn merge(&mut self, new: Self) {
        self.seconds_checked = new.seconds_checked && self.seconds_checked;
    }
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for TrainMilitaryAnalyzer<'e, E> {
    type State = TrainMilitaryState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                if ctrl.user_state().seconds_checked {
                    ctrl.end_analysis();
                }
                let condition = ctrl.resolve(condition);
                let ok = condition.if_arithmetic_gt()
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0xa))
                    .filter(|&x| is_game_seconds(self.game, x))
                    .is_some();
                if ok {
                    // Skip the jump (TODO: Should ideally also be able to handle
                    // the case where we only want to follow the jump)
                    ctrl.skip_operation();
                    ctrl.user_state().seconds_checked = true;
                }
            }
            Operation::Call(dest) if ctrl.user_state().seconds_checked => {
                let result = ctrl.resolve_va(dest);
                if single_result_assign(result, &mut self.result) {
                    ctrl.end_analysis();
                } else {
                    ctrl.end_branch();
                }
            }
            _ => (),
        }
    }
}

fn is_game_seconds<'e>(game: Operand<'e>, operand: Operand<'e>) -> bool {
    operand.if_mem32()
        .and_then(|x| x.if_arithmetic_add_const(0xe608))
        .filter(|&x| x == game)
        .is_some()
}

pub(crate) fn add_military_to_region<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    train_military: E::VirtualAddress,
    ai_regions: Operand<'e>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;

    // Check for call of add_military_to_region(ai_regions[arg1] + 1, unit_id, priority)
    // Arg1 AiRegion is only one that's easy to check
    // While there's technically one function in middle of train_military
    // and add_military_to_region, it seems to always be inlined
    // (train_attack_force)
    let mut analysis = FuncAnalysis::new(binary, ctx, train_military);
    let mut analyzer = AddMilitaryAnalyzer::<E> {
        result: None,
        ai_regions,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AddMilitaryAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    ai_regions: Operand<'e>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for AddMilitaryAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let is_region1 = arg1.if_arithmetic_add_const(0x34)
                    .and_then(|x| ctrl.if_mem_word(x))
                    .and_then(|x| x.if_arithmetic_add())
                    .and_either_other(|x| Some(()).filter(|()| x == self.ai_regions))
                    .and_then(|x| x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()))
                    .filter(|&x| x == self.arg_cache.on_entry(0))
                    .is_some();
                if !is_region1 {
                    return;
                }
                let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                if arg2.if_mem32().is_none() {
                    return;
                }
                let result = ctrl.resolve_va(dest);
                if single_result_assign(result, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn ai_spell_cast<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_guard: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    // Order 0xa0 (Guard) immediately calls ai_spell_cast

    struct Analyzer<'exec, 'b, E: ExecutionState<'exec>> {
        result: Option<E::VirtualAddress>,
        args: &'b ArgCache<'exec, E>,
    }
    impl<'exec, 'b, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for Analyzer<'exec, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let arg1 = ctrl.resolve(self.args.on_call(0));
                        let arg2 = ctrl.resolve(self.args.on_call(1));
                        let this = ctrl.ctx().register(1);
                        let args_ok = arg1 == this &&
                            arg2.if_constant() == Some(0);
                        if args_ok {
                            self.result = Some(E::VirtualAddress::from_u64(dest));
                        }
                    }
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer {
        result: None,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, order_guard);
    analysis.analyze(&mut analyzer);
    analyzer.result
}
