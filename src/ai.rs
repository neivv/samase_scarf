use arrayvec::ArrayVec;
use scarf::{
    DestOperand, Operand, Operation, MemAccessSize, OperandCtx, OperandType, BinaryFile,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState};

use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

use crate::{
    ArgCache, OptionExt, OperandExt, single_result_assign, Analysis, find_functions_using_global,
    entry_of_until, EntryOf, find_callers, DatType,
};

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

pub fn ai_update_attack_target<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    // Order 0xa3 (Computer return) immediately calls ai_update_attack_target
    let order_computer_return = crate::step_order::find_order_function(analysis, 0xa3)?;

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

pub fn aiscript_hook<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<AiScriptHook<'e, E::VirtualAddress>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let switch_tables = analysis.switch_tables();
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
        find_functions_using_global(analysis, switch_table.address)
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
    let simplified_70 = ctx.transform(condition, |x| match x.if_mem8().is_some() {
        true => Some(ctx.constant(0x70)),
        false => None,
    });
    let const_70 = match simplified_70.if_constant() {
        Some(x) => x,
        _ => return None,
    };
    let simplified_71 = ctx.transform(condition, |x| match x.if_mem8().is_some() {
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
    first_op_jumps: ArrayVec<[E::VirtualAddress; 4]>,
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

pub fn first_ai_script<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let funcs = &analysis.functions();
    let aiscript_hook = analysis.aiscript_hook();
    let aiscript_hook = (*aiscript_hook).as_ref()?;
    let hook_start = aiscript_hook.op_limit_hook_begin;

    let result = entry_of_until(binary, &funcs, hook_start, |entry| {
        let mut result = None;
        let callers = find_callers(analysis, entry);
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

pub fn first_guard_ai<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    // There's a function referring build times and looping through all guard ais,
    // guard ais are the first memaccess
    let funcs = &analysis.functions();
    let build_time_refs = {
        let units_dat = analysis.dat_virtual_address(DatType::Units);
        units_dat.and_then(|(dat, dat_table_size)| {
            binary.read_address(dat + 0x2a * dat_table_size).ok().map(|times| {
                find_functions_using_global(analysis, times)
                    .into_iter()
                    .map(|global_ref| global_ref.use_address)
                    .collect::<Vec<_>>()
            })
        }).unwrap_or_else(|| Vec::new())
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

pub fn player_ai_towns<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let aiscript = analysis.aiscript_hook();
    let aiscript = (*aiscript).as_ref()?;

    let addr_size = E::VirtualAddress::SIZE;
    let start_town = binary.read_address(aiscript.switch_table + 0x3 * addr_size).ok()?;

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

pub fn player_ai<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let aiscript = analysis.aiscript_hook();
    let aiscript_hook = (*aiscript).as_ref()?;

    let addr_size = E::VirtualAddress::SIZE;
    let farms_notiming = binary.read_address(aiscript_hook.switch_table + 0x32 * addr_size).ok()?;

    // Set script->player to 0
    let mut state = E::initial_state(ctx, binary);
    let player_offset = if addr_size == 4 { 0x10 } else { 0x18 };
    let player = ctx.mem32(ctx.add(
        aiscript_hook.script_operand_at_switch,
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

pub fn attack_prepare<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let aiscript = analysis.aiscript_hook();
    let aiscript_hook = (*aiscript).as_ref()?;

    let addr_size = E::VirtualAddress::SIZE;
    let attack_prepare = binary.read_address(aiscript_hook.switch_table + 0xd * addr_size).ok()?;

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
