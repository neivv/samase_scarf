use std::rc::Rc;

use arrayvec::ArrayVec;
use scarf::{
    self, DestOperand, Operand, Operation, VirtualAddress, MemAccessSize, OperandContext,
    OperandType, BinaryFile,
};
use scarf::analysis::{self, Control};
use scarf::exec_state::{InternMap, ExecutionState};

use scarf::ExecutionStateX86;
use scarf::exec_state::VirtualAddress as VirtualAddressTrait;
type FuncAnalysis<'a, T> = scarf::analysis::FuncAnalysis<'a, ExecutionStateX86<'a>, T>;

use crate::{
    ArgCache, Error, OptionExt, entry_of_until_call, single_result_assign, Analysis,
    find_functions_using_global,
};

pub fn check_step_ai_scripts(
    binary: &BinaryFile<VirtualAddress>,
    funcs: &[VirtualAddress],
    ctx: &OperandContext,
    call_pos: VirtualAddress,
    errors: &mut Vec<Error>,
) -> Option<Rc<Operand>> {
    let mut first_branch = false;
    entry_of_until_call(binary, funcs, call_pos, ctx, errors, |reset, op, state, _addr, i| {
        if reset {
            first_branch = true;
        }
        if first_branch {
            match *op {
                Operation::Jump { ref condition, .. } => {
                    first_branch = false;
                    let cond = state.resolve(condition, i);
                    let result = cond.if_arithmetic_eq()
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
                    if let Some(res) = result {
                        return Some(res);
                    }
                }
                _ => (),
            }
        }
        None
    }).into_option()
}

pub fn ai_towns_check(
    val: &Rc<Operand>,
    state: &mut ExecutionStateX86,
    i: &mut InternMap,
    ctx: &OperandContext
) -> Option<Rc<Operand>> {
    use scarf::operand_helpers::*;

    // aiscript_start_town accesses player's first ai town
    if let Some(mem) = val.if_memory() {
        let resolved = state.resolve(&mem.address, i);
        resolved.if_arithmetic_add()
            .and_then(|(l, r)| Operand::either(l, r, |x| x.if_arithmetic_mul()))
            .and_then(|((l, r), other)| {
                Operand::either(l, r, |x| x.if_constant())
                    .filter(|&(c, _)| c == 8)
                    .map(|_| Operand::simplified(operand_sub(other.clone(), ctx.const_4())))
            })
    } else {
        None
    }
}

pub fn ai_towns_child_func(
    binary: &BinaryFile<VirtualAddress>,
    func: VirtualAddress,
    ctx: &OperandContext,
) -> Option<Rc<Operand>> {
    use scarf::operand_helpers::*;

    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    let mut result = None;
    let jump_count_marker = mem32(ctx.undefined_rc());
    'outer: while let Some(mut branch) = analysis.next_branch() {
        let mut operations = branch.operations();
        while let Some((op, state, _address, i)) = operations.next() {
            match *op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    let jumps_calls_done =
                        state.resolve(&jump_count_marker, i).if_constant().unwrap_or(0);
                    if jumps_calls_done > 4 {
                        break 'outer;
                    }
                    let dest = DestOperand::from_oper(&jump_count_marker);
                    let val = ctx.constant(jumps_calls_done + 1);
                    state.move_to(&dest, val, i);
                }
                Operation::Move(ref _dest, ref val, ref _cond) => {
                    let res = ai_towns_check(val, state, i, &ctx);
                    if single_result_assign(res, &mut result) {
                        break 'outer;
                    }
                }
                _ => (),
            }
        }
    }
    result
}

pub fn ai_update_attack_target<'a>(
    analysis: &mut Analysis<'a, ExecutionStateX86<'a>>,
) -> Option<VirtualAddress> {
    let ctx = analysis.ctx;
    // Order 0xa3 (Computer return) immediately calls ai_update_attack_target
    let order_computer_return = crate::step_order::find_order_function(analysis, ctx, 0xa3)?;

    struct Analyzer<'exec, 'b, E: ExecutionState<'exec>> {
        result: Option<E::VirtualAddress>,
        args: &'b ArgCache<'exec, E>,
    }
    impl<'exec, 'b, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for Analyzer<'exec, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let arg1 = ctrl.resolve(&self.args.on_call(0));
                        let arg2 = ctrl.resolve(&self.args.on_call(1));
                        let arg3 = ctrl.resolve(&self.args.on_call(2));
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
pub struct AiScriptHook<Va: VirtualAddressTrait> {
    pub op_limit_hook_begin: Va,
    pub op_limit_hook_end: Va,
    pub op_limit_ok: Va,
    pub op_limit_fail: Va,
    // Operand that the comparision should be done against.
    pub opcode_operand: Rc<Operand>,
    pub script_operand_at_switch: Rc<Operand>,
    pub switch_table: Va,
    pub switch_loop_address: Va,
    pub return_address: Va,
}

pub fn aiscript_hook<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<AiScriptHook<E::VirtualAddress>> {
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
        let mut analysis = analysis::FuncAnalysis::new(binary, &ctx, entry);
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
            let i = &mut analysis.interner;
            switch_state.unresolve(&script_operand_orig, i)
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
    aiscript_operand: Option<Rc<Operand>>,
    switch_state: Option<E>,
    branch_start: E::VirtualAddress,
    best_def_jump: Option<BestDefaultJump<E::VirtualAddress>>,
    op_default_jump: Option<OpDefaultJump<E::VirtualAddress>>,
}

struct OpDefaultJump<Va: VirtualAddressTrait> {
    address: Va,
    to: Va,
    jumps_to_default: bool,
    opcode: Rc<Operand>,
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
struct BestDefaultJump<Va: VirtualAddressTrait> {
    address: Va,
    to: Va,
    branch_start: Va,
    branch_end: Va,
    jumps_to_default: bool,
    opcode: Rc<Operand>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiscriptHookAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Jump { condition, to } => {
                let condition = match condition.if_constant() {
                    Some(_) => None,
                    None => Some(condition),
                };
                let to = ctrl.resolve(to);
                match (condition, &to.ty) {
                    // Check for switch jump
                    (None, &OperandType::Memory(ref mem)) => {
                        // Checking for arith since it could tecnically be a
                        // tail call to fnptr.
                        if let OperandType::Arithmetic(_) = mem.address.ty {
                            let (state, _) = ctrl.exec_state();
                            self.switch_state = Some(state.clone());
                        }
                    }
                    // Check for default case jump
                    (Some(cond), &OperandType::Constant(to)) => {
                        let resolved = ctrl.resolve(cond);
                        let ctx = ctrl.ctx();
                        let (state, interner) = ctrl.exec_state();
                        let jumps = is_aiscript_switch_jump(ctx, &resolved, state, interner);
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
            Operation::Move(dest, val, _cond) => {
                // Try to find script->pos += 1
                if self.aiscript_operand.is_none() {
                    if let DestOperand::Memory(ref mem) = dest {
                        let addr = ctrl.resolve(&mem.address);
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
    ctx: &'e OperandContext,
    condition: &Rc<Operand>,
    state: &mut E,
    interner: &mut InternMap,
) -> Option<(bool, Rc<Operand>)> {
    // The chances of there being another jump with different constresults when Mem8[x]
    // is replaced by 0x70 and 0x71 is low, so use that instead of trying to match all
    // gt/lt/ge/le variations
    let simplified_70 = ctx.transform(condition, |x| match x.ty {
        OperandType::Memory(ref mem) => {
            if mem.size == MemAccessSize::Mem8 {
                Some(ctx.constant(0x70))
            } else {
                None
            }
        }
        _ => None,
    });
    let const_70 = match simplified_70.if_constant() {
        Some(x) => x,
        _ => return None,
    };
    let simplified_71 = ctx.transform(condition, |x| match x.ty {
        OperandType::Memory(ref mem) => {
            if mem.size == MemAccessSize::Mem8 {
                Some(ctx.constant(0x71))
            } else {
                None
            }
        }
        _ => None,
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
        // Eww bad api
        state.unresolve(&Rc::new(opcode_mem.clone()), interner)
    }).map(|x| (gt_jump, x))
}

fn aiscript_find_switch_loop_and_end<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: &'e OperandContext,
    switch_table: E::VirtualAddress,
) -> Option<(E::VirtualAddress, E::VirtualAddress)> {
    let opcode_case = binary.read_u32(switch_table + 0xb * 4).ok()?;
    let second_opcode_case = binary.read_u32(switch_table + 0x2b * 4).ok()?;
    let wait_case = binary.read_u32(switch_table + 0x2 * 4).ok()?;
    let opcode_case = E::VirtualAddress::from_u64(opcode_case as u64);
    let mut analysis = analysis::FuncAnalysis::new(binary, ctx, opcode_case);
    let mut analyzer: AiscriptFindSwitchLoop<E> = AiscriptFindSwitchLoop {
        first_op_jumps: ArrayVec::new(),
        first_op: true,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    let second_opcode_case = E::VirtualAddress::from_u64(second_opcode_case as u64);
    let mut analysis = analysis::FuncAnalysis::new(binary, &ctx, second_opcode_case);
    analyzer.first_op = false;
    analysis.analyze(&mut analyzer);

    let wait_case = E::VirtualAddress::from_u64(wait_case as u64);
    let other = aiscript_find_switch_loop_end::<E>(binary, &ctx, wait_case);
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
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
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
    ctx: &'e OperandContext,
    wait_case: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let mut analysis = analysis::FuncAnalysis::new(binary, &ctx, wait_case);
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
    old_base: Option<Rc<Operand>>,
    result: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiscriptFindSwitchEnd<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        let ok = (self.pos_written && self.wait_written) ||
            (self.wait_written && self.not_inlined_op_read);
        if ok {
            self.result = Some(ctrl.address());
            ctrl.end_analysis();
        }
        match op {
            Operation::Call(..) => {
                if self.first_branch {
                    self.not_inlined_op_read = true;
                }
            }
            Operation::Move(dest, val, _) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem32 {
                        let addr = ctrl.resolve(&mem.address);
                        let c_write = addr.if_arithmetic_add()
                            .and_either(|x| x.if_constant());
                        if let Some((offset, base)) = c_write {
                            let old_ok =
                                self.old_base.as_ref().map(|x| x == base).unwrap_or(true);
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
