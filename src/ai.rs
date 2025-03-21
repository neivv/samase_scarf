use arrayvec::ArrayVec;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use scarf::{
    DestOperand, Operand, Operation, MemAccessSize, OperandCtx, BinaryFile, Rva,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState};

use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::analysis_state::{self, AnalysisState, AiTownState, GiveAiState, TrainMilitaryState};
use crate::call_tracker::{CallTracker};
use crate::hash_map::HashSet;
use crate::switch::CompleteSwitch;
use crate::util::{
    MemAccessExt, OptionExt, OperandExt, single_result_assign, ControlExt, bumpvec_with_capacity,
    is_global, ExecStateExt, seems_assertion_call,
};

pub(crate) fn ai_update_attack_target<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_computer_return: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    // Order 0xa3 (Computer return) immediately calls ai_update_attack_target

    struct Analyzer<'exec, E: ExecutionState<'exec>> {
        result: Option<E::VirtualAddress>,
    }
    impl<'exec, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for Analyzer<'exec, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ctx = ctrl.ctx();
                        let args_ok = ctrl.resolve_arg_thiscall_u8(0) == ctx.const_0() &&
                            ctrl.resolve_arg_thiscall_u8(1) == ctx.const_1() &&
                            ctrl.resolve_arg_thiscall_u8(2) == ctx.const_0();
                        if args_ok {
                            self.result = Some(dest);
                        }
                    }
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: None,
    };
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, order_computer_return);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct AiScriptHook<'e, Va: VirtualAddressTrait> {
    pub op_limit_hook_begin: Va,
    pub op_limit_hook_end: Va,
    pub op_limit_ok: Va,
    pub op_limit_fail: Va,
    // Operand that the comparision should be done against.
    pub opcode_operand: Operand<'e>,
    pub script_operand_at_switch: Operand<'e>,
    pub switch_table: Va,
    pub switch_base: Option<Va>,
    pub switch_loop_address: Va,
    pub return_address: Va,
}

fn aiscript_hook<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    entry: E::VirtualAddress,
    switch_jump_address: E::VirtualAddress,
    switch: &CompleteSwitch<'e>,
) -> Option<AiScriptHook<'e, E::VirtualAddress>> {
    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
    let mut analyzer: AiscriptHookAnalyzer<E> = AiscriptHookAnalyzer {
        aiscript_operand: None,
        switch_state: None,
        branch_start: entry,
        best_def_jump: None,
        op_default_jump: None,
        switch_jump_address,
    };
    analysis.analyze(&mut analyzer);

    let switch_table = E::VirtualAddress::from_u64(switch.switch_table());
    let switch_base = match switch.base() {
        0 => None,
        x => Some(E::VirtualAddress::from_u64(x)),
    };

    let tp = (analyzer.best_def_jump, analyzer.aiscript_operand, analyzer.switch_state);
    if let (Some(default_jump), Some(script_operand_orig), Some(switch_state)) = tp {
        let (op_limit_ok, op_limit_fail) = match default_jump.jumps_to_default {
            true => (default_jump.branch_end, default_jump.to),
            false => (default_jump.to, default_jump.branch_end),
        };
        switch_state.unresolve(script_operand_orig)
            .and_then(|at_switch| {
                aiscript_find_switch_loop_and_end::<E>(binary, ctx, switch)
                    .map(move |(switch_loop_address, return_address)| {
                        AiScriptHook {
                            op_limit_hook_begin: default_jump.branch_start,
                            op_limit_hook_end: default_jump.address,
                            op_limit_ok,
                            op_limit_fail,
                            opcode_operand: default_jump.opcode,
                            script_operand_at_switch: at_switch,
                            switch_table,
                            switch_base,
                            switch_loop_address,
                            return_address,
                        }
                    })
            })
    } else {
        None
    }
}

struct AiscriptHookAnalyzer<'e, E: ExecutionState<'e>> {
    aiscript_operand: Option<Operand<'e>>,
    switch_state: Option<E>,
    branch_start: E::VirtualAddress,
    best_def_jump: Option<BestDefaultJump<'e, E::VirtualAddress>>,
    op_default_jump: Option<OpDefaultJump<'e, E::VirtualAddress>>,
    switch_jump_address: E::VirtualAddress,
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
                let to = ctrl.resolve(to);
                if ctrl.address() == self.switch_jump_address {
                    let state = ctrl.exec_state();
                    self.switch_state = Some(state.clone());
                    return;
                }
                if let Some(to) = ctrl.resolve_va(to) {
                    let resolved = ctrl.resolve(condition);
                    let state = ctrl.exec_state();
                    let jumps = resolved.if_arithmetic_gt()
                        .and_then(|(l, r)| {
                            let (other, jumps) = if r.if_constant() == Some(0x70) {
                                (l, true)
                            } else if l.if_constant() == Some(0x71) {
                                (r, false)
                            } else {
                                return None;
                            };
                            other.if_mem8()?;
                            let unresolved = state.unresolve(other)?;
                            Some((jumps, unresolved))
                        });
                    if let Some((jumps_to_default, opcode)) = jumps {
                        self.op_default_jump = Some(OpDefaultJump {
                            address: ctrl.address(),
                            to,
                            jumps_to_default,
                            opcode,
                        });
                    }
                }
            }
            Operation::Move(ref dest, val) => {
                // Try to find script->pos += 1
                if self.aiscript_operand.is_none() {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == MemAccessSize::Mem32 {
                            let mem = ctrl.resolve_mem(mem);
                            let (base, offset) = mem.address();
                            let pos_offset = E::struct_layouts().ai_script_pos();
                            if offset == pos_offset {
                                let val = ctrl.resolve(val);
                                let val_refers_to_dest = val.iter_no_mem_addr().any(|x| {
                                    x.if_memory() == Some(&mem)
                                });
                                if val_refers_to_dest {
                                    self.aiscript_operand = Some(base);
                                }
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

fn aiscript_find_switch_loop_and_end<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    switch: &CompleteSwitch<'e>,
) -> Option<(E::VirtualAddress, E::VirtualAddress)> {
    let opcode_case = switch.branch::<E::VirtualAddress>(binary, ctx, 0xb)?;
    let second_opcode_case = switch.branch::<E::VirtualAddress>(binary, ctx, 0x2b)?;
    let wait_case = switch.branch::<E::VirtualAddress>(binary, ctx, 0x2)?;
    let mut analysis = FuncAnalysis::new(binary, ctx, opcode_case);
    let mut analyzer: AiscriptFindSwitchLoop<E> = AiscriptFindSwitchLoop {
        first_op_jumps: ArrayVec::new(),
        first_op: true,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    let mut analysis = FuncAnalysis::new(binary, ctx, second_opcode_case);
    analyzer.first_op = false;
    analysis.analyze(&mut analyzer);

    let other = aiscript_find_switch_loop_end::<E>(binary, ctx, wait_case);
    Some((analyzer.result?, other?))
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
                    let to = ctrl.resolve_va(to);
                    if let Some(dest) = to {
                        if self.first_op {
                            self.first_op_jumps.push(dest);
                            if self.first_op_jumps.is_full() {
                                ctrl.end_analysis();
                            }
                        } else {
                            if self.first_op_jumps.iter().any(|&x| x == dest) {
                                self.result = Some(dest);
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
            Operation::Move(ref dest, val) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem32 {
                        let dest = ctrl.resolve_mem(mem);
                        let (base, offset) = dest.address();
                        let old_ok = self.old_base.map(|x| x == base).unwrap_or(true);
                        if old_ok {
                            let pos_offset = E::struct_layouts().ai_script_pos();
                            let wait_offset = E::struct_layouts().ai_script_wait();
                            if offset == pos_offset {
                                let val = ctrl.resolve(val);
                                let ok = Operand::and_masked(val).0
                                    .if_arithmetic_add_const(2)
                                    .is_some();
                                if ok {
                                    self.pos_written = true;
                                    self.old_base = Some(base);
                                }
                            } else if offset == wait_offset {
                                let val = ctrl.resolve(val);
                                let ok = val.if_mem16()
                                    .and_then(|x| x.address().0.if_arithmetic_add())
                                    .is_some();
                                if self.not_inlined_op_read || ok {
                                    self.wait_written = true;
                                    self.old_base = Some(base);
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
            Operation::Move(_, val) => {
                let val = ctrl.resolve(val);
                let ctx = ctrl.ctx();
                let result = ctrl.if_mem_word(val)
                    .and_then(|mem| {
                        mem.if_add_either_other(ctx, |x| {
                            x.if_arithmetic_mul_const(u64::from(2 * E::VirtualAddress::SIZE))
                        })
                    })
                    .map(|val| ctx.sub_const(val, E::VirtualAddress::SIZE.into()));
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
    let bump = &analysis.bump;

    let start_town = crate::switch::simple_switch_branch(binary, aiscript_switch_table, 0x3)?;

    let state = AiTownState {
        jump_count: 0,
    };
    let exec_state = E::initial_state(ctx, binary);
    let state = AnalysisState::new(bump, analysis_state::StateEnum::AiTown(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, start_town, exec_state, state);
    let mut analyzer = AiTownAnalyzer {
        result: None,
        inlining: false,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AiTownAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e (), &'acx ())>,
}

impl<'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    AiTownAnalyzer<'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let mut jump_check = false;
        match *op {
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inlining = true;
                        let state = ctrl.user_state().get::<AiTownState>();
                        let old_jump_count = state.jump_count;
                        state.jump_count = 0;
                        ctrl.analyze_with_current_state(self, dest);
                        let state = ctrl.user_state().get::<AiTownState>();
                        state.jump_count = old_jump_count;
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    jump_check = true;
                }
            }
            Operation::Move(_, val) => {
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
            let state = ctrl.user_state().get::<AiTownState>();
            state.jump_count += 1;
            if self.inlining && state.jump_count > 5 {
                ctrl.end_analysis();
            } else if !self.inlining && state.jump_count > 2 {
                ctrl.end_branch();
            }
        }
    }
}

impl<'acx, 'e: 'acx, E: ExecutionState<'e>> AiTownAnalyzer<'acx, 'e, E> {
    fn ai_towns_check(
        &self,
        val: Operand<'e>,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> Option<Operand<'e>> {
        let ctx = ctrl.ctx();
        let val = ctrl.resolve(val);
        // aiscript_start_town accesses player's first ai town
        if let Some(mem) = val.if_memory() {
            mem.if_add_either_other(ctx, |x| {
                    x.if_arithmetic_mul_const(u64::from(2 * E::VirtualAddress::SIZE))
                })
                .map(|other| ctx.sub_const(other, E::VirtualAddress::SIZE.into()))
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

    let farms_notiming =
        crate::switch::simple_switch_branch(binary, aiscript.switch_table, 0x32)?;

    // Set script->player to 0
    let mut state = E::initial_state(ctx, binary);
    let player_offset = E::struct_layouts().ai_script_player();
    let player = ctx.mem32(
        aiscript.script_operand_at_switch,
        player_offset,
    );
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
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(ref dest, val) => {
                if let DestOperand::Memory(mem) = dest {
                    let dest = ctrl.resolve_mem(mem);
                    let val = ctrl.resolve(val);
                    let ctx = ctrl.ctx();
                    let result = val.if_arithmetic_or()
                        .and_either_other(|x| x.if_memory().filter(|&mem| mem == &dest))
                        .and_then(|y| y.if_constant())
                        .filter(|&c| c == 0x10)
                        .map(|_| {
                            ctx.mem_sub_const_op(&dest, E::struct_layouts().player_ai_flags())
                        });
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

#[derive(Copy, Clone)]
pub(crate) struct AiscriptSwitchAnalysis<Va: VirtualAddressTrait> {
    pub ai_attack_prepare: Option<Va>,
    pub ai_attack_clear: Option<Va>,
}

pub(crate) fn aiscript_switch_analysis<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_switch_table: E::VirtualAddress,
) -> AiscriptSwitchAnalysis<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = AiscriptSwitchAnalysis {
        ai_attack_prepare: None,
        ai_attack_clear: None,
    };

    let mut analyzer = AttackPrepareAnalyzer::<E> {
        result: &mut result,
        state: AiscriptSwitchState::AttackPrepare,
    };

    let attack_prepare =
        match crate::switch::simple_switch_branch(binary, aiscript_switch_table, 0xd)
    {
        Some(s) => s,
        None => return result,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, attack_prepare);
    analysis.analyze(&mut analyzer);

    analyzer.state = AiscriptSwitchState::AttackClear;
    let attack_clear = match
        crate::switch::simple_switch_branch(binary, aiscript_switch_table, 0xb)
    {
        Some(s) => s,
        None => return result,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, attack_clear);
    analysis.analyze(&mut analyzer);

    result
}

struct AttackPrepareAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut AiscriptSwitchAnalysis<E::VirtualAddress>,
    state: AiscriptSwitchState,
}

#[derive(Eq, PartialEq)]
enum AiscriptSwitchState {
    AttackPrepare,
    AttackClear,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AttackPrepareAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                let player_off = E::struct_layouts().ai_script_player();
                if self.state == AiscriptSwitchState::AttackPrepare {
                    let pos_off = E::struct_layouts().ai_script_center();
                    let ok = Some(())
                        .map(|_| ctrl.resolve_arg(0))
                        .and_then(|x| x.if_mem32_offset(player_off))
                        .map(|_| ctrl.resolve_arg(1))
                        .and_then(|x| x.if_mem32_offset(pos_off))
                        .map(|_| ctrl.resolve_arg(2))
                        .and_then(|x| x.if_mem32_offset(pos_off + 4))
                        .map(|_| ctrl.resolve_arg_u32(3))
                        .filter(|&x| x == ctx.const_1())
                        .map(|_| ctrl.resolve_arg_u32(4))
                        .filter(|&x| x == ctx.const_0())
                        .is_some();
                    if ok {
                        self.result.ai_attack_prepare = ctrl.resolve_va(dest);
                    }
                } else {
                    let ok = Some(())
                        .map(|_| ctrl.resolve_arg(0))
                        .and_then(|x| x.if_mem32_offset(player_off))
                        .map(|_| ctrl.resolve_arg_u32(1))
                        .filter(|&x| x == ctx.const_1())
                        .is_some();
                    if ok {
                        self.result.ai_attack_clear = ctrl.resolve_va(dest);
                    }
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
pub(crate) struct AiStepFrameFuncs<'e, Va: VirtualAddressTrait> {
    pub ai_step_region: Option<Va>,
    pub ai_spend_money: Option<Va>,
    pub step_ai_scripts: Option<Va>,
    pub step_ai_script: Option<Va>,
    pub ai_target_expansion: Option<Va>,
    pub players: Option<Operand<'e>>,
    pub first_ai_script: Option<Operand<'e>>,
    pub hook: Option<AiScriptHook<'e, Va>>,
    pub step_ai_regions_region: Option<Operand<'e>>,
    pub step_ai_regions_player: Option<Operand<'e>>,
    pub resource_areas: Option<Operand<'e>>,
    pub ai_target_ignore_reset_counter: Option<Operand<'e>>,
    pub ai_target_ignore_reset_counter2: Option<Operand<'e>>,
    pub ai_target_ignore_request_reset: Option<Operand<'e>>,
    pub ai_military_update_counter: Option<Operand<'e>>,
}

pub(crate) fn step_frame_funcs<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_objects: E::VirtualAddress,
    game: Operand<'e>,
) -> AiStepFrameFuncs<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;

    let mut result = AiStepFrameFuncs {
        ai_step_region: None,
        ai_spend_money: None,
        step_ai_scripts: None,
        step_ai_script: None,
        ai_target_expansion: None,
        first_ai_script: None,
        players: None,
        hook: None,
        step_ai_regions_region: None,
        step_ai_regions_player: None,
        resource_areas: None,
        ai_target_ignore_reset_counter: None,
        ai_target_ignore_reset_counter2: None,
        ai_target_ignore_request_reset: None,
        ai_military_update_counter: None,
    };

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    let mut analyzer = StepRegionAnalyzer {
        result: &mut result,
        arg_cache,
        inline_depth: 0,
        step_ai_regions_depth: 0,
        checked_functions: HashSet::with_capacity_and_hasher(0x40, Default::default()),
        binary,
        game,
        state: StepAiState::StepAiScript,
        game_seconds_checked: false,
        entry: step_objects,
        target_reset_counter2_candidates: bumpvec_with_capacity(4, bump),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepAiState {
    StepAiScript,
    StepRegions,
    /// ai_target_expansion(a1 = step_ai_regions_player) in same loop as ai_step_region.
    /// Find by jump on player_ai[step_ai_regions_player].target_expansion_attacks.
    /// Inline twice.
    TargetExpansion,
    ResourceAreas,
    TargetResetCounter,
    TargetResetCounter2,
    SpendMoney,
}

struct StepRegionAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut AiStepFrameFuncs<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    /// Valid after StepRegions
    step_ai_regions_depth: u8,
    checked_functions: HashSet<Rva>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    game: Operand<'e>,
    game_seconds_checked: bool,
    state: StepAiState,
    entry: E::VirtualAddress,
    target_reset_counter2_candidates: BumpVec<'acx, Operand<'e>>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepRegionAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) if self.state != StepAiState::SpendMoney => {
                let limit = match self.state {
                    StepAiState::StepAiScript => 3,
                    StepAiState::TargetExpansion => 4,
                    StepAiState::StepRegions => 3,
                    StepAiState::ResourceAreas => 3,
                    StepAiState::TargetResetCounter => 3,
                    StepAiState::TargetResetCounter2 => 0,
                    StepAiState::SpendMoney => 0,
                };
                if self.inline_depth < limit {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let relative = dest.as_u64().checked_sub(self.binary.base.as_u64());
                        if let Some(relative) = relative {
                            let rva = Rva(relative as u32);
                            if self.checked_functions.insert(rva) {
                                if self.state == StepAiState::StepAiScript {
                                    self.inline_depth += 1;
                                    let entry = self.entry;
                                    self.entry = dest;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.entry = entry;
                                    self.inline_depth -= 1;
                                    if self.result.first_ai_script.is_some() {
                                        if self.inline_depth > 1 &&
                                            self.result.step_ai_scripts.is_none()
                                        {
                                            self.result.step_ai_scripts = Some(entry);
                                        }
                                        if self.inline_depth > 1 || self.inline_depth == 0 {
                                            ctrl.end_analysis();
                                        }
                                    }
                                } else if self.state == StepAiState::StepRegions {
                                    // Step region is recognized from its arg1, so
                                    // create separate analysis instead of using current state.
                                    self.inline_depth += 1;
                                    let mut analysis = FuncAnalysis::new(self.binary, ctx, dest);
                                    analysis.analyze(self);
                                    self.inline_depth -= 1;
                                    if let Some(result) = self.result.ai_step_region {
                                        if self.state == StepAiState::TargetExpansion {
                                            if self.inline_depth > 1 {
                                                ctrl.end_analysis();
                                            } else {
                                                self.state = StepAiState::ResourceAreas;
                                            }
                                        }
                                        if result.as_u64() == 0 {
                                            self.step_ai_regions_depth = self.inline_depth;
                                            let arg1 = ctrl.resolve_arg(0);
                                            let arg2 = ctrl.resolve_arg(1);
                                            self.result.ai_step_region = Some(dest);
                                            self.result.step_ai_regions_player = Some(arg1);
                                            self.result.step_ai_regions_region = Some(arg2);
                                            self.state = StepAiState::TargetExpansion;
                                        }
                                    }
                                } else if self.state == StepAiState::TargetExpansion {
                                    let a1 = ctrl.resolve_arg(0);
                                    if Some(a1) == self.result.step_ai_regions_player {
                                        self.inline_depth += 1;
                                        ctrl.analyze_with_current_state(self, dest);
                                        self.inline_depth -= 1;
                                        if self.inline_depth > self.step_ai_regions_depth {
                                            ctrl.end_analysis();
                                            return;
                                        }
                                        if let Some(result) = self.result.ai_target_expansion {
                                            if result.as_u64() == 0 {
                                                self.result.ai_target_expansion = Some(dest);
                                            }
                                            // ai_spend_money is expected to be at inline depth 1
                                            if self.inline_depth > 1 {
                                                ctrl.end_analysis();
                                            } else {
                                                self.state = StepAiState::ResourceAreas;
                                            }
                                        }
                                    }
                                } else {
                                    self.inline_depth += 1;
                                    let mut analysis = FuncAnalysis::new(self.binary, ctx, dest);
                                    analysis.analyze(self);
                                    self.inline_depth -= 1;
                                }
                            }
                        }
                    }
                }
            }
            Operation::Call(dest) if self.state == StepAiState::SpendMoney => {
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
            Operation::Jump { to, condition } if self.state == StepAiState::StepAiScript => {
                let to = ctrl.resolve(to);
                if let Some(dest) = to.if_constant() {
                    let condition = ctrl.resolve(condition);
                    // Assume jumps checking Mem8[script.flags] & 1 (aiscript/bwscript)
                    // always be taken to avoid making switch index undefined
                    // (Doesn't matter whether it is aiscript or bwscript, just not both)
                    let is_bwscript_check = condition.if_arithmetic_eq_neq_zero(ctx)
                        .map(|x| x.0)
                        .unwrap_or(condition)
                        .if_arithmetic_and_const(1)
                        .and_then(|op| op.if_mem8_offset(E::struct_layouts().ai_script_flags()))
                        .is_some();
                    if is_bwscript_check {
                        ctrl.end_branch();
                        ctrl.add_branch_with_current_state(E::VirtualAddress::from_u64(dest));
                    }
                } else if let Some(switch) = CompleteSwitch::new(to, ctx, ctrl.exec_state()) {
                    let ok = Some(()).and_then(|()| {
                        let index = switch.index_operand(ctx)?;
                        let first_ai_script = index.if_mem8()?
                            .if_add_either(ctx, |x| {
                                let pos_off = E::struct_layouts().ai_script_pos();
                                x.if_memory()?.if_offset(pos_off)
                            })?.0;
                        Some(first_ai_script)
                    });
                    if let Some(first_ai_script) = ok {
                        self.result.first_ai_script = Some(first_ai_script);
                        self.result.step_ai_script = Some(self.entry);
                        self.state = StepAiState::StepRegions;
                        self.result.hook = aiscript_hook::<E>(
                            ctx,
                            ctrl.binary(),
                            self.entry,
                            ctrl.address(),
                            &switch,
                        );
                        if self.inline_depth > 1 {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { condition, .. } if self.state == StepAiState::StepRegions => {
                if self.result.players.is_none() {
                    // Check for players[global].type == 1
                    let condition = ctrl.resolve(condition);
                    let players = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1 == ctx.const_1())
                        .and_then(|x| {
                            x.0.if_mem8_offset(8)?.if_arithmetic_add()
                        })
                        .and_either_other(|x| x.if_arithmetic_mul_const(0x24));
                    single_result_assign(players, &mut self.result.players);
                }
            }
            Operation::Jump { condition, .. } if self.state == StepAiState::TargetExpansion => {
                if self.inline_depth > self.step_ai_regions_depth {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                        .and_then(|x| {
                            let mem = x.0.if_mem8()?;
                            let base = mem.address().0;
                            let pair = base.if_arithmetic_add()
                                .unwrap_or((base, ctx.const_0()));
                            let player_ai_size = E::struct_layouts().player_ai_size();
                            let (x, _) = Operand::either(
                                pair.0,
                                pair.1,
                                |x| x.if_arithmetic_mul_const(player_ai_size),
                            )?;
                            (Some(x) == self.result.step_ai_regions_player).then_some(())
                        })
                        .is_some();
                    if ok {
                        self.result.ai_target_expansion = Some(E::VirtualAddress::from_u64(0));
                    }
                    ctrl.end_analysis();
                }
            }
            Operation::Jump { condition, to } if self.state == StepAiState::TargetResetCounter2 =>
            {
                let condition = ctrl.resolve(condition);
                // The code should do `counter2 == 0 || request != 0`
                // Always continue at != 0 address, for the first jump,
                // and if the `global = 6` is found without the global being in candidates,
                // it just means that `request != 0` was checked first.
                if let Some((val, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                    if is_global(val) && !self.target_reset_counter2_candidates.contains(&val) {
                        self.target_reset_counter2_candidates.push(val);
                        ctrl.continue_at_neq_address(eq, to);
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val)
                if self.state == StepAiState::SpendMoney && mem.size == MemAccessSize::Mem32 =>
            {
                // Search for ai_spend_money by checking for a global store
                // global = game.seconds < 4500 ? 7 : 0x25
                let val = ctrl.resolve(val);
                if Operand::and_masked(val).0.if_custom() == Some(0) || val.iter_no_mem_addr()
                    .any(|x| {
                        // Checking for 4500 > Mem32[game.seconds]
                        x.if_arithmetic_gt()
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 4500))
                            .filter(|&x| is_game_seconds(self.game, x))
                            .is_some()
                    })
                {
                    let mem = ctrl.resolve_mem(&mem);
                    if mem.is_global() {
                        self.game_seconds_checked = true;
                        self.result.ai_military_update_counter = Some(ctx.memory(&mem));
                    }
                }
            }
            Operation::ConditionalMove(ref dest, _, condition)
                if self.state == StepAiState::SpendMoney =>
            {
                let condition = ctrl.resolve(condition);
                let ok = condition.if_arithmetic_gt()
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 4500))
                    .filter(|&x| is_game_seconds(self.game, x))
                    .is_some();
                if ok {
                    ctrl.skip_operation();
                    ctrl.move_unresolved(dest, ctx.custom(0));
                }
            }
            Operation::Move(ref dest, val) if self.state == StepAiState::StepAiScript => {
                // step_objects has `counter = counter - 1`
                // instruction which is after step_ai, so we can stop
                // if that is reached.
                if self.inline_depth == 0 {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == MemAccessSize::Mem32 {
                            let val = ctrl.resolve(val);
                            let dest = ctrl.resolve_mem(mem);
                            let stop = Operand::and_masked(val).0
                                .if_arithmetic_sub_const(1)
                                .and_then(|x| x.if_memory())
                                .filter(|&x| x == &dest)
                                .is_some();
                            if stop {
                                ctrl.end_analysis();
                            }
                        }
                    }
                    return;
                } else if self.inline_depth == 1 {
                    // Avoid analyzing step_dcreep, which does
                    // Mem8[global + global >> 7] read early on to the function.
                    if let Some(mem) = val.if_mem8() {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.if_add_either(ctx, |x| x.if_arithmetic_rsh_const(7)).is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val)
                if self.state == StepAiState::StepRegions =>
            {
                // First branch of ai_step_region always clears flag 0x4
                // region = ai_regions[arg1] + arg2 * region_size;
                // region.flags &= !0x4;
                let val = ctrl.resolve(val);
                let dest = ctrl.resolve_mem(mem);
                let ok = val.if_arithmetic_and_const(0xfb)
                    .and_then(|x| x.if_mem8())
                    .filter(|&x| x.address() == dest.address())
                    .and_then(|x| x.if_offset(8)) // flag offset
                    .and_then(|x| x.if_arithmetic_add()) // addition for regions base + index
                    .and_either(|x| {
                        // One is arg2 * region_size (0x34),
                        // other is ai_regions[arg1], that is, Mem32[ai_regions + arg1 * 4]
                        // Check for just ai_regions[arg1]
                        x.if_memory()
                            .and_then(|x| {
                                x.if_add_either(ctx, |x| {
                                    x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                                        .filter(|&x| {
                                            Operand::and_masked(x).0 ==
                                                self.arg_cache.on_entry(0)
                                        })
                                })
                            })
                    })
                    .is_some();
                if ok {
                    self.result.ai_step_region = Some(E::VirtualAddress::from_u64(0));
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), _)
                if self.state == StepAiState::TargetExpansion =>
            {
                let dest = ctrl.resolve_mem(mem);
                let is_player_global_write = self.result.step_ai_regions_player
                    .is_some_and(|x| x.if_memory() == Some(&dest));
                if is_player_global_write {
                    ctrl.skip_operation();
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val)
                if self.state == StepAiState::ResourceAreas =>
            {
                if ctrl.resolve(val).if_constant() == Some(0x1c2) {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.is_global() {
                        self.result.resource_areas =
                            Some(mem.with_offset(0u64.wrapping_sub(0x2ee4)).address_op(ctx));
                        self.state = StepAiState::TargetResetCounter;
                        if self.inline_depth > 1 {
                            ctrl.end_analysis();
                        } else {
                            ctrl.end_branch();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val)
                if self.state == StepAiState::TargetResetCounter =>
            {
                if ctrl.resolve(val).if_constant() == Some(0x12c) {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.is_global() {
                        self.result.ai_target_ignore_reset_counter = Some(ctx.memory(&mem));
                        ctrl.clear_unchecked_branches();
                        self.state = StepAiState::TargetResetCounter2;
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val)
                if self.state == StepAiState::TargetResetCounter2 =>
            {
                if ctrl.resolve(val).if_constant() == Some(6) {
                    let mem = ctrl.resolve_mem(mem);
                    let result = ctx.memory(&mem);
                    if self.target_reset_counter2_candidates.len() == 0 {
                        return;
                    }
                    self.result.ai_target_ignore_reset_counter2 = Some(result);
                    if let Some(&other) = self.target_reset_counter2_candidates.iter()
                        .find(|&&x| x != result)
                    {
                        self.result.ai_target_ignore_request_reset = Some(other);
                        self.state = StepAiState::SpendMoney;
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
    let bump = &analysis.bump;

    let action_create_unit = binary.read_address(actions + E::VirtualAddress::SIZE * 0x2c).ok()?;
    let units_dat_group_flags = binary.read_address(units_dat.0 + 0x2c * units_dat.1).ok()?;
    let units_dat_ai_flags = binary.read_address(units_dat.0 + 0x15 * units_dat.1).ok()?;

    let arg_cache = &analysis.arg_cache;
    let exec_state = E::initial_state(ctx, binary);
    let state = GiveAiState::SearchingSwitchJump;
    let state = AnalysisState::new(bump, analysis_state::StateEnum::GiveAi(state));
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, action_create_unit, exec_state, state);
    let mut analyzer = GiveAiAnalyzer {
        result: None,
        arg_cache,
        inline_depth: 0,
        units_dat_group_flags,
        units_dat_ai_flags,
        stop_on_first_branch: false,
        bump,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct GiveAiAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    units_dat_group_flags: E::VirtualAddress,
    units_dat_ai_flags: E::VirtualAddress,
    stop_on_first_branch: bool,
    bump: &'acx Bump,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    GiveAiAnalyzer<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *ctrl.user_state().get::<GiveAiState>() {
            GiveAiState::SearchingSwitchJump => {
                match *op {
                    Operation::Jump { condition, to } => {
                        let condition = ctrl.resolve(condition);
                        // Trigger.current_player = Mem32[arg1 + 10]
                        let is_switch_default_case = condition
                            .if_arithmetic_gt_const(0xd)
                            .and_then(|x| x.if_arithmetic_sub_const(0xd))
                            .and_then(|x| x.if_mem32_offset(0x10))
                            .filter(|&x| x == self.arg_cache.on_entry(0))
                            .is_some();
                        if is_switch_default_case {
                            if let Some(to) = ctrl.resolve_va(to) {
                                let state = GiveAiState::SearchingMapCreateUnit;
                                let state = AnalysisState::new(
                                    self.bump,
                                    analysis_state::StateEnum::GiveAi(state)
                                );
                                let mut analysis = FuncAnalysis::custom_state(
                                    ctrl.binary(),
                                    ctx,
                                    to,
                                    ctrl.exec_state().clone(),
                                    state,
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            // Arg 1 = unit id (Mem16[arg1] + 18)
                            // Arg 2 = x ((location.left + location.right) sdiv 2)
                            // Arg 3 = y ((location.top + location.bottom) sdiv 2)
                            let ok = Some(())
                                .map(|_| ctrl.resolve_arg(0))
                                .and_then(|x| x.if_mem16_offset(0x18))
                                .filter(|&x| x == self.arg_cache.on_entry(0))
                                .map(|_| ctrl.resolve_arg(1))
                                .filter(|&x| is_sdiv_2(x))
                                .map(|_| ctrl.resolve_arg(2))
                                .filter(|&x| is_sdiv_2(x))
                                .is_some();
                            if ok {
                                self.inline_depth = 0;
                                ctrl.user_state().set(GiveAiState::SearchingRaceCheck);
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
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
                        let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                            .and_then(|x| x.0.if_arithmetic_and())
                            .filter(|x| x.1.if_constant().is_some())
                            .and_then(|x| x.0.if_mem8_offset(self.units_dat_group_flags.as_u64()))
                            .is_some();
                        if ok {
                            self.stop_on_first_branch = false;
                            ctrl.user_state().set(GiveAiState::RaceCheckSeen);
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
                        if let Some(dest) = ctrl.resolve_va(dest) {
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
                        let ok = condition.if_arithmetic_eq_neq()
                            .and_then(|x| x.0.if_arithmetic_and_const(0x2))
                            .and_then(|x| x.if_mem8_offset(self.units_dat_ai_flags.as_u64()))
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
    let mut exec_state = E::initial_state(ctx, binary);
    let order_state = ctx.mem_access8(ctx.register(1), E::struct_layouts().unit_order_state());
    let target = ctx.mem_access32(ctx.register(1), E::struct_layouts().unit_target());
    exec_state.write_memory(&order_state, ctx.const_0());
    exec_state.write_memory(&target, ctx.const_0());
    let mut analysis =
        FuncAnalysis::custom_state(binary, ctx, order_move, exec_state, Default::default());
    let mut analyzer = AiPrepareMovingToAnalyzer {
        result: None,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AiPrepareMovingToAnalyzer<'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    inline_depth: u8,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for AiPrepareMovingToAnalyzer<'e, E> {
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
                let jump_on_null = condition.if_arithmetic_eq_neq_zero(ctx)
                    .and_then(|x| {
                        let unit_ai = E::struct_layouts().unit_ai();
                        ctrl.if_mem_word_offset(x.0, unit_ai)
                            .filter(|&x| x == ctx.register(1))?;
                        Some(x.1)
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
                let ecx = ctrl.resolve_register(1);
                let arg1 = ctrl.resolve_arg_thiscall(0);
                let arg2 = ctrl.resolve_arg_thiscall(1);
                if ecx != ctx.register(1) {
                    return;
                }
                let order_target_pos = E::struct_layouts().unit_order_target_pos();
                let ok = arg1.unwrap_sext()
                    .if_mem16_offset(order_target_pos)
                    .filter(|&x| x == ecx)
                    .is_some();
                if !ok {
                    return;
                }
                let ok = arg2.unwrap_sext()
                    .if_mem16_offset(order_target_pos + 2)
                    .filter(|&x| x == ecx)
                    .is_some();
                if !ok {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(dest) {
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
                            .and_then(|x| {
                                x.if_add_either_other(ctx, |x| {
                                    x.if_arithmetic_mul_const(4)?
                                        .if_mem8_offset(E::struct_layouts().unit_player())
                                        .filter(|&x| x == ctx.register(1))
                                })
                            })
                    })
                    .map(|x| x.0);
                if single_result_assign(result, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            Operation::Call(dest) if self.inline_depth < 3 => {
                // Inline to f(this, this.order_target.x, this.order_target.y)
                let arg1 = ctrl.resolve_arg(0);
                let arg2 = ctrl.resolve_arg(1);
                let arg3 = ctrl.resolve_arg(2);
                let mut do_inline = false;
                if self.inline_depth == 0 {
                    // Inline to cdecl f(this, arg1, arg2) at depth 0
                    // ("ai_are_on_connected_regions")
                    do_inline = arg1 == ctx.register(1) &&
                        ctx.and_const(arg2, 0xffff) ==
                            ctx.and_const(self.arg_cache.on_thiscall_entry(0), 0xffff) &&
                        ctx.and_const(arg3, 0xffff) ==
                            ctx.and_const(self.arg_cache.on_thiscall_entry(1), 0xffff);
                }
                if !do_inline {
                    // Also inline to f(this.player, unit_region, dest_region)
                    // ("ai_region_reachable_without_transport")
                    // Only checking for player now
                    do_inline = ctx.and_const(arg1, 0xff)
                        .if_mem8_offset(E::struct_layouts().unit_player())
                        .filter(|&x| x == ctx.register(1))
                        .is_some();
                }
                if do_inline {
                    if let Some(dest) = ctrl.resolve_va(dest) {
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
    let bump = &analysis.bump;

    // ai_spend_money calls ai_train_military after checking game_second >= 10
    let exec_state = E::initial_state(ctx, binary);
    let state = TrainMilitaryState {
        seconds_checked: false,
    };
    let state = AnalysisState::new(bump, analysis_state::StateEnum::TrainMilitary(state));
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, spend_money, exec_state, state);
    let mut analyzer = TrainMilitaryAnalyzer::<E> {
        result: None,
        game,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct TrainMilitaryAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    game: Operand<'e>,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    TrainMilitaryAnalyzer<'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                if ctrl.user_state().get::<TrainMilitaryState>().seconds_checked {
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
                    ctrl.user_state().get::<TrainMilitaryState>().seconds_checked = true;
                }
            }
            Operation::Call(dest) => {
                if ctrl.user_state().get::<TrainMilitaryState>().seconds_checked {
                    let result = ctrl.resolve_va(dest);
                    if single_result_assign(result, &mut self.result) {
                        ctrl.end_analysis();
                    } else {
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

fn is_game_seconds<'e>(game: Operand<'e>, operand: Operand<'e>) -> bool {
    operand.if_mem32_offset(0xe608) == Some(game)
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
                let ctx = ctrl.ctx();
                let arg1 = ctrl.resolve_arg(0);
                let is_region1 = arg1.if_arithmetic_add_const(E::struct_layouts().ai_region_size())
                    .and_then(|x| ctrl.if_mem_word(x))
                    .and_then(|x| x.address_op(ctx).if_arithmetic_add())
                    .and_if_either_other(|x| x == self.ai_regions)
                    .and_then(|x| x.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into()))
                    .filter(|&x| {
                        ctx.and_const(x, 0xffff_ffff) ==
                            ctx.and_const(self.arg_cache.on_entry(0), 0xffff_ffff)
                    })
                    .is_some();
                if !is_region1 {
                    return;
                }
                let arg2 = ctrl.resolve_arg(1);
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

    struct Analyzer<'exec, E: ExecutionState<'exec>> {
        result: Option<E::VirtualAddress>,
    }
    impl<'exec, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for Analyzer<'exec, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
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

    let mut analyzer = Analyzer::<E> {
        result: None,
    };
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, order_guard);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub(crate) struct AiRemoveUnit<Va: VirtualAddressTrait> {
    pub military: Option<Va>,
    pub town: Option<Va>,
}

pub(crate) fn analyze_ai_remove_unit<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    ai_remove_unit: E::VirtualAddress,
) -> AiRemoveUnit<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = AiRemoveUnit {
        military: None,
        town: None,
    };

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, ai_remove_unit);
    let mut analyzer = AiRemoveUnitAnalyzer {
        result: &mut result,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AiRemoveUnitAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut AiRemoveUnit<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AiRemoveUnitAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // Just expecting first call to be military remove (a1 = a1, a2 = a2),
        // second town remove (a1 = a1, a2 = 0)
        // No jumps even with assertion builds
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg1 = ctrl.resolve_arg(0);
                    if arg1 != self.arg_cache.on_entry(0) {
                        self.fail(ctrl);
                        return;
                    }
                    let arg2 = ctrl.resolve_arg_u8(1);
                    if self.result.military.is_none() {
                        if arg2 != ctx.and_const(self.arg_cache.on_entry(1), 0xff) {
                            self.fail(ctrl);
                            return;
                        } else {
                            self.result.military = Some(dest);
                        }
                    } else {
                        if arg2 != ctx.const_0() {
                            self.fail(ctrl);
                            return;
                        } else {
                            self.result.town = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    self.fail(ctrl);
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), _) => {
                let ctx = ctrl.ctx();
                if mem.address().0 != ctx.register(4) {
                    self.fail(ctrl);
                }
            }
            Operation::Jump { .. } => {
                self.fail(ctrl);
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> AiRemoveUnitAnalyzer<'a, 'e, E> {
    fn fail(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.result.military = None;
        self.result.town = None;
        ctrl.end_analysis();
    }
}

pub(crate) struct AddAiToTrainedUnit<Va: VirtualAddressTrait> {
    pub change_ai_region_state: Option<Va>,
    pub add_building_ai: Option<Va>,
    pub add_military_ai: Option<Va>,
}

pub(crate) fn analyze_add_ai_to_trained_unit<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    add_ai_to_trained_unit: E::VirtualAddress,
) -> AddAiToTrainedUnit<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = AddAiToTrainedUnit {
        change_ai_region_state: None,
        add_building_ai: None,
        add_military_ai: None,
    };

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, add_ai_to_trained_unit);
    let mut analyzer = AddAiToTrainedAnalyzer {
        result: &mut result,
        arg_cache,
        state: AddAiToTrainedState::OverlordJump,
        inline_depth: 0,
        overlord_neq_branch: None,
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AddAiToTrainedState {
    /// Check for x == 0x2a jump
    OverlordJump,
    /// On eq branch, function call to add_building_ai(a1 = a1, a2)
    /// May be tail call.
    AddBuildingAi,
    /// On overlord neq branch, check for x == 0x28 jump
    BroodlingJump,
    /// On broodling eq branch, inline once to make_military_in_current_region(a1 = a1, a2),
    /// find add_military(a1 = ai_regions + id * 0x34, a2, 1u8)
    /// May be tail call.
    AddMilitaryAi,
}

struct AddAiToTrainedAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut AddAiToTrainedUnit<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: AddAiToTrainedState,
    inline_depth: u8,
    overlord_neq_branch: Option<(E::VirtualAddress, E)>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AddAiToTrainedAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match self.state {
            AddAiToTrainedState::OverlordJump | AddAiToTrainedState::BroodlingJump => {
                if let Operation::Jump { condition, to } = *op {
                    let unit_id = match self.state {
                        AddAiToTrainedState::OverlordJump => 0x2a,
                        _ => 0x28,
                    };
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(unit_id))
                        .map(|x| x.2);
                    if let Some(jump_if_eq) = ok {
                        if self.state == AddAiToTrainedState::OverlordJump {
                            if let Some(to) = ctrl.resolve_va(to) {
                                let no_jump = ctrl.current_instruction_end();
                                let (eq_branch, neq_branch) = match jump_if_eq {
                                    true => (to, no_jump),
                                    false => (no_jump, to),
                                };
                                let state = ctrl.exec_state();
                                self.overlord_neq_branch = Some((neq_branch, state.clone()));
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(eq_branch);
                                self.state = AddAiToTrainedState::AddBuildingAi;
                            }
                        } else {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(jump_if_eq, to);
                            self.state = AddAiToTrainedState::AddMilitaryAi;
                        }
                    }
                }
            }
            AddAiToTrainedState::AddBuildingAi | AddAiToTrainedState::AddMilitaryAi => {
                let ctx = ctrl.ctx();
                let arg_cache = self.arg_cache;
                if let Some((dest, is_tail)) = ctrl.call_or_tail_call(op, ctx.register(4)) {
                    let arg1 = if is_tail { arg_cache.on_entry(0) } else { arg_cache.on_call(0) };
                    let arg2 = if is_tail { arg_cache.on_entry(1) } else { arg_cache.on_call(1) };
                    let arg3 = if is_tail { arg_cache.on_entry(2) } else { arg_cache.on_call(2) };
                    if self.state == AddAiToTrainedState::AddBuildingAi {
                        let ok = ctrl.resolve(arg1) == arg_cache.on_entry(0) &&
                            ctrl.resolve(arg2) == arg_cache.on_entry(1);
                        if ok {
                            self.result.add_building_ai = Some(dest);
                            ctrl.clear_unchecked_branches();
                            ctrl.end_branch();
                            if let Some((addr, state)) = self.overlord_neq_branch.take() {
                                ctrl.add_branch_with_state(addr, state, Default::default());
                                self.state = AddAiToTrainedState::BroodlingJump;
                            }
                        }
                    } else {
                        let arg1 = ctrl.resolve(arg1);
                        let ai_region_size = E::struct_layouts().ai_region_size();
                        let a1_ok = arg1.if_arithmetic_add()
                            .and_either_other(|x| x.if_arithmetic_mul_const(ai_region_size))
                            .and_then(|x| ctrl.if_mem_word(x))
                            .is_some();
                        if a1_ok {
                            let arg2 = ctrl.resolve(arg2);
                            if arg2 == arg_cache.on_entry(1) {
                                let arg3 = ctrl.resolve(arg3);
                                if ctx.and_const(arg3, 0xff) == ctx.const_1() {
                                    self.result.add_military_ai = Some(dest);
                                    ctrl.end_analysis();
                                }
                            } else if ctx.and_const(arg2, 0xff) == ctx.const_1() {
                                single_result_assign(
                                    Some(dest),
                                    &mut self.result.change_ai_region_state,
                                );
                            }
                        }
                    }
                }

                if self.state == AddAiToTrainedState::AddMilitaryAi {
                    if let Operation::Call(dest) = *op {
                        if seems_assertion_call(ctrl) {
                            ctrl.end_branch();
                            return;
                        }
                        if self.inline_depth == 0 {
                            let inline =
                                ctrl.resolve_arg(0) == arg_cache.on_entry(0) &&
                                ctrl.resolve_arg(1) == arg_cache.on_entry(1);
                            if inline {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.inline_depth = 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth = 0;
                                    if self.result.add_military_ai.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) struct AddBuildingAi<Va: VirtualAddressTrait> {
    pub add_town_unit_ai: Option<Va>,
}

pub(crate) fn analyze_add_building_ai<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    add_building_ai: E::VirtualAddress,
) -> AddBuildingAi<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut result = AddBuildingAi {
        add_town_unit_ai: None,
    };

    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, add_building_ai);
    let mut analyzer = AddBuildingAiAnalyzer {
        result: &mut result,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct AddBuildingAiAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut AddBuildingAi<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AddBuildingAiAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            // Just add_town_unit_ai(a1 = a1.ai.town, a2)
            // arg1.ai access may be outlined so just check BuildingAi.town deref
            let arg1 = ctrl.resolve_arg(0);
            let ok =
                ctrl.if_mem_word_offset(arg1, E::struct_layouts().building_ai_town()).is_some() &&
                    ctrl.resolve_arg(1) == self.arg_cache.on_entry(1);
            if ok {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.result.add_town_unit_ai = Some(dest);
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) struct AiStepRegion<Va: VirtualAddressTrait> {
    pub ai_region_update_strength: Option<Va>,
    pub ai_region_update_target: Option<Va>,
    pub ai_region_abandon_if_overwhelmed: Option<Va>,
    pub ai_region_pick_attack_target: Option<Va>,
    pub change_ai_region_state: Option<Va>,
}

pub(crate) fn analyze_ai_step_region<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    ai_step_region: E::VirtualAddress,
) -> AiStepRegion<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = AiStepRegion {
        ai_region_update_strength: None,
        ai_region_update_target: None,
        ai_region_abandon_if_overwhelmed: None,
        ai_region_pick_attack_target: None,
        change_ai_region_state: None,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, ai_step_region);
    let mut analyzer = StepRegionInnerAnalyzer {
        result: &mut result,
        region_operand: ctx.const_0(),
        inline_depth: 0,
        state: StepAiRegionState::FindSwitch,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepAiRegionState {
    /// Switch on [ai_regions[a1] + a2].state
    FindSwitch,
    /// On switch state 8 (Attack grouping), find function that writes to region.local_strength = 0
    /// before any calls or jumps.
    /// Size may be up to u64 since it also zeroes later strength values
    /// May have to inline once to state_attack_grouping.
    UpdateStrength,
    /// Next call with a1 = region after UpdateStrength
    UpdateTarget,
    /// Find jump on region.flags & 0x20, follow nonzero branch
    AbandonFlagCheck,
    /// Next call with a1 = region
    AbandonCall,
    /// Find jump where x == 1ffd, follow that
    PickAttackTargetUnwalkableJump,
    /// Find change_ai_region_state(a1 = region, 0u8)
    ChangeRegionState,
    /// Next call with a1 = region
    PickAttackTarget,
}

struct StepRegionInnerAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut AiStepRegion<E::VirtualAddress>,
    // Valid after FindSwitch
    region_operand: Operand<'e>,
    inline_depth: u8,
    state: StepAiRegionState,
    call_tracker: CallTracker<'acx, 'e, E>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepRegionInnerAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        let is_jump_state = match self.state {
            StepAiRegionState::FindSwitch | StepAiRegionState::AbandonFlagCheck |
                StepAiRegionState::PickAttackTargetUnwalkableJump => true,
            _ => false,
        };
        let is_call_state = !is_jump_state ||
            self.state == StepAiRegionState::PickAttackTargetUnwalkableJump;
        if self.state == StepAiRegionState::UpdateStrength && self.inline_depth > 0 {
            if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                let value = ctrl.resolve(value);
                if value == ctx.const_0() {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.address() == (self.region_operand, 0x10) {
                        self.result.ai_region_update_strength =
                            Some(E::VirtualAddress::from_u64(0));
                        ctrl.end_analysis();
                    }
                }
                return;
            }
        }
        match *op {
            Operation::Call(dest) => {
                if !is_call_state {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(dest) {
                    match self.state {
                        StepAiRegionState::UpdateStrength => {
                            if self.inline_depth >= 2 {
                                ctrl.end_analysis();
                            } else {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.ai_region_update_strength ==
                                    Some(E::VirtualAddress::from_u64(0))
                                {
                                    self.result.ai_region_update_strength = Some(dest);
                                    self.state = StepAiRegionState::UpdateTarget;
                                } else {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                        StepAiRegionState::UpdateTarget | StepAiRegionState::AbandonCall |
                            StepAiRegionState::ChangeRegionState |
                            StepAiRegionState::PickAttackTarget =>
                        {
                            let a1 = ctrl.resolve_arg(0);
                            if a1 == self.region_operand {
                                if self.state == StepAiRegionState::UpdateTarget {
                                    self.state = StepAiRegionState::AbandonFlagCheck;
                                    self.result.ai_region_update_target = Some(dest);
                                } else if self.state == StepAiRegionState::AbandonCall {
                                    self.state = StepAiRegionState::PickAttackTargetUnwalkableJump;
                                    self.result.ai_region_abandon_if_overwhelmed = Some(dest);
                                } else if self.state == StepAiRegionState::ChangeRegionState {
                                    let a2 = ctrl.resolve_arg_u8(1);
                                    if a2 == ctx.const_0() {
                                        self.state = StepAiRegionState::PickAttackTarget;
                                        self.result.change_ai_region_state = Some(dest);
                                    }
                                } else {
                                    // self.state == StepAiRegionState::PickAttackTarget
                                    ctrl.end_analysis();
                                    self.result.ai_region_pick_attack_target = Some(dest);
                                }
                            }
                        }
                        StepAiRegionState::PickAttackTargetUnwalkableJump => {
                            self.call_tracker.add_call(ctrl, dest);
                        }
                        _ => (),
                    }
                }
            }
            Operation::Jump { to, condition } => {
                if !is_jump_state && condition != ctx.const_1() {
                    ctrl.end_analysis();
                    return;
                }
                if condition == ctx.const_1() {
                    if self.state == StepAiRegionState::FindSwitch && to.if_constant().is_none() {
                        let to = ctrl.resolve(to);
                        let switch = CompleteSwitch::new(to, ctx, ctrl.exec_state());
                        if let Some(switch) = switch {
                            if let Some(index) = switch.index_operand(ctx) {
                                if let Some(base) = index.if_mem8_offset(5) {
                                    self.region_operand = base;
                                    let binary = ctrl.binary();
                                    if let Some(state8) = switch.branch(binary, ctx, 0x8) {
                                        self.state = StepAiRegionState::UpdateStrength;
                                        ctrl.clear_unchecked_branches();
                                        ctrl.continue_at_address(state8);
                                    }
                                }
                            }
                        }
                    }
                } else if self.state != StepAiRegionState::FindSwitch {
                    let condition = ctrl.resolve(condition);
                    if self.state == StepAiRegionState::AbandonFlagCheck {
                        if let Some((val, eq)) = condition.if_and_mask_eq_neq(0x20) {
                            if val.if_mem8_offset(8) == Some(self.region_operand) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_neq_address(eq, to);
                                self.state = StepAiRegionState::AbandonCall;
                            }
                        }
                    } else {
                        let condition =
                            self.call_tracker.resolve_calls_with_branch_limit(condition, 4);
                        if let Some(eq) = condition.if_arithmetic_eq_neq()
                            .filter(|x| x.1.if_constant() == Some(0x1ffd))
                            .map(|x| x.2)
                        {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.state = StepAiRegionState::ChangeRegionState;
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) struct OrderUnitAi<Va: VirtualAddressTrait> {
    pub unit_ai_worker: Option<Va>,
    pub unit_ai_military: Option<Va>,
    pub ai_try_progress_spending_request: Option<Va>,
    pub find_nearest_unit_in_area: Option<Va>,
    pub find_nearest_unit_around_unit: Option<Va>,
    pub can_attack_unit: Option<Va>,
    pub is_outside_attack_range: Option<Va>,
    pub ai_should_keep_targeting: Option<Va>,
}

pub(crate) fn analyze_order_unit_ai<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    order_unit_ai: E::VirtualAddress,
) -> OrderUnitAi<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let mut result = OrderUnitAi {
        unit_ai_worker: None,
        unit_ai_military: None,
        ai_try_progress_spending_request: None,
        find_nearest_unit_in_area: None,
        find_nearest_unit_around_unit: None,
        can_attack_unit: None,
        is_outside_attack_range: None,
        ai_should_keep_targeting: None,
    };

    let arg_cache = &actx.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, order_unit_ai);
    let mut analyzer = OrderUnitAiAnalyzer {
        result: &mut result,
        arg_cache,
        state: OrderUnitAiState::FindAiCheck,
        inline_depth: 0,
        unit_specific_depth: 0,
        entry_esp: ctx.register(4),
        after_ai_type_jump_branches: bumpvec_with_capacity(16, bump),
        worker_state: None,
        building_state: None,
        military_state: None,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x10),
        find_nearest_unit_in_area_candidate: None,
        ai_call_candidate: None,
    };
    analysis.analyze(&mut analyzer);
    if let Some(ai_should_keep_targeting) = result.ai_should_keep_targeting {
        let mut state = E::initial_state(ctx, binary);
        state.move_to(&DestOperand::from_oper(arg_cache.on_thiscall_entry(0)), ctx.const_0());
        let mut analysis = FuncAnalysis::with_state(binary, ctx, ai_should_keep_targeting, state);
        let mut analyzer = ShouldKeepTargetingAnalyzer {
            result: &mut result,
            state: ShouldKeepTargetingState::CanAttackUnit,
        };
        analysis.analyze(&mut analyzer);
    }
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum OrderUnitAiState {
    /// Check unit.ai != null
    FindAiCheck,
    /// Inline once to ai_unit_specific(a1 = this), first jump should be
    /// secondary_order == 6d
    CloakCheck,
    /// In cloak branch, ai_should_keep_targeting(this = unit, a1 = null)
    AiShouldKeepTargeting,
    /// Inline once with a1 = unit, tail call or first call
    /// find_nearest_unit_around_unit(this = unit, 0x100, func, unit)
    FindNearestUnitAroundUnit,
    /// Back to inline depth 0, find jump on unit.ai.type == 2, 3, 4
    /// Save their state but don't analyze yet
    AiTypeJumps,
    /// Find issue_order_targeting_unit(this = unit, 0x31, target = func())
    /// (Possibly tail call)
    /// Where func is either find_nearest_unit_in_area(this = unit, &global_map_bounds, func, unit)
    /// Or a function which (tail) calls it.
    FindRepairer,
    /// Should call just unit_ai_worker before joining with after_ai_type_jump_branches
    WorkerAi,
    /// Should call ai_try_progress_spending_request and then write unit.order_timer
    BuildingAi,
    /// Should call just unit_ai_military
    MilitaryAi,
}

struct OrderUnitAiAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderUnitAi<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    unit_specific_depth: u8,
    entry_esp: Operand<'e>,
    state: OrderUnitAiState,
    /// For determining when worker / building / military
    after_ai_type_jump_branches: BumpVec<'acx, (E::VirtualAddress, E::VirtualAddress)>,
    worker_state: Option<(E, analysis::DefaultState, E::VirtualAddress)>,
    building_state: Option<(E, analysis::DefaultState, E::VirtualAddress)>,
    military_state: Option<(E, analysis::DefaultState, E::VirtualAddress)>,
    call_tracker: CallTracker<'acx, 'e, E>,
    /// Set only if find_repairer is inlined
    find_nearest_unit_in_area_candidate: Option<E::VirtualAddress>,
    ai_call_candidate: Option<E::VirtualAddress>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    OrderUnitAiAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            OrderUnitAiState::FindAiCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((op, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if ctrl.if_mem_word_offset(op, E::struct_layouts().unit_ai()) ==
                            Some(ctx.register(1))
                        {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq, to);
                            self.state = OrderUnitAiState::CloakCheck;
                        }
                    }
                }
            }
            OrderUnitAiState::CloakCheck => {
                match *op {
                    Operation::Call(dest) => {
                        if self.inline_depth == 0 {
                            if let Some(dest) = ctrl.resolve_va(dest) {
                                let a1 = ctrl.resolve_arg(0);
                                if a1 == ctx.register(1) {
                                    self.inline_depth = 1;
                                    let old_esp = self.entry_esp;
                                    // inline to ai_unit_specific
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth = 0;
                                    self.entry_esp = old_esp;
                                    if self.state != OrderUnitAiState::CloakCheck {
                                        self.state = OrderUnitAiState::AiTypeJumps;
                                    }
                                }
                            }
                        }
                    }
                    Operation::Jump { condition, to } => {
                        let condition = ctrl.resolve(condition);
                        let ok = condition.if_arithmetic_eq_neq()
                            .filter(|x| x.1.if_constant() == Some(0x6d))
                            .map(|x| x.2);
                        if let Some(eq) = ok {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_eq_address(eq, to);
                            self.state = OrderUnitAiState::AiShouldKeepTargeting;
                        } else {
                            if self.inline_depth != 0 {
                                // Should be first jump in ai_unit_specific
                                ctrl.end_analysis();
                            }
                        }
                    }
                    _ => (),
                }
            }
            OrderUnitAiState::AiShouldKeepTargeting => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = ctrl.resolve_register(1) == ctx.register(1) &&
                            ctrl.resolve_arg_thiscall(0) == ctx.const_0();
                        if ok {
                            self.result.ai_should_keep_targeting = Some(dest);
                            self.unit_specific_depth = self.inline_depth;
                            self.state = OrderUnitAiState::FindNearestUnitAroundUnit;
                        }
                    }
                }
            }
            OrderUnitAiState::FindNearestUnitAroundUnit => {
                let unit = ctx.register(1);
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = ctrl.resolve_register(1) == unit &&
                            ctrl.resolve_arg_thiscall_u32(0).if_constant() == Some(0x100) &&
                            ctrl.resolve_arg_thiscall(2) == unit;
                        if ok {
                            self.result.find_nearest_unit_around_unit = Some(dest);
                            self.state = OrderUnitAiState::AiTypeJumps;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                        if self.inline_depth != self.unit_specific_depth {
                            ctrl.end_analysis();
                            return;
                        }
                        let inline = self.inline_depth == self.unit_specific_depth &&
                            ctrl.resolve_arg(0) == unit;
                        if inline {
                            self.inline_depth += 1;
                            self.entry_esp = ctrl.get_new_esp_for_call();
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.state != OrderUnitAiState::FindNearestUnitAroundUnit &&
                                self.inline_depth != 0
                            {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    if self.inline_depth != self.unit_specific_depth {
                        if condition == ctx.const_1() &&
                            ctrl.resolve_register(4) == self.entry_esp
                        {
                            // Tail call
                            let ok = ctrl.resolve_register(1) == unit &&
                                ctrl.resolve(self.arg_cache.on_thiscall_entry_u32(0)).if_constant()
                                    == Some(0x100) &&
                                ctrl.resolve(self.arg_cache.on_thiscall_entry(2)) == unit;
                            if ok {
                                self.result.find_nearest_unit_around_unit = ctrl.resolve_va(to);
                                self.state = OrderUnitAiState::AiTypeJumps;
                            }
                        }
                        // Should be first jump or nothing
                        ctrl.end_analysis();
                    }
                }
            }
            OrderUnitAiState::AiTypeJumps => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((op, val, eq)) = condition.if_arithmetic_eq_neq() {
                        if let Some(c) = val.if_constant() {
                            let is_ai_type = op.if_mem8_offset(E::struct_layouts().unit_ai_type())
                                .and_then(|mut x| {
                                    if x.if_custom().is_some() {
                                        // May be unit_ai_expect_valid call
                                        x = self.call_tracker.resolve_calls(x);
                                    }
                                    ctrl.if_mem_word_offset(x, E::struct_layouts().unit_ai())
                                }) == Some(ctx.register(1));
                            if is_ai_type {
                                let state = match c {
                                    2 => &mut self.worker_state,
                                    3 => &mut self.building_state,
                                    4 => &mut self.military_state,
                                    _ => return,
                                };
                                *state = ctrl.state_for_eq_address(eq, to);
                                ctrl.continue_at_neq_address(eq, to);
                                if self.worker_state.is_some() &&
                                    self.building_state.is_some() &&
                                    self.military_state.is_some()
                                {
                                    self.state = OrderUnitAiState::FindRepairer;
                                }
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            OrderUnitAiState::FindRepairer => {
                let (dest, a1, a2, a3) = match *op {
                    Operation::Jump { condition, to } => {
                        if condition == ctx.const_1() &&
                            ctrl.resolve_register(4) == self.entry_esp
                        {
                            (
                                to,
                                self.arg_cache.on_thiscall_entry(0),
                                self.arg_cache.on_thiscall_entry(1),
                                self.arg_cache.on_thiscall_entry(2),
                            )
                        } else {
                            return;
                        }
                    }
                    Operation::Call(dest) => (
                        dest,
                        self.arg_cache.on_thiscall_call(0),
                        self.arg_cache.on_thiscall_call(1),
                        self.arg_cache.on_thiscall_call(2),
                    ),
                    _ => return,
                };

                if ctx.and_const(ctrl.resolve(a1), 0xff).if_constant() == Some(0x31) {
                    if ctrl.resolve_register(1) != ctx.register(1) {
                        return;
                    }
                    // issue_order_targeting_unit
                    let target = ctrl.resolve(a2);
                    if let Some(custom) = target.unwrap_and_mask().if_custom() {
                        if let Some(addr) = self.call_tracker.custom_id_to_func(custom) {
                            if Some(addr) == self.find_nearest_unit_in_area_candidate {
                                self.result.find_nearest_unit_in_area = Some(addr);
                            } else {
                                let binary = ctrl.binary();
                                self.inline_depth = 1;
                                let old_esp = self.entry_esp;
                                self.entry_esp = ctx.register(4);
                                let mut analysis = FuncAnalysis::new(binary, ctx, addr);
                                analysis.analyze(self);
                                self.entry_esp = old_esp;
                                self.inline_depth = 0;
                            }
                        }
                    }
                    self.next_ai_state(ctrl);
                    return;
                } else {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let unit = if self.inline_depth == 0 {
                            ctx.register(1)
                        } else {
                            self.arg_cache.on_entry(0)
                        };
                        if ctrl.resolve_register(1) == unit && ctrl.resolve(a3) == unit {
                            if self.inline_depth == 0 {
                                self.find_nearest_unit_in_area_candidate = Some(dest);
                            } else {
                                self.result.find_nearest_unit_in_area = Some(dest);
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            OrderUnitAiState::WorkerAi | OrderUnitAiState::BuildingAi |
                OrderUnitAiState::MilitaryAi =>
            {
                if let Operation::Call(dest) = *op {
                    if self.ai_call_candidate.is_none() {
                        self.ai_call_candidate = ctrl.resolve_va(dest);
                    } else {
                        self.next_ai_state(ctrl);
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        if let Some(to) = ctrl.resolve_va(to) {
                            let is_after_branch = self.after_ai_type_jump_branches.iter()
                                .any(|x| to >= x.0 && to < x.1);
                            if is_after_branch {
                                if self.state == OrderUnitAiState::WorkerAi {
                                    self.result.unit_ai_worker = self.ai_call_candidate;
                                } else if self.state == OrderUnitAiState::MilitaryAi {
                                    self.result.unit_ai_military = self.ai_call_candidate;
                                }
                            }
                        }
                    }
                    self.next_ai_state(ctrl);
                } else if self.state == OrderUnitAiState::BuildingAi {
                    if let Operation::Move(DestOperand::Memory(ref mem), _) = *op {
                        if mem.size == MemAccessSize::Mem8 {
                            let mem = ctrl.resolve_mem(mem);
                            if mem.address() ==
                                (ctx.register(1), E::struct_layouts().unit_order_timer())
                            {
                                self.result.ai_try_progress_spending_request =
                                    self.ai_call_candidate;
                                self.next_ai_state(ctrl);
                            }
                        }
                    }
                }
            }
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.state == OrderUnitAiState::FindRepairer {
            self.after_ai_type_jump_branches.push((ctrl.branch_start(), ctrl.address()));
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> OrderUnitAiAnalyzer<'a, 'acx, 'e, E> {
    fn next_ai_state(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let state = if let Some(new) = self.worker_state.take() {
            ctrl.continue_with_state(new);
            OrderUnitAiState::WorkerAi
        } else if let Some(new) = self.military_state.take() {
            ctrl.continue_with_state(new);
            OrderUnitAiState::MilitaryAi
        } else if let Some(new) = self.building_state.take() {
            ctrl.continue_with_state(new);
            OrderUnitAiState::BuildingAi
        } else {
            ctrl.end_analysis();
            return;
        };
        self.state = state;
        self.ai_call_candidate = None;
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum ShouldKeepTargetingState {
    /// can_attack_unit(this = target, a1 = this, a2 = 1u8)
    CanAttackUnit,
    /// is_outside_attack_range(this = target, a1 = this)
    IsOutsideAttackRange,
}

struct ShouldKeepTargetingAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut OrderUnitAi<E::VirtualAddress>,
    state: ShouldKeepTargetingState,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    ShouldKeepTargetingAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            let ctx = ctrl.ctx();
            let is_target = |op: Operand<'e>| {
                op.if_memory()
                    .is_some_and(|x| {
                        x.size == E::WORD_SIZE &&
                            x.address() == (ctx.register(1), E::struct_layouts().unit_target())
                    })
            };
            if let Some(dest) = ctrl.resolve_va(dest) {
                match self.state {
                    ShouldKeepTargetingState::CanAttackUnit => {
                        let ok = is_target(ctrl.resolve_register(1)) &&
                            ctrl.resolve_arg_thiscall(0) == ctx.register(1) &&
                            ctrl.resolve_arg_thiscall_u8(1) == ctx.const_1();
                        if ok {
                            self.result.can_attack_unit = Some(dest);
                            self.state = ShouldKeepTargetingState::IsOutsideAttackRange;
                            ctrl.do_call_with_result(ctx.const_1());
                        }
                    }
                    ShouldKeepTargetingState::IsOutsideAttackRange => {
                        let ok = is_target(ctrl.resolve_register(1)) &&
                            ctrl.resolve_arg_thiscall(0) == ctx.register(1);
                        if ok {
                            self.result.is_outside_attack_range = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) struct UnitAiWorker<Va: VirtualAddressTrait> {
    pub calculate_chokes_for_placement: Option<Va>,
    pub place_building: Option<Va>,
}

pub(crate) fn analyze_unit_ai_worker<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    unit_ai_worker: E::VirtualAddress,
) -> UnitAiWorker<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = UnitAiWorker {
        calculate_chokes_for_placement: None,
        place_building: None,
    };

    let arg_cache = &actx.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, unit_ai_worker);
    let mut analyzer = UnitAiWorkerAnalyzer {
        result: &mut result,
        arg_cache,
        state: UnitAiWorkerState::BunkerIdCheck,
        inline_depth: 0,
        unit_id: ctx.const_0(),
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum UnitAiWorkerState {
    /// - Assume that x == 1 jumps are false (unit.race == terran)
    /// - Inline to worker_try_progress_spending_queue(a1 = unit.ai.town, a2 = unit)
    /// - Find x == 0x7d (bunker), follow true branch and store x as unit_id
    BunkerIdCheck,
    /// Find ai_check_choke_point_regions(a1 = town.player, _, 1u32)
    GetChokePointRegions,
    /// Inline to ai_place_building_outer(a1 = unit, unit_id, _, _, 1u32, 0x40u32)
    /// find ai_place_building(a1 = unit, unit_id, _, _, 0x40u32)
    PlaceBuilding,
}

struct UnitAiWorkerAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut UnitAiWorker<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    state: UnitAiWorkerState,
    unit_id: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitAiWorkerAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            UnitAiWorkerState::BunkerIdCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((a, b, eq)) = condition.if_arithmetic_eq_neq() {
                        if let Some(c) = b.if_constant() {
                            if c == 1 {
                                if a.unwrap_and_mask().if_custom() == Some(0) {
                                    ctrl.continue_at_neq_address(eq, to);
                                }
                            } else if c == 0x7d {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_eq_address(eq, to);
                                self.unit_id = ctx.and_const(a, 0xffff);
                                self.state = UnitAiWorkerState::GetChokePointRegions;
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let inline = self.is_town(ctrl.resolve_arg(0)) &&
                                ctrl.resolve_arg(1) == self.arg_cache.on_entry(0);
                            if inline {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                if self.state != UnitAiWorkerState::BunkerIdCheck {
                                    ctrl.end_analysis();
                                }
                            }
                            if ctrl.resolve_register(1) == self.arg_cache.on_entry(0) {
                                // Possibly unit_race(a1)
                                ctrl.do_call_with_result(ctx.custom(0));
                            }
                        }
                    }
                }
            }
            UnitAiWorkerState::GetChokePointRegions => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = self.is_town_player(ctrl.resolve_arg(0)) &&
                            ctrl.resolve_arg_u32(2) == ctx.const_1();
                        if ok {
                            self.result.calculate_chokes_for_placement = Some(dest);
                            self.state = UnitAiWorkerState::PlaceBuilding;
                            ctrl.clear_unchecked_branches();
                        } else {
                            ctrl.skip_call_preserve_esp();
                        }
                    }
                }
            }
            UnitAiWorkerState::PlaceBuilding => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = ctrl.resolve_arg(0) ==
                                self.arg_cache.on_entry(0) &&
                            {
                                let a1 = ctrl.resolve_arg_u16(1);
                                a1 == self.unit_id || a1.if_constant() == Some(0x7d)
                            };
                        if ok {
                            let a5 = ctrl.resolve_arg_u32(4);
                            if let Some(c) = a5.if_constant() {
                                if c == 1 && self.inline_depth < 2 {
                                    let a6 = ctrl.resolve_arg_u32(5);
                                    if a6.if_constant() == Some(0x40) {
                                        // place_building_outer does radius = id == 7c ? 28 :
                                        // radius check, move explicit constant to id so that
                                        // nothing breaks If place_building_outer is inlined, the
                                        // inliner should remove that check as well since id is
                                        // known to be 7d (hopefully)
                                        let old_unit_id = self.unit_id;
                                        let new_unit_id = ctx.constant(0x7d);
                                        ctrl.move_unresolved(
                                            &DestOperand::from_oper(self.arg_cache.on_call(1)),
                                            new_unit_id
                                        );
                                        self.unit_id = new_unit_id;
                                        self.inline_depth += 1;
                                        ctrl.analyze_with_current_state(self, dest);
                                        self.unit_id = old_unit_id;
                                        self.inline_depth -= 1;
                                        if self.result.place_building.is_some() {
                                            ctrl.end_analysis();
                                        }
                                    }
                                } else if c == 0x40 {
                                    self.result.place_building = Some(dest);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> UnitAiWorkerAnalyzer<'a, 'e, E> {
    fn is_town(&self, op: Operand<'e>) -> bool {
        // MemWord[MemWord[a1 + unit_ai] + worker_ai_town]
        // or
        // MemWord[get_unit_ai_expect_valid(this = a1) + worker_ai_town]
        // which gets replaced with Custom(0) since this = a1
        op.if_memory()
            .and_then(|mem| {
                let (base, offset) = mem.address();
                if mem.size != E::WORD_SIZE || offset != E::struct_layouts().worker_ai_town() {
                    return None;
                }
                if base.if_custom() == Some(0) {
                    return Some(());
                }
                let mem = base.if_memory()?;
                let (base, offset) = mem.address();
                if mem.size != E::WORD_SIZE || offset != E::struct_layouts().unit_ai() {
                    return None;
                }
                if base == self.arg_cache.on_entry(0) {
                    Some(())
                } else {
                    None
                }
            })
            .is_some()
    }

    fn is_town_player(&self, op: Operand<'e>) -> bool {
        op.if_mem8_offset(E::struct_layouts().ai_town_player()).is_some_and(|x| self.is_town(x))
    }
}

pub(crate) struct CalculateChokesForPlacement<Va: VirtualAddressTrait> {
    pub get_choke_point_regions: Option<Va>,
}

pub(crate) fn analyze_calculate_chokes_for_placement<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    calculate_chokes: E::VirtualAddress,
) -> CalculateChokesForPlacement<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = CalculateChokesForPlacement {
        get_choke_point_regions: None,
    };

    let arg_cache = &actx.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, calculate_chokes);
    let mut analyzer = ChokesForPlacementAnalyzer {
        result: &mut result,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct ChokesForPlacementAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut CalculateChokesForPlacement<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for ChokesForPlacementAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        // Should be just get_choke_point_regions(a2_region, _, 2, &stack, &stack, 2)
        if let Operation::Call(dest) = *op {
            let ok = ctrl.resolve_arg_u16(0) ==
                    ctx.and_const(self.arg_cache.on_entry(1), 0xffff) &&
                ctrl.resolve_arg_u32(2).if_constant() == Some(2) &&
                ctrl.resolve_arg_u32(5).if_constant() == Some(2);
            if ok {
                self.result.get_choke_point_regions = ctrl.resolve_va(dest);
                ctrl.end_analysis();
            }
        }
    }
}

pub(crate) struct PlaceBuilding<Va: VirtualAddressTrait> {
    pub update_building_placement_state: Option<Va>,
    pub ai_update_building_placement_state: Option<Va>,
    pub find_nearest_unit_in_area_point: Option<Va>,
}

pub(crate) fn analyze_place_building<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    place_building: E::VirtualAddress,
) -> PlaceBuilding<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = PlaceBuilding {
        update_building_placement_state: None,
        ai_update_building_placement_state: None,
        find_nearest_unit_in_area_point: None,
    };

    let arg_cache = &actx.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, place_building);
    let mut analyzer = PlaceBuildingAnalyzer {
        result: &mut result,
        arg_cache,
        state: PlaceBuildingState::UpdatePlacement,
        inline_depth: 0
    };
    analysis.analyze(&mut analyzer);
    result
}

struct PlaceBuildingAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut PlaceBuilding<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: PlaceBuildingState,
    inline_depth: u8,
}

enum PlaceBuildingState {
    /// find update_building_placement_state(a1 = a1, a1.player, _, _, a2, 0u32, 0u32, 1u32, 0u32)
    /// assume return 1
    UpdatePlacement,
    /// Switch on a2, follow pylon branch (9c)
    Switch,
    /// Inline once if func(a1 = a1.player, a3), find
    /// find_nearest_unit_in_area_pos(a3 & ffff, a3 >> 10, map_bounds, func, a1.player)
    FindNearest,
    /// ai_update_building_placement_state(a1 = a2?, &local, a1.player, _, a5)
    AiUpdatePlacement,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for PlaceBuildingAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            PlaceBuildingState::UpdatePlacement => {
                if let Operation::Call(dest) = *op {
                    if ctrl.check_stack_probe() {
                        return;
                    }
                    if seems_assertion_call(ctrl) {
                        ctrl.end_branch();
                        return;
                    }
                    let unit = self.arg_cache.on_entry(0);
                    let ok = ctrl.resolve_arg(0) == unit &&
                        ctrl.resolve_arg_u8(1)
                            .if_mem8_offset(E::struct_layouts().unit_player()) == Some(unit) &&
                        ctrl.resolve_arg_u8(5) == ctx.const_0() &&
                        ctrl.resolve_arg_u8(6) == ctx.const_0() &&
                        ctrl.resolve_arg_u8(7) == ctx.const_1() &&
                        ctrl.resolve_arg_u8(8) == ctx.const_0();
                    if ok {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.result.update_building_placement_state = Some(dest);
                            self.state = PlaceBuildingState::Switch;
                            ctrl.clear_unchecked_branches();
                        }
                    }
                }
            }
            PlaceBuildingState::Switch => {
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        let switch = CompleteSwitch::new(to, ctx, ctrl.exec_state());
                        if let Some(switch) = switch {
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x9c) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = PlaceBuildingState::FindNearest;
                            }
                        }
                    }
                }
            }
            PlaceBuildingState::FindNearest => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg(0);
                        let a2 = ctrl.resolve_arg(1);
                        let unit = self.arg_cache.on_entry(0);
                        let pos_xy = self.arg_cache.on_entry(2);
                        let ok = ctx.and_const(a1, 0xffff) == ctx.and_const(pos_xy, 0xffff) &&
                            ctx.and_const(a2, 0xffff) ==
                                ctx.and_const(ctx.rsh_const(pos_xy, 0x10), 0xffff) &&
                            ctrl.resolve_arg_u8(4)
                                .if_mem8_offset(E::struct_layouts().unit_player()) == Some(unit);
                        if ok {
                            self.result.find_nearest_unit_in_area_point = Some(dest);
                            self.state = PlaceBuildingState::AiUpdatePlacement;
                            if self.inline_depth != 0 {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                        let inline = self.inline_depth == 0 &&
                            a1.if_mem8_offset(E::struct_layouts().unit_player()) == Some(unit) &&
                            ctx.and_const(a2, 0xffff_ffff) == ctx.and_const(pos_xy, 0xffff_ffff);
                        if inline {
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                        }
                    }
                }
            }
            PlaceBuildingState::AiUpdatePlacement => {
                if let Operation::Call(dest) = *op {
                    let unit = self.arg_cache.on_entry(0);
                    let radius = self.arg_cache.on_entry(4);
                    let ok = ctrl.resolve_arg_u8(2)
                            .if_mem8_offset(E::struct_layouts().unit_player()) == Some(unit) &&
                        ctrl.resolve_arg_u8(4) == ctx.and_const(radius, 0xff);
                    if ok {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.result.ai_update_building_placement_state = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}
