use scarf::{
    ArithOpType, MemAccessSize, Operand, OperandType, OperandCtx, Operation, BinaryFile,
    DestOperand,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::ExecutionState;
use scarf::exec_state::VirtualAddress;

use crate::{
    Analysis, ArgCache, entry_of_until, EntryOfResult, EntryOf, find_functions_using_global,
    OptionExt, single_result_assign,
};

pub struct StepIscript<'e, Va: VirtualAddress> {
    pub step_fn: Option<Va>,
    pub script_operand_at_switch: Option<Operand<'e>>,
    pub switch_table: Option<Va>,
    pub iscript_bin: Option<Operand<'e>>,
    pub opcode_check: Option<(Va, u32)>,
}

// Note that this returns the `*const u8` script pointer, which can be a local and differ from
// what the iscript structure has, as it may only be written on return
fn get_iscript_operand_from_goto<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    address: E::VirtualAddress,
) -> Option<Operand<'e>> {
    // Goto should just read mem16[x], or possibly do a single x + 2 < y compare first
    struct Analyzer<'e, F: ExecutionState<'e>> {
        is_first_branch: bool,
        is_inlining: bool,
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<*const F>,
    }
    impl<'e, F: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match *op {
                Operation::Move(_, from, None) => {
                    if let Some(mem) = from.if_memory() {
                        if mem.size == MemAccessSize::Mem16 {
                            self.result = Some(mem.address.clone());
                            // Don't end on first branch if this is part of x + 2 < y comparision
                            if !self.is_first_branch {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                    }
                }
                Operation::Call(dest) => {
                    if self.is_inlining {
                        ctrl.end_analysis();
                        return;
                    }
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, F::VirtualAddress::from_u64(dest));
                        if self.result.is_some() {
                            ctrl.end_analysis();
                            return;
                        }
                        self.is_inlining = false;
                    }
                }
                Operation::Jump { condition, .. } => {
                    if !self.is_first_branch {
                        // Didn't find anything quickly, give up
                        ctrl.end_analysis();
                        return;
                    }
                    let condition = ctrl.resolve(condition);
                    let compare = condition.iter_no_mem_addr()
                        .filter_map(|x| x.if_arithmetic(ArithOpType::GreaterThan))
                        .filter_map(|(l, r)| Operand::either(l, r, |x| match x.ty() {
                            OperandType::Arithmetic(arith) => match arith.ty {
                                ArithOpType::Add | ArithOpType::Sub => Some(x),
                                _ => None,
                            },
                            _ => None,
                        }))
                        .filter_map(|(a, b)| Operand::either(a, b, |x| x.if_constant()))
                        .filter(|&(c, _)| c == 2)
                        .next();
                    if compare.is_none() {
                        // Not a condition that was expected
                        ctrl.end_analysis();
                        return;
                    }
                    self.is_first_branch = false;
                }
                _ => ()
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        is_first_branch: true,
        is_inlining: false,
        result: None,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, address);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub fn step_iscript<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> StepIscript<'e, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let switch_tables = analysis.switch_tables();
    let switches = switch_tables.iter().filter_map(|switch| {
        let cases = &switch.cases;
        if cases.len() < 0x40 {
            return None;
        }
        get_iscript_operand_from_goto::<E>(binary, ctx, cases[0x7]).map(|x| (x, switch))
    });
    let mut result = StepIscript {
        step_fn: None,
        script_operand_at_switch: None,
        switch_table: None,
        iscript_bin: None,
        opcode_check: None,
    };
    'outer: for (script_operand, switch) in switches {
        let users = find_functions_using_global(analysis, switch.address);
        for user in users {
            let func_result = entry_of_until(binary, funcs, user.func_entry, |entry| {
                let arg_cache = &analysis.arg_cache;
                let mut analyzer = IscriptFromSwitchAnalyzer {
                    switch_addr: switch.address,
                    iscript_bin: None,
                    opcode_check: None,
                    result: EntryOf::Retry,
                    wait_check_seen: false,
                    arg_cache,
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                analyzer.result
            });
            if let EntryOfResult::Ok(entry, (iscript_bin, opcode_check)) = func_result {
                if crate::test_assertions() {
                    if let Some(step) = result.step_fn {
                        assert_eq!(step, entry);
                    }
                    if let Some(ref op) = result.script_operand_at_switch {
                        assert_eq!(*op, script_operand);
                    }
                    if let Some(ref op) = result.opcode_check {
                        if let Some(ref new) = opcode_check {
                            assert_eq!(op, new);
                        }
                    }
                    if let Some(ref op) = result.iscript_bin {
                        if let Some(ref new) = iscript_bin {
                            assert_eq!(op, new);
                        }
                    }
                }
                result.step_fn = Some(entry);
                result.script_operand_at_switch = Some(script_operand.clone());
                result.iscript_bin = iscript_bin;
                result.opcode_check = opcode_check;
                result.switch_table = Some(switch.address);
                if !crate::test_assertions() {
                    break 'outer;
                }
            }
        }
    }
    result
}

struct IscriptFromSwitchAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    switch_addr: E::VirtualAddress,
    iscript_bin: Option<Operand<'e>>,
    result: EntryOf<(Option<Operand<'e>>, Option<(E::VirtualAddress, u32)>)>,
    wait_check_seen: bool,
    arg_cache: &'a ArgCache<'e, E>,
    opcode_check: Option<(E::VirtualAddress, u32)>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for IscriptFromSwitchAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(_, val, None) => {
                if self.iscript_bin.is_none() {
                    let val = ctrl.resolve(val);
                    let iscript_bin = val.if_mem8()
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_either_other(|x| {
                            x.if_mem16().filter(|x| x.if_arithmetic_add().is_some())
                        });
                    if let Some(iscript_bin) = iscript_bin {
                        self.iscript_bin = Some(iscript_bin);
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let to = ctrl.resolve(to);
                let is_switch_jump = to.iter().any(|x| match x.if_constant() {
                    Some(s) => s == self.switch_addr.as_u64(),
                    None => false,
                });
                if is_switch_jump {
                    self.result = match self.wait_check_seen {
                        false => EntryOf::Stop,
                        true => EntryOf::Ok((self.iscript_bin.take(), self.opcode_check.take())),
                    };
                    ctrl.end_analysis();
                    return;
                }
                let condition = ctrl.resolve(condition);
                let has_wait_check = condition.iter_no_mem_addr()
                    .filter_map(|x| x.if_mem8())
                    .filter_map(|x| x.if_arithmetic_add())
                    .filter_map(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                    .filter(|&(c, other)| c == 7 && other == self.arg_cache.on_entry(0))
                    .next().is_some();
                if has_wait_check {
                    self.wait_check_seen = true;
                }
                if self.wait_check_seen {
                    let has_opcode_limit_constant = condition.iter_no_mem_addr()
                        .any(|x| x.if_constant().filter(|&c| c == 0x44 || c == 0x45).is_some());
                    let has_mem8 = condition.iter_no_mem_addr()
                        .any(|x| x.if_mem8().is_some());
                    if has_opcode_limit_constant && has_mem8 {
                        let len =
                            ctrl.current_instruction_end().as_u64() - ctrl.address().as_u64();
                        self.opcode_check = Some((ctrl.address(), len as u32));
                    }
                }
            }
            _ => ()
        }
    }
}

pub fn add_overlay_iscript<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let iscript = analysis.step_iscript();
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // Search for a 5-argument fn(img, sprite (Mem32[x + 3c]), x, y, 1) from
    // iscript opcode 8 (imgol)
    // Sprite is actually unused, but checking for it anyway as the function signature
    // changing isn't anticipated.
    let switch_table = iscript.switch_table?;
    let word_size = <E::VirtualAddress as VirtualAddress>::SIZE;
    let case_8 = binary.read_address(switch_table + word_size * 8).ok()?;

    let mut analyzer = AddOverlayAnalyzer::<E> {
        result: None,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, case_8);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AddOverlayAnalyzer<'exec, 'b, Exec: ExecutionState<'exec>> {
    result: Option<Exec::VirtualAddress>,
    args: &'b ArgCache<'exec, Exec>,
}

impl<'e, 'b, Exec: ExecutionState<'e>> scarf::Analyzer<'e> for AddOverlayAnalyzer<'e, 'b, Exec> {
    type State = analysis::DefaultState;
    type Exec = Exec;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let word_size = <Exec::VirtualAddress as VirtualAddress>::SIZE;
        match *op {
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                let is_switch_jump = to.if_memory().is_some();
                if is_switch_jump {
                    ctrl.end_branch();
                    return;
                }
            }
            Operation::Call(to) => {
                let to = ctrl.resolve(to);
                if let Some(dest) = to.if_constant() {
                    let arg5 = ctrl.resolve(self.args.on_call(4));
                    let arg5_ok = arg5
                        .if_constant()
                        .filter(|&c| c == 1)
                        .is_some();
                    if !arg5_ok {
                        return;
                    }
                    let arg2 = ctrl.resolve(self.args.on_call(1));
                    // TODO not 64-bit since not sure about image->parent pointer
                    let arg2_ok = if word_size == 4 {
                        arg2
                            .if_mem32()
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either(|x| x.if_constant().filter(|&c| c == 0x3c))
                            .is_some()
                    } else {
                        unimplemented!();
                    };
                    if !arg2_ok {
                        return;
                    }

                    let result = Some(Exec::VirtualAddress::from_u64(dest));
                    if single_result_assign(result, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub fn draw_cursor_marker<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let iscript = analysis.step_iscript();
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // hide_cursor_marker is iscript opcode 0x2d
    let cases = iscript.switch_table?;
    let case =
        binary.read_address(cases + 0x2d * <E::VirtualAddress as VirtualAddress>::SIZE).ok()?;

    let mut analyzer = FindDrawCursorMarker::<E> {
        result: None,
        inlining: false,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, case);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindDrawCursorMarker<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDrawCursorMarker<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { to, .. } => {
                if to.if_constant().is_none() {
                    // Skip switch branch
                    ctrl.end_branch();
                }
            }
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, E::VirtualAddress::from_u64(dest));
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    ctrl.end_analysis();
                }
            }
            Operation::Move(ref dest, val, None) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem8 {
                        let val = ctrl.resolve(val);
                        if val.if_constant() == Some(0) {
                            let ctx = ctrl.ctx();
                            self.result = Some(ctx.mem_variable_rc(mem.size, mem.address));
                            ctrl.end_analysis();
                        }
                    }
                }
                if self.inlining {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}
