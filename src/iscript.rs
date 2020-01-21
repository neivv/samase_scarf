use std::rc::Rc;

use scarf::{
    ArithOpType, MemAccessSize, Operand, OperandType, OperandContext, Operation, VirtualAddress,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::ExecutionState;
use scarf::ExecutionStateX86;
use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

type BinaryFile = scarf::BinaryFile<VirtualAddress>;

use crate::{
    Analysis, ArgCache, entry_of_until, EntryOfResult, EntryOf, find_functions_using_global,
    OptionExt, single_result_assign,
};

pub struct StepIscript {
    pub step_fn: Option<VirtualAddress>,
    pub script_operand_at_switch: Option<Rc<Operand>>,
    pub switch_table: Option<VirtualAddress>,
    pub iscript_bin: Option<Rc<Operand>>,
    pub opcode_check: Option<(VirtualAddress, u32)>,
}

// Note that this returns the `*const u8` script pointer, which can be a local and differ from
// what the iscript structure has, as it may only be written on return
fn get_iscript_operand_from_goto(
    binary: &BinaryFile,
    ctx: &OperandContext,
    address: VirtualAddress,
) -> Option<Rc<Operand>> {
    // Goto should just read mem16[x], or possibly do a single x + 2 < y compare first
    struct Analyzer {
        is_first_branch: bool,
        is_inlining: bool,
        result: Option<Rc<Operand>>,
    }
    impl<'exec> scarf::Analyzer<'exec> for Analyzer {
        type State = analysis::DefaultState;
        type Exec = scarf::ExecutionStateX86<'exec>;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
            match *op {
                Operation::Move(_, ref from, None) => {
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
                Operation::Call(ref dest) => {
                    if self.is_inlining {
                        ctrl.end_analysis();
                        return;
                    }
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
                        if self.result.is_some() {
                            ctrl.end_analysis();
                            return;
                        }
                        self.is_inlining = false;
                    }
                }
                Operation::Jump { ref condition, .. } => {
                    if !self.is_first_branch {
                        // Didn't find anything quickly, give up
                        ctrl.end_analysis();
                        return;
                    }
                    let condition = ctrl.resolve(&condition);
                    let compare = condition.iter_no_mem_addr()
                        .filter_map(|x| x.if_arithmetic(ArithOpType::GreaterThan))
                        .filter_map(|(l, r)| Operand::either(l, r, |x| match x.ty {
                            OperandType::Arithmetic(ref arith) => match arith.ty {
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

    let mut analyzer = Analyzer {
        is_first_branch: true,
        is_inlining: false,
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, address);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

pub fn step_iscript<'a>(
    analysis: &mut Analysis<'a, ExecutionStateX86<'a>>,
    ctx: &OperandContext,
) -> StepIscript {
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let switch_tables = analysis.switch_tables();
    let switches = switch_tables.iter().filter_map(|switch| {
        let cases = &switch.cases;
        if cases.len() < 0x40 {
            return None;
        }
        get_iscript_operand_from_goto(binary, ctx, cases[0x7]).map(|x| (x, switch))
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
                let mut analyzer = IscriptFromSwitchAnalyzer {
                    switch_addr: switch.address,
                    iscript_bin: None,
                    opcode_check: None,
                    result: EntryOf::Retry,
                    wait_check_seen: false,
                    arg1: {
                        use scarf::operand_helpers::*;
                        Operand::simplified(mem32(operand_add(ctx.const_4(), ctx.register(4))))
                    }
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

struct IscriptFromSwitchAnalyzer {
    switch_addr: VirtualAddress,
    iscript_bin: Option<Rc<Operand>>,
    result: EntryOf<(Option<Rc<Operand>>, Option<(VirtualAddress, u32)>)>,
    wait_check_seen: bool,
    arg1: Rc<Operand>,
    opcode_check: Option<(VirtualAddress, u32)>,
}

impl<'exec> scarf::Analyzer<'exec> for IscriptFromSwitchAnalyzer {
    type State = analysis::DefaultState;
    type Exec = ExecutionStateX86<'exec>;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
        match *op {
            Operation::Move(_, ref val, None) => {
                if self.iscript_bin.is_none() {
                    let val = ctrl.resolve(&val);
                    let iscript_bin = val.if_mem8()
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_either_other(|x| {
                            x.if_mem16().filter(|x| x.if_arithmetic_add().is_some())
                        })
                        .cloned();
                    if let Some(iscript_bin) = iscript_bin {
                        self.iscript_bin = Some(iscript_bin);
                    }
                }
            }
            Operation::Jump { ref condition, ref to } => {
                let to = ctrl.resolve(&to);
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
                let condition = ctrl.resolve(&condition);
                let has_wait_check = condition.iter_no_mem_addr()
                    .filter_map(|x| x.if_mem8())
                    .filter_map(|x| x.if_arithmetic_add())
                    .filter_map(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                    .filter(|&(c, other)| c == 7 && *other == self.arg1)
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
                        let len = (ctrl.current_instruction_end() - ctrl.address()).0;
                        self.opcode_check = Some((ctrl.address(), len));
                    }
                }
            }
            _ => ()
        }
    }
}

pub fn add_overlay_iscript<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
) -> Option<VirtualAddress> {
    let iscript = analysis.step_iscript();
    let ctx = &OperandContext::new();
    let binary = analysis.binary;
    // Search for a 5-argument fn(img, sprite (Mem32[x + 3c]), x, y, 1) from
    // iscript opcode 8 (imgol)
    // Sprite is actually unused, but checking for it anyway as the function signature
    // changing isn't anticipated.
    let switch_table = iscript.switch_table?;
    let case_8 = binary.read_address(switch_table + VirtualAddress::SIZE * 8).ok()?;

    let mut analyzer = AddOverlayAnalyzer::<ExecutionStateX86<'_>> {
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
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        let word_size = <Exec::VirtualAddress as VirtualAddressTrait>::SIZE;
        match op {
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
                    let arg5 = ctrl.resolve(&self.args.on_call(4));
                    let arg5_ok = arg5
                        .if_constant()
                        .filter(|&c| c == 1)
                        .is_some();
                    if !arg5_ok {
                        return;
                    }
                    let arg2 = ctrl.resolve(&self.args.on_call(1));
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
