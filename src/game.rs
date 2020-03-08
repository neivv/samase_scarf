use std::rc::Rc;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, OperandContext, Operand, DestOperand, Operation, MemAccessSize};

use crate::{
    Analysis, OptionExt, find_functions_using_global, find_callers, EntryOf,
    single_result_assign, if_callable_const, entry_of_until,
};

pub fn step_objects<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    // step_objects calls enable_rng(1) at start and enable_rng(0) at end,
    // detect both inlined writes (though untested, welp) and calls
    // Detect step_objects itself by searching for code that writes both
    // 0x64 and [x] - 1 to [x]; x is vision update counter.
    let rng = analysis.rng();
    let rng_enable = rng.enable.as_ref()?;
    // Use addresses of RNG or call location addresses of RNG set func
    let mut rng_refs = Vec::with_capacity(16);
    for part in rng_enable.iter_no_mem_addr() {
        if let Some(enable_addr) = part.if_memory().and_then(|x| x.address.if_constant()) {
            let enable_addr = E::VirtualAddress::from_u64(enable_addr);
            let globals = find_functions_using_global(analysis, enable_addr);
            for global_ref in globals {
                if is_branchless_leaf(analysis, global_ref.func_entry) {
                    rng_refs.extend(find_callers(analysis, global_ref.func_entry));
                } else {
                    rng_refs.push(global_ref.use_address);
                }
            }
        }
    }
    rng_refs.sort();
    rng_refs.dedup();
    let mut checked_vision_funcs = Vec::new();
    let mut result = None;
    let funcs = analysis.functions();
    let funcs = &funcs[..];
    let ctx = analysis.ctx;
    let mut checked_functions = Vec::with_capacity(8);
    'outer: for &first_candidate_only in &[true, false] {
        for &addr in &rng_refs {
            let res = entry_of_until(binary, funcs, addr, |entry| {
                let mut analyzer: IsStepObjects<E> = IsStepObjects {
                    vision_state: VisionStepState::new(),
                    checked_vision_funcs: &mut checked_vision_funcs,
                    binary,
                    ctx,
                    result: EntryOf::Retry,
                    rng_ref_address: addr,
                    rng_ref_seen: false,
                };
                if !checked_functions.iter().any(|&x| x == entry) {
                    checked_functions.push(entry);
                    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                    analysis.analyze(&mut analyzer);
                }
                if first_candidate_only {
                    if let EntryOf::Retry = analyzer.result {
                        analyzer.result = EntryOf::Stop;
                    }
                }
                analyzer.result
            }).into_option_with_entry().map(|x| x.0);
            if single_result_assign(res, &mut result) {
                break 'outer;
            }
        }
    }
    result
}

struct IsStepObjects<'a, 'e, E: ExecutionState<'e>> {
    vision_state: VisionStepState,
    checked_vision_funcs: &'a mut Vec<(E::VirtualAddress, bool)>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: &'e OperandContext,
    result: EntryOf<()>,
    // Can either be mem access or call
    rng_ref_address: E::VirtualAddress,
    // rng enable is the first call (or inlinied), if not seen by first call
    // should stop.
    rng_ref_seen: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsStepObjects<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                self.check_rng_ref(ctrl);
                if !self.rng_ref_seen {
                    ctrl.end_analysis();
                    return;
                }
                if let Some(dest) = if_callable_const(self.binary, dest, ctrl) {
                    let cached = self.checked_vision_funcs.iter()
                        .find(|x| x.0 == dest)
                        .map(|x| x.1);
                    let is = match cached {
                        Some(is) => is,
                        None => {
                            let is = is_vision_step_func::<E>(self.binary, self.ctx, dest);
                            self.checked_vision_funcs.push((dest, is));
                            is
                        }
                    };
                    if is {
                        self.result = EntryOf::Ok(());
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Move(dest, val, _cond) => {
                self.check_rng_ref(ctrl);
                self.vision_state.update(dest, &ctrl.resolve(val));
                if self.vision_state.is_ok() {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> IsStepObjects<'a, 'e, E> {
    fn check_rng_ref(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if !self.rng_ref_seen {
            let ok = self.rng_ref_address >= ctrl.address() &&
                self.rng_ref_address < ctrl.current_instruction_end();
            if ok {
                self.rng_ref_seen = true;
            }
        }
    }
}

fn is_branchless_leaf<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    addr: E::VirtualAddress,
) -> bool {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: bool,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }
    impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    self.result = false;
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }

    let ctx = analysis.ctx;
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, addr);
    let mut analyzer: Analyzer<E> = Analyzer {
        result: true,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn is_vision_step_func<'e, E: ExecutionState<'e>>(
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: &'e OperandContext,
    addr: E::VirtualAddress,
) -> bool {
    let mut analysis = FuncAnalysis::new(binary, ctx, addr);
    let mut analyzer: IsVisionStepFunc<E> = IsVisionStepFunc {
        vision_state: VisionStepState::new(),
        jump_limit: 10,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.vision_state.is_ok()
}

struct IsVisionStepFunc<'e, E: ExecutionState<'e>> {
    jump_limit: u8,
    vision_state: VisionStepState,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for IsVisionStepFunc<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(..) => {
                ctrl.end_analysis();
            }
            Operation::Jump { .. } => {
                self.jump_limit -= 1;
                if self.jump_limit == 0 {
                    ctrl.end_analysis();
                }
            }
            Operation::Move(ref dest, ref val, ref _cond) => {
                self.vision_state.update(dest, &ctrl.resolve(val));
                if self.vision_state.is_ok() {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

/// For step_objects detection
#[derive(Debug)]
struct VisionStepState {
    store_64_seen: bool,
    store_sub_seen: bool,
}

impl VisionStepState {
    fn new() -> VisionStepState {
        VisionStepState {
            store_64_seen: false,
            store_sub_seen: false,
        }
    }

    fn is_ok(&self) -> bool {
        self.store_64_seen && self.store_sub_seen
    }

    /// `val` must be resolved
    fn update(&mut self, dest: &DestOperand, val: &Rc<Operand>) {
        if let DestOperand::Memory(ref mem) = *dest {
            if mem.size == MemAccessSize::Mem32 {
                if let Some(_addr) = mem.address.if_constant() {
                    if val.if_constant() == Some(0x64) {
                        self.store_64_seen = true;
                    } else {
                        let sub_self_1 = {
                            val.if_arithmetic_add()
                                .and_either_other(|x| {
                                    x.if_constant().filter(|&c| c as u32 == u32::max_value())
                                })
                                .and_then(|other| other.if_memory())
                                .filter(|other| *other == mem)
                                .is_some()
                        } || {
                            val.if_arithmetic_sub()
                                .filter(|(l, r)| {
                                    r.if_constant() == Some(1) &&
                                        l.if_memory().filter(|m| *m == mem).is_some()
                                }).is_some()
                        };
                        if sub_self_1 {
                            self.store_sub_seen = true;
                        }
                    }
                }
            }
        }
    }
}

pub fn game<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Rc<Operand>> {
    let step_objects = analysis.step_objects()?;
    let binary = analysis.binary;

    let ctx = analysis.ctx;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    let mut analyzer: FindGame<E> = FindGame {
        call_depth: 0,
        jump_limit: 0,
        result: None,
        binary,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindGame<'e, E: ExecutionState<'e>> {
    call_depth: u8,
    jump_limit: u8,
    result: Option<Rc<Operand>>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindGame<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                if self.call_depth < 3 {
                    if let Some(dest) = if_callable_const(self.binary, dest, ctrl) {
                        let jump_limit = self.jump_limit;
                        self.jump_limit = 3;
                        self.call_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.call_depth -= 1;
                        self.jump_limit = jump_limit;
                        if self.result.is_some() && !crate::test_assertions() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Jump { .. } => {
                if self.call_depth > 0 {
                    self.jump_limit = self.jump_limit.wrapping_sub(1);
                    if self.jump_limit == 0 {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Move(_dest, val, _cond) => {
                let val = ctrl.resolve(val);
                let val = game_detect_check(ctrl.ctx(), &val);
                if single_result_assign(val, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

fn game_detect_check(ctx: &OperandContext, val: &Rc<Operand>) -> Option<Rc<Operand>> {
    // Check for map_width_tiles * map_height_tiles, at UpdateFog or ProgressCreepDisappearance
    // (They're at game + 0xe4 and game + 0xe6)
    val.iter_no_mem_addr().filter_map(|x| x.if_arithmetic_mul())
        .filter_map(|(l, r)| {
            l.if_memory().and_then(|l| r.if_memory().map(|r| (l, r)))
        }).filter(|&(l, r)| {
            l.size == MemAccessSize::Mem16 && r.size == MemAccessSize::Mem16
        }).filter_map(|(l, r)| {
            let l_minus_2 = ctx.sub_const(&l.address, 2);
            if l_minus_2 == r.address {
                Some(ctx.sub_const(&r.address, 0xe4))
            } else {
                let r_minus_2 = ctx.sub_const(&r.address, 2);
                if r_minus_2 == l.address {
                    Some(ctx.sub_const(&l.address, 0xe4))
                } else {
                    None
                }
            }
        }).next()
}
