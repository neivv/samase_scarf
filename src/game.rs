use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, OperandCtx, Operand, DestOperand, Operation, MemAccessSize};

use crate::{
    AnalysisCtx, OptionExt, find_functions_using_global, find_callers, EntryOf,
    single_result_assign, if_callable_const, entry_of_until, ArgCache,
};

#[derive(Clone)]
pub struct Limits<'e, Va: VirtualAddress> {
    pub set_limits: Option<Va>,
    // These are vector<Object>, unlike sprites/units elsewhere which
    // are Object pointer (These are `x` where sprites/units would be `Mem32[x]`)
    // Also multiple arrays, no guarantees about which one is primary and which are auxillary
    //
    // First set of arrays is for limit struct offset 0 (images)
    // second for offset 4 (sprites)
    // and so on
    //
    // First u32 is addition, second multiplier
    // (Some sprite arrays are resized to sprite_count + 1,
    // unit arrays to unit_count * 2)
    pub arrays: Vec<Vec<(Operand<'e>, u32, u32)>>,
    pub smem_alloc: Option<Va>,
    pub smem_free: Option<Va>,
}

pub(crate) fn step_objects<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
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
    rng_refs.sort_unstable();
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
    ctx: OperandCtx<'e>,
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
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
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
            Operation::Move(ref dest, val, _cond) => {
                self.check_rng_ref(ctrl);
                self.vision_state.update(dest, ctrl.resolve(val));
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
    analysis: &mut AnalysisCtx<'_, 'e, E>,
    addr: E::VirtualAddress,
) -> bool {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: bool,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }
    impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
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
    ctx: OperandCtx<'e>,
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
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(..) => {
                ctrl.end_analysis();
            }
            Operation::Jump { .. } => {
                self.jump_limit -= 1;
                if self.jump_limit == 0 {
                    ctrl.end_analysis();
                }
            }
            Operation::Move(ref dest, val, _cond) => {
                self.vision_state.update(dest, ctrl.resolve(val));
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
    fn update<'e>(&mut self, dest: &DestOperand<'e>, val: Operand<'e>) {
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

pub(crate) fn game<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<Operand<'e>> {
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
    result: Option<Operand<'e>>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindGame<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
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
            Operation::Move(_, val, _cond) => {
                let val = ctrl.resolve(val);
                let val = game_detect_check(ctrl.ctx(), val);
                if single_result_assign(val, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

fn game_detect_check<'e>(ctx: OperandCtx<'e>, val: Operand<'e>) -> Option<Operand<'e>> {
    // Check for map_width_tiles * map_height_tiles, at UpdateFog or ProgressCreepDisappearance
    // (They're at game + 0xe4 and game + 0xe6)
    val.iter_no_mem_addr().filter_map(|x| x.if_arithmetic_mul())
        .filter_map(|(l, r)| {
            l.if_memory().and_then(|l| r.if_memory().map(|r| (l, r)))
        }).filter(|&(l, r)| {
            l.size == MemAccessSize::Mem16 && r.size == MemAccessSize::Mem16
        }).filter_map(|(l, r)| {
            let l_minus_2 = ctx.sub_const(l.address, 2);
            if l_minus_2 == r.address {
                Some(ctx.sub_const(r.address, 0xe4))
            } else {
                let r_minus_2 = ctx.sub_const(r.address, 2);
                if r_minus_2 == l.address {
                    Some(ctx.sub_const(l.address, 0xe4))
                } else {
                    None
                }
            }
        }).next()
}

pub(crate) fn limits<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Limits<'e, E::VirtualAddress> {
    let mut result = Limits {
        set_limits: None,
        arrays: Vec::with_capacity(7),
        smem_alloc: None,
        smem_free: None,
    };
    let game_loop = match analysis.game_init().game_loop {
        Some(s) => s,
        None => return result,
    };

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;

    let mut analysis = FuncAnalysis::new(binary, ctx, game_loop);
    let mut analyzer = FindSetLimits::<E> {
        result: &mut result,
        arg_cache,
        game_loop_set_local_u32s: Vec::with_capacity(0x20),
        binary,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct FindSetLimits<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut Limits<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    // Bits describing if a stack local has been written
    // [0] & 0x1 == esp - 0
    // [0] & 0x2 == esp - 4
    // [0] & 0x4 == esp - 8
    // [0] & 0x80 == esp - 1c
    // [1] & 0x1 == esp - 20
    // ...
    // So index = offset / 0x20
    // bit = (offset & 0x1f) / 4
    // Used to check that set_limits should contain stack local with
    // 7 u32s written
    game_loop_set_local_u32s: Vec<u8>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

struct SetLimitsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut Limits<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    inlining_object_subfunc: bool,
    // Set once inside Vec::resize, for finding SMemAlloc and SMemFree
    // (Trying this for images only)
    check_malloc_free: bool,
    // If detecting inlined resize, the function has to be redone
    redo_check_malloc_free: bool,
    func_initial_esp: Operand<'e>,
    // The code does both `global_limits = arg1` and `global_limits = default_limits()`
    // at set_limits (inline_depth == 0)
    // We want to behave as if global_limits was only assigned arg1, so keep any
    // global arg1 stores saved and force-reapply them on function calls
    depth_0_arg1_global_stores: Vec<(Operand<'e>, Operand<'e>)>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindSetLimits<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn esp_offset<'e>(val: Operand<'e>) -> Option<u32> {
            val.if_arithmetic_sub()
                .filter(|&(l, _)| {
                    // Allow esp - x and
                    // ((esp - y) & 0xffff_fff0) - x
                    l.if_register().filter(|r| r.0 == 4).is_some() ||
                        l.if_arithmetic_and()
                            .filter(|&(_, r)| r.if_constant().is_some())
                            .and_then(|(l, _)| {
                                l.if_arithmetic_sub()
                                    .filter(|&(_, r)| r.if_constant().is_some())
                                    .and_then(|(l, _)| l.if_register())
                                    .or_else(|| l.if_register())
                                    .filter(|r| r.0 == 4)
                            })
                            .is_some()
                })
                .and_then(|(_, r)| r.if_constant())
                .map(|c| c as u32)
        }

        match *op {
            Operation::Call(dest) => {
                let dest = match ctrl.resolve(dest).if_constant() {
                    Some(s) => E::VirtualAddress::from_u64(s),
                    None => return,
                };
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                if let Some(offset) = esp_offset(arg1).filter(|&x| x >= 6 * 4) {
                    let u32_offset = offset / 4;
                    if (0..7).all(|i| self.is_local_u32_set(u32_offset - i)) {
                        let ctx = ctrl.ctx();
                        let mut analysis = FuncAnalysis::new(self.binary, ctx, dest);
                        let mut analyzer = SetLimitsAnalyzer::<E> {
                            result: self.result,
                            arg_cache: self.arg_cache,
                            inline_depth: 0,
                            func_initial_esp: ctx.register(4),
                            inlining_object_subfunc: false,
                            check_malloc_free: false,
                            redo_check_malloc_free: false,
                            depth_0_arg1_global_stores: Vec::with_capacity(0x10),
                        };
                        analysis.analyze(&mut analyzer);
                        let ok = self.result.arrays.iter().take(4).all(|x| !x.is_empty()) &&
                            self.result.arrays.len() >= 4;
                        if ok {
                            self.result.set_limits = Some(dest);
                            for arr in &mut self.result.arrays {
                                arr.sort_unstable();
                                arr.dedup();
                            }
                            ctrl.end_analysis();
                        } else {
                            self.result.arrays.clear();
                        }
                    } else {
                        // Maybe a func which writes to arg1?
                        for i in 0..7 {
                            self.set_local_u32(u32_offset - i);
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), _, _) => {
                let dest = ctrl.resolve(mem.address);
                if let Some(offset) = esp_offset(dest) {
                    let u32_offset = offset / 4;
                    self.set_local_u32(u32_offset);
                    if mem.size == MemAccessSize::Mem64 {
                        self.set_local_u32(u32_offset + 1);
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindSetLimits<'a, 'e, E> {
    fn is_local_u32_set(&self, offset: u32) -> bool {
        let index = offset / 8;
        let bit = offset & 7;
        self.game_loop_set_local_u32s
            .get(index as usize)
            .cloned()
            .map(|bits| bits & (1 << bit) != 0)
            .unwrap_or(false)
    }

    fn set_local_u32(&mut self, offset: u32) {
        let index = (offset / 8) as usize;
        let bit = offset & 7;
        if self.game_loop_set_local_u32s.len() <= index {
            self.game_loop_set_local_u32s.resize(index + 1, 0u8);
        }
        self.game_loop_set_local_u32s[index] |= 1 << bit;
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for SetLimitsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let dest = match ctrl.resolve(dest).if_constant() {
                    Some(s) => E::VirtualAddress::from_u64(s),
                    None => return,
                };
                let ctx = ctrl.ctx();
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let ecx = ctrl.resolve(ctx.register(1));
                let mut inline = false;
                if self.check_malloc_free {
                    // Note: Assuming this is inside image vector resize.
                    // alloc image_count * 0x40
                    let is_alloc = arg1.if_arithmetic(scarf::ArithOpType::Lsh)
                        .and_then(|(_, r)| r.if_constant())
                        .filter(|&c| c == 6)
                        .is_some();
                    if is_alloc {
                        self.result.smem_alloc = Some(dest);
                        return;
                    }
                    let is_free = arg1.if_memory()
                        .and_then(|mem| {
                            Some(mem.address == self.result.arrays.get(0)?.get(0)?.0)
                        })
                        .unwrap_or(false);
                    if is_free {
                        self.result.smem_free = Some(dest);
                        return;
                    }
                }
                if let Some((off, add, mul)) = self.arg1_off(arg1) {
                    if ecx.if_constant().is_some() {
                        if off & 3 != 0 {
                            self.result.arrays.clear();
                            ctrl.end_analysis();
                            return;
                        }
                        self.add_result(off, add, mul, ecx);
                        // off == 0 => images
                        if self.result.smem_alloc.is_none() && off == 0 {
                            self.check_malloc_free = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.check_malloc_free = false;
                        }
                    } else {
                        inline = true;
                    }
                }
                if self.check_malloc_free && ecx.if_constant().is_some() {
                    inline = true;
                }
                if inline || self.inline_depth == 0 {
                    if self.inline_depth < 3 {
                        let exec_state = ctrl.exec_state();
                        if self.inline_depth == 0 {
                            for &(dest, value) in &self.depth_0_arg1_global_stores {
                                exec_state.move_resolved(
                                    &DestOperand::Memory(scarf::operand::MemAccess {
                                        size: MemAccessSize::Mem32,
                                        address: dest,
                                    }),
                                    value,
                                );
                            }
                        }

                        self.inline_depth += 1;
                        let was_inlining_object_subfunc = self.inlining_object_subfunc;
                        let was_checking_malloc_free = self.check_malloc_free;
                        self.inlining_object_subfunc = inline;
                        let esp = self.func_initial_esp;
                        let ctx = ctrl.ctx();
                        self.func_initial_esp = ctx.sub_const(
                            ctrl.resolve(ctx.register(4)),
                            E::VirtualAddress::SIZE as u64,
                        );
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining_object_subfunc = was_inlining_object_subfunc;
                        self.check_malloc_free = was_checking_malloc_free;
                        self.func_initial_esp = esp;
                        self.inline_depth -= 1;
                        if self.redo_check_malloc_free {
                            self.redo_check_malloc_free = false;
                            self.check_malloc_free = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.check_malloc_free = was_checking_malloc_free;
                        }
                    }
                }
            }
            Operation::Move(ref dest, value, None) => {
                match dest {
                    DestOperand::Register64(reg) => {
                        if reg.0 == 5 && value.if_memory().is_some() {
                            // Make pop ebp always be mov esp, orig_esp
                            // even if current esp is considered unknown
                            let ctx = ctrl.ctx();
                            let exec_state = ctrl.exec_state();
                            exec_state.move_resolved(
                                &DestOperand::Register64(scarf::operand::Register(4)),
                                ctx.sub_const(
                                    self.func_initial_esp,
                                    E::VirtualAddress::SIZE as u64,
                                ),
                            );
                        }
                    }
                    DestOperand::Memory(mem) if !self.redo_check_malloc_free => {
                        let value = ctrl.resolve(value);
                        // Generally vector.resize(limits.x) is caught at call
                        // but check also for inlined vector.size = limits.x
                        if let Some((off, add, mul)) = self.arg1_off(value) {
                            if off & 3 != 0 {
                                return;
                            }
                            let dest = ctrl.resolve(mem.address);
                            if dest.if_constant().is_some() {
                                if self.inlining_object_subfunc {
                                    let ctx = ctrl.ctx();
                                    let vector =
                                        ctx.sub_const(dest, E::VirtualAddress::SIZE as u64);
                                    self.add_result(off, add, mul, vector);
                                    // off == 0 => images
                                    if self.result.smem_alloc.is_none() && off == 0 {
                                        self.redo_check_malloc_free = true;
                                    }
                                } else if self.inline_depth == 0 {
                                    self.depth_0_arg1_global_stores.push((dest, value));
                                }
                            }
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> SetLimitsAnalyzer<'a, 'e, E> {
    fn arg1_off(&self, val: Operand<'e>) -> Option<(u32, u32, u32)> {
        Some(val)
            .map(|val| {
                val.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        r.if_constant().map(|c| (l, c as u32, 0))
                    })
                    .or_else(|| {
                        val.if_arithmetic_mul()
                            .and_then(|(l, r)| {
                                r.if_constant().map(|c| (l, 0, c as u32))
                            })
                    })
                    .unwrap_or_else(|| (val, 0, 0))
            })
            .and_then(|(x, add, mul)| {
                x.if_mem32()
                    .and_then(|x| {
                        let self_arg1 = self.arg_cache.on_entry(0);
                        x.if_arithmetic_add()
                            .filter(|&(l, _)| l == self_arg1)
                            .and_then(|(_, r)| r.if_constant())
                            .or_else(|| {
                                if x == self_arg1 {
                                    Some(0)
                                } else {
                                    None
                                }
                            })
                            .map(|x| (x as u32, add, mul))
                    })
            })
    }

    fn add_result(&mut self, off: u32, add: u32, mul: u32, value: Operand<'e>) {
        let index = off as usize / 4;
        let arrays = &mut self.result.arrays;
        while arrays.len() <= index {
            arrays.push(Vec::new());
        }
        arrays[index].push((value, add, mul));
    }
}
