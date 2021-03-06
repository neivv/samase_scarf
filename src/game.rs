use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, OperandCtx, Operand, DestOperand, Operation, MemAccessSize};

use crate::{
    AnalysisCtx, ControlExt, OptionExt, EntryOf, FunctionFinder, if_arithmetic_eq_neq,
    OperandExt, single_result_assign, if_callable_const, entry_of_until, ArgCache,
    bumpvec_with_capacity,
};
use crate::call_tracker::CallTracker;

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
    pub allocator: Option<Operand<'e>>,
}

pub(crate) struct StepObjectsAnalysis<'e, Va: VirtualAddress> {
    pub step_active_frame: Option<Va>,
    pub step_hidden_frame: Option<Va>,
    pub step_bullet_frame: Option<Va>,
    pub reveal_area: Option<Va>,
    pub vision_update_counter: Option<Operand<'e>>,
    pub vision_updated: Option<Operand<'e>>,
    pub first_dying_unit: Option<Operand<'e>>,
    pub first_revealer: Option<Operand<'e>>,
    pub first_invisible_unit: Option<Operand<'e>>,
    pub active_iscript_flingy: Option<Operand<'e>>,
    pub active_iscript_bullet: Option<Operand<'e>>,
}

pub(crate) fn step_objects<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    rng_enable: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let bump = &analysis.bump;
    // step_objects calls enable_rng(1) at start and enable_rng(0) at end,
    // detect both inlined writes (though untested, welp) and calls
    // Detect step_objects itself by searching for code that writes both
    // 0x64 and [x] - 1 to [x]; x is vision update counter.
    let rng_enable = rng_enable;
    // Use addresses of RNG or call location addresses of RNG set func
    let mut rng_refs = bumpvec_with_capacity(16, bump);
    for part in rng_enable.iter_no_mem_addr() {
        if let Some(enable_addr) = part.if_memory().and_then(|x| x.address.if_constant()) {
            let enable_addr = E::VirtualAddress::from_u64(enable_addr);
            let globals = functions.find_functions_using_global(analysis, enable_addr);
            for global_ref in globals {
                let entry = global_ref.func_entry;
                if is_branchless_leaf(analysis, entry) {
                    rng_refs.extend(functions.find_callers(analysis, entry));
                } else {
                    rng_refs.push(global_ref.use_address);
                }
            }
        }
    }
    rng_refs.sort_unstable();
    rng_refs.dedup();
    // Binary size trickery as sbumpalo is somewhat bad with generic bloat
    let mut checked_vision_funcs = bumpvec_with_capacity(8, bump);
    let mut result = None;
    let funcs = functions.functions();
    let ctx = analysis.ctx;
    let mut checked_functions = bumpvec_with_capacity(8, bump);
    'outer: for &first_candidate_only in &[true, false] {
        for &addr in &rng_refs {
            let res = entry_of_until(binary, funcs, addr, |entry| {
                let mut analyzer: IsStepObjects<E> = IsStepObjects {
                    vision_state: VisionStepState::new(),
                    checked_vision_funcs: &mut checked_vision_funcs,
                    binary,
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

struct IsStepObjects<'a, 'acx, 'e, E: ExecutionState<'e>> {
    vision_state: VisionStepState,
    checked_vision_funcs: &'a mut BumpVec<'acx, (E::VirtualAddress, bool)>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    result: EntryOf<()>,
    // Can either be mem access or call
    rng_ref_address: E::VirtualAddress,
    // rng enable is the first call (or inlinied), if not seen by first call
    // should stop.
    rng_ref_seen: bool,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    IsStepObjects<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
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
                            let is = is_vision_step_func::<E>(self.binary, ctx, dest);
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
            Operation::Move(ref dest, val, None) => {
                self.check_rng_ref(ctrl);
                self.vision_state.update(dest, ctrl.resolve(val), ctx);
                if self.vision_state.is_ok() {
                    self.result = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> IsStepObjects<'a, 'acx, 'e, E> {
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
    analysis: &AnalysisCtx<'e, E>,
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
                let ctx = ctrl.ctx();
                self.vision_state.update(dest, ctrl.resolve(val), ctx);
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
    fn update<'e>(&mut self, dest: &DestOperand<'e>, val: Operand<'e>, ctx: OperandCtx<'e>) {
        if let DestOperand::Memory(ref mem) = *dest {
            if mem.size == MemAccessSize::Mem32 {
                if let Some(_addr) = mem.address.if_constant() {
                    if val.if_constant() == Some(0x64) {
                        self.store_64_seen = true;
                    } else {
                        let sub_self_1 = val.if_arithmetic_and_const(0xffff_ffff)
                            .unwrap_or(val)
                            .if_arithmetic_sub()
                            .filter(|&(l, r)| {
                                r == ctx.const_1() && l.if_memory() == Some(mem)
                            }).is_some();
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
    analysis: &AnalysisCtx<'e, E>,
    step_objects: E::VirtualAddress,
) -> Option<Operand<'e>> {
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
    actx: &AnalysisCtx<'e, E>,
    game_loop: E::VirtualAddress,
) -> Limits<'e, E::VirtualAddress> {
    let mut result = Limits {
        set_limits: None,
        arrays: Vec::with_capacity(7),
        smem_alloc: None,
        smem_free: None,
        allocator: None,
    };

    let binary = actx.binary;
    let ctx = actx.ctx;
    let arg_cache = &actx.arg_cache;
    let bump = &actx.bump;

    let mut analysis = FuncAnalysis::new(binary, ctx, game_loop);
    let mut analyzer = FindSetLimits::<E> {
        actx,
        result: &mut result,
        arg_cache,
        game_loop_set_local_u32s: bumpvec_with_capacity(0x8, bump),
        binary,
    };
    analysis.analyze(&mut analyzer);
    if let Some(alloc) = result.smem_alloc {
        let mut analysis = FuncAnalysis::new(binary, ctx, alloc);
        let mut analyzer = AllocatorFromSMemAlloc::<E> {
            limit: 24,
            result: None,
            phantom: Default::default(),
        };
        analysis.analyze(&mut analyzer);
        result.allocator = analyzer.result;
    }
    result
}

struct AllocatorFromSMemAlloc<'e, E: ExecutionState<'e>> {
    limit: u8,
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for AllocatorFromSMemAlloc<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if matches!(*op, Operation::Call(..) | Operation::Jump { .. } ) {
            if self.limit == 0 {
                ctrl.end_analysis();
                return;
            } else {
                self.limit -= 1;
            }
        }
        if let Operation::Call(dest) = *op {
            let dest = ctrl.resolve(dest);
            if let Some(dest) = dest.if_constant() {
                let dest = E::VirtualAddress::from_u64(dest);
                ctrl.analyze_with_current_state(self, dest);
            } else {
                // Check for allocator.vtable.alloc(size, align)
                let ctx = ctrl.ctx();
                let ecx = ctrl.resolve(ctx.register(1));
                self.result = ctrl.if_mem_word(dest)
                    .and_then(|x| {
                        let x = x.if_arithmetic_add_const(1 * E::VirtualAddress::SIZE as u64)?;
                        ctrl.if_mem_word(x)
                            .filter(|&x| x == ecx)
                    });
            }
            if self.result.is_some() {
                ctrl.end_analysis();
            }
        }
    }
}

struct FindSetLimits<'a, 'acx, 'e, E: ExecutionState<'e>> {
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
    //
    // sizeof 8 struct to allow generic func deduplication
    game_loop_set_local_u32s: BumpVec<'acx, U8Chunk>,
    actx: &'acx AnalysisCtx<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

#[repr(align(4))]
#[derive(Copy, Clone)]
struct U8Chunk([u8; 8]);

struct SetLimitsAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut Limits<'e, E::VirtualAddress>,
    arg_cache: &'acx ArgCache<'e, E>,
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
    depth_0_arg1_global_stores: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
    call_tracker: CallTracker<'acx, 'e, E>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    FindSetLimits<'a, 'acx, 'e, E>
{
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
                            depth_0_arg1_global_stores:
                                bumpvec_with_capacity(0x10, &self.actx.bump),
                            call_tracker: CallTracker::with_capacity(self.actx, 0x1000_0000, 32),
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

impl<'a, 'acx, 'e, E: ExecutionState<'e>> FindSetLimits<'a, 'acx, 'e, E> {
    fn is_local_u32_set(&self, offset: u32) -> bool {
        let index = (offset / 8) as usize;
        let bit = offset & 7;
        self.game_loop_set_local_u32s
            .get(index >> 3)
            .map(|x| x.0[index & 7])
            .map(|bits| bits & (1 << bit) != 0)
            .unwrap_or(false)
    }

    fn set_local_u32(&mut self, offset: u32) {
        let index = (offset / 8) as usize;
        let bit = offset & 7;
        if self.game_loop_set_local_u32s.len() <= (index >> 3) {
            self.game_loop_set_local_u32s.resize((index >> 3) + 1, U8Chunk([0u8; 8]));
        }
        self.game_loop_set_local_u32s[(index >> 3)].0[index & 7] |= 1 << bit;
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SetLimitsAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest_unres) => {
                let dest_op = ctrl.resolve(dest_unres);
                let ctx = ctrl.ctx();
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let ecx = ctrl.resolve(ctx.register(1));
                let mut inline = false;
                let word_size = E::VirtualAddress::SIZE;
                if self.check_malloc_free && self.result.allocator.is_none() {
                    // Note: Assuming this is inside image vector resize.
                    // alloc image_count * 0x40
                    let is_alloc = arg1.if_arithmetic(scarf::ArithOpType::Lsh)
                        .and_then(|(_, r)| r.if_constant())
                        .filter(|&c| c == 6)
                        .is_some();
                    if is_alloc {
                        match dest_op.if_constant() {
                            Some(s) => {
                                self.result.smem_alloc = Some(E::VirtualAddress::from_u64(s));
                            }
                            None => {
                                // Check for call word[word[ecx] + 4],
                                // allocator.vtable.alloc(size, align)
                                let allocator = ctrl.if_mem_word(dest_op)
                                    .and_then(|x| {
                                        let x = x.if_arithmetic_add_const(1 * word_size as u64)?;
                                        ctrl.if_mem_word(x)
                                            .filter(|&x| x == ecx)
                                    });
                                if let Some(allocator) = allocator {
                                    self.result.allocator =
                                        Some(self.call_tracker.resolve_calls(allocator));
                                }
                            }
                        };
                        return;
                    }
                    let is_free = arg1.if_memory()
                        .and_then(|mem| {
                            Some(mem.address == self.result.arrays.get(0)?.get(0)?.0)
                        })
                        .unwrap_or(false);
                    if is_free {
                        let dest = match dest_op.if_constant() {
                            Some(s) => E::VirtualAddress::from_u64(s),
                            None => return,
                        };
                        self.result.smem_free = Some(dest);
                        return;
                    }
                }
                let dest = match dest_op.if_constant() {
                    Some(s) => E::VirtualAddress::from_u64(s),
                    None => return,
                };
                if let Some((off, add, mul)) = self.arg1_off(arg1) {
                    if ecx.if_constant().is_some() {
                        if off & 3 != 0 {
                            self.result.arrays.clear();
                            ctrl.end_analysis();
                            return;
                        }
                        self.add_result(off, add, mul, ecx);
                        // off == 0 => images
                        if self.result.smem_alloc.is_none() &&
                            self.result.allocator.is_none() &&
                            off == 0
                        {
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
                if self.check_malloc_free {
                    self.call_tracker.add_call(ctrl, dest);
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
                                    if self.result.smem_alloc.is_none() &&
                                        self.result.allocator.is_none() &&
                                        off == 0
                                    {
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

impl<'a, 'acx, 'e, E: ExecutionState<'e>> SetLimitsAnalyzer<'a, 'acx, 'e, E> {
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

pub(crate) fn analyze_step_objects<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_objects: E::VirtualAddress,
    game: Operand<'e>,
    first_active_unit: Operand<'e>,
    first_hidden_unit: Operand<'e>,
    first_active_bullet: Operand<'e>,
    active_iscript_unit: Operand<'e>,
) -> StepObjectsAnalysis<'e, E::VirtualAddress> {
    let mut result = StepObjectsAnalysis {
        step_active_frame: None,
        step_hidden_frame: None,
        step_bullet_frame: None,
        reveal_area: None,
        vision_update_counter: None,
        vision_updated: None,
        first_dying_unit: None,
        first_revealer: None,
        first_invisible_unit: None,
        active_iscript_flingy: None,
        active_iscript_bullet: None,
    };

    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    let mut analyzer = StepObjectsAnalyzer::<E> {
        result: &mut result,
        inline_depth: 0,
        inline_limit: 0,
        needs_inline_verify: false,
        game,
        first_active_unit,
        first_hidden_unit,
        first_active_bullet,
        active_iscript_unit,
        state: StepObjectsAnalysisState::VisionUpdateCounter,
        continue_state: None,
        simulated_funcs: FxHashMap::with_capacity_and_hasher(64, Default::default()),
        active_iscript_flingy_candidate: None,
        invisible_unit_inline_depth: 0,
        invisible_unit_checked_fns: bumpvec_with_capacity(0x10, &actx.bump),
        first_call_of_func: false,
    };
    loop {
        analysis.analyze(&mut analyzer);
        match analyzer.continue_state.take() {
            Some((state, addr)) => {
                analysis =
                    FuncAnalysis::custom_state(binary, ctx, addr, *state, Default::default());
            }
            _ => break,
        }
    }
    result
}

struct StepObjectsAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepObjectsAnalysis<'e, E::VirtualAddress>,
    inline_depth: u8,
    inline_limit: u8,
    needs_inline_verify: bool,
    game: Operand<'e>,
    first_active_unit: Operand<'e>,
    first_hidden_unit: Operand<'e>,
    first_active_bullet: Operand<'e>,
    active_iscript_unit: Operand<'e>,
    state: StepObjectsAnalysisState,
    // Used to kill all other analysis branches and continuing from there
    // (Avoid unnecessarily deep stack from using analyze_with_current_state)
    continue_state: Option<(Box<E>, E::VirtualAddress)>,
    simulated_funcs: FxHashMap<E::VirtualAddress, Option<Operand<'e>>>,
    // (Value stored, operand stored to)
    active_iscript_flingy_candidate: Option<(Operand<'e>, Operand<'e>)>,
    invisible_unit_inline_depth: u8,
    invisible_unit_checked_fns: BumpVec<'acx, E::VirtualAddress>,
    first_call_of_func: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepObjectsAnalysisState {
    // Search for move of 0x64 to Mem32[vision_update_counter]
    VisionUpdateCounter,
    // Search for move 0 to Mem8[vision_updated], followed by comparision of that
    // against 0.
    VisionUpdated,
    // Inline once to depth 1 (step_units), but require the function to start with store of 0
    // to global value (interceptor_focused_this_frame), or a call to such function.
    // Also assume any comparision against first_active_unit != 0 to be false, as well
    // as completed_unit_count(0xb, 0x69) (Pl12 Dweb)
    // Assume first_dying_unit to be first write to active_iscript_unit.
    FirstDyingUnit,
    // First call where active_iscript_unit is set to first_active_unit and ecx is that too
    StepActiveUnitFrame,
    // Same as first_dying_unit, write something new to active_iscript_unit.
    // Calls reveal_area(this = first_revealer)
    FirstRevealer,
    // Same as StepActiveUnitFrame for first_hidden_unit
    StepHiddenUnitFrame,
    // Inline one level deeper.
    // Check for cmp Mem8[first_invisible_unit + 0x96] == 0
    // Afterwards end inlining back to step_objects
    FirstInvisibleUnit,
    // Function where this == first_active_bullet, and which immediately compares this.order
    StepBulletFrame,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepObjectsAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepObjectsAnalysisState::VisionUpdateCounter => {
                if let Operation::Move(DestOperand::Memory(mem), value, None) = *op {
                    if mem.size == MemAccessSize::Mem32 {
                        let value = ctrl.resolve(value);
                        if value.if_constant() == Some(0x64) {
                            let addr = ctrl.resolve(mem.address);
                            self.result.vision_update_counter = Some(ctx.mem32(addr));
                            self.state = StepObjectsAnalysisState::VisionUpdated;
                            self.continue_state = Some((
                                Box::new(ctrl.exec_state().clone()),
                                ctrl.address(),
                            ));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            StepObjectsAnalysisState::VisionUpdated => {
                if let Operation::Move(DestOperand::Memory(mem), value, None) = *op {
                    if mem.size == MemAccessSize::Mem8 {
                        let value = ctrl.resolve(value);
                        if value.if_constant() == Some(0) {
                            let addr = ctrl.resolve(mem.address);
                            if !is_stack_address(addr) {
                                self.result.vision_updated = Some(ctx.mem8(addr));
                                self.state = StepObjectsAnalysisState::FirstDyingUnit;
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::FirstDyingUnit => {
                if self.needs_inline_verify {
                    match *op {
                        Operation::Move(DestOperand::Memory(mem), value, None) => {
                            if mem.size == MemAccessSize::Mem32 {
                                let value = ctrl.resolve(value);
                                if value.if_constant() == Some(0) {
                                    let addr = ctrl.resolve(mem.address);
                                    if !is_stack_address(addr) {
                                        self.needs_inline_verify = false;
                                    }
                                }
                            }
                        }
                        Operation::Jump { .. } | Operation::Return(..) => {
                            ctrl.end_analysis();
                            return;
                        }
                        _ => (),
                    }
                }
                ctrl.aliasing_memory_fix(op);
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.check_large_stack_alloc(ctrl) {
                            return;
                        }
                        if self.inline_depth == 0 {
                            self.inline_depth = 1;
                            self.needs_inline_verify = true;
                            self.first_call_of_func = true;
                            ctrl.analyze_with_current_state(self, dest);
                            while let Some((state, addr)) = self.continue_state.take() {
                                let binary = ctrl.binary();
                                let mut analysis = FuncAnalysis::custom_state(
                                    binary,
                                    ctx,
                                    addr,
                                    *state,
                                    Default::default(),
                                );
                                analysis.analyze(self);
                            }
                            self.inline_depth = 0;
                            if !self.needs_inline_verify {
                                self.state = StepObjectsAnalysisState::StepBulletFrame;
                            }
                            self.needs_inline_verify = false;
                        }
                        if self.inline_depth == 1 && self.needs_inline_verify {
                            // Inline once to depth 2 to find write 0 to
                            // interceptor_focused_this_frame
                            ctrl.analyze_with_current_state(self, dest);
                            if self.needs_inline_verify {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                        self.simulate_func(ctrl, dest);
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((cmp, eq_zero)) = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1 == ctx.const_0())
                        .map(|x| (x.0, x.2))
                    {
                        let assume_zero = cmp == self.first_active_unit ||
                            cmp.if_mem32().filter(|&x| x == ctx.add_const(self.game, 0x70d0))
                                .is_some();
                        if assume_zero {
                            let dest = match eq_zero {
                                true => match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                },
                                false => ctrl.current_instruction_end(),
                            };
                            ctrl.end_branch();
                            ctrl.add_branch_with_current_state(dest);
                        }
                    }
                } else if let Operation::Move(ref dest, value, None) = *op {
                    if let DestOperand::Memory(mem) = dest {
                        if mem.size == E::WORD_SIZE {
                            let address = ctrl.resolve(mem.address);
                            let dest_op = ctrl.mem_word(address);
                            let value = ctrl.resolve(value);
                            if dest_op == self.active_iscript_unit {
                                self.result.first_dying_unit = Some(value);
                                if let Some((val2, dest2)) = self.active_iscript_flingy_candidate {
                                    if val2 == value {
                                        self.result.active_iscript_flingy = Some(dest2);
                                        self.state = StepObjectsAnalysisState::StepActiveUnitFrame;
                                    }
                                }
                            } else {
                                if self.result.first_dying_unit == Some(value) {
                                    self.result.active_iscript_flingy = Some(dest_op);
                                    self.state = StepObjectsAnalysisState::StepActiveUnitFrame;
                                } else {
                                    self.active_iscript_flingy_candidate = Some((value, dest_op));
                                }
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::StepActiveUnitFrame |
                StepObjectsAnalysisState::StepHiddenUnitFrame =>
            {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ctx.register(1));
                        let cmp = if self.state == StepObjectsAnalysisState::StepActiveUnitFrame {
                            self.first_active_unit
                        } else {
                            self.first_hidden_unit
                        };
                        if this == cmp {
                            let active_iscript_unit = ctrl.resolve(self.active_iscript_unit);
                            if active_iscript_unit == cmp {
                                if self.state == StepObjectsAnalysisState::StepActiveUnitFrame {
                                    self.result.step_active_frame = Some(dest);
                                    self.state = StepObjectsAnalysisState::FirstRevealer;
                                } else {
                                    self.result.step_hidden_frame = Some(dest);
                                    self.inline_limit = 0;
                                    self.state = StepObjectsAnalysisState::FirstInvisibleUnit;
                                }
                                if let Some(vision_updated) = self.result.vision_updated {
                                    // Has to be done for revealer loop to run
                                    let state = ctrl.exec_state();
                                    state.move_to(
                                        &DestOperand::from_oper(vision_updated),
                                        ctx.const_1(),
                                    );
                                }
                                return;
                            }
                        }
                        self.simulate_func(ctrl, dest);
                    }
                }
            }
            StepObjectsAnalysisState::FirstRevealer => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve(ctx.register(1));
                        let active_iscript_unit = ctrl.resolve(self.active_iscript_unit);
                        // The not Mem[x + 4] check is to avoid confusing other_list.next
                        // from loops.
                        let is_unit_next = this.if_memory()
                            .and_then(|x| {
                                x.address.if_arithmetic_add_const(E::VirtualAddress::SIZE.into())
                            })
                            .is_some();
                        if this == active_iscript_unit &&
                            this != self.first_active_unit &&
                            !is_unit_next &&
                            !this.is_undefined()
                        {
                            self.result.first_revealer = Some(this);
                            self.result.reveal_area = Some(dest);
                            self.state = StepObjectsAnalysisState::StepHiddenUnitFrame;
                            return;
                        }
                        self.simulate_func(ctrl, dest);
                    }
                }
            }
            StepObjectsAnalysisState::FirstInvisibleUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.check_large_stack_alloc(ctrl) {
                            return;
                        }
                        let simulated = self.simulate_func(ctrl, dest);
                        if simulated {
                            return;
                        }
                        if self.invisible_unit_inline_depth < 2 {
                            if !self.invisible_unit_checked_fns.contains(&dest) {
                                self.invisible_unit_checked_fns.push(dest);
                                let old_depth = self.invisible_unit_inline_depth;
                                let old_limit = self.inline_limit;
                                self.invisible_unit_inline_depth += 1;
                                self.inline_limit = 5;
                                self.first_call_of_func = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.invisible_unit_inline_depth = old_depth;
                                self.inline_limit = old_limit;
                                if self.result.first_invisible_unit.is_some() {
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    } else {
                                        self.state = StepObjectsAnalysisState::StepBulletFrame;
                                    }
                                }
                            }
                        }
                    }
                }
                if let Operation::Jump { condition, ..} = *op {
                    if self.inline_limit != 0 {
                        if self.inline_limit == 1 {
                            ctrl.end_analysis();
                            return;
                        }
                        self.inline_limit -= 1;
                    }
                    let condition = ctrl.resolve(condition);
                    let result = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1 == ctx.const_0())
                        .and_then(|x| x.0.if_mem8()?.if_arithmetic_add_const(0x96));
                    if let Some(result) = result {
                        self.result.first_invisible_unit = Some(result);
                        if self.invisible_unit_inline_depth != 0 || self.inline_depth != 0 {
                            ctrl.end_analysis()
                        } else {
                            self.state = StepObjectsAnalysisState::StepBulletFrame;
                        }
                    }
                }
            }
            StepObjectsAnalysisState::StepBulletFrame => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let simulated = self.simulate_func(ctrl, dest);
                        if simulated {
                            return;
                        }
                        if self.inline_depth < 2 {
                            let old_inline_depth = self.inline_depth;
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = old_inline_depth;
                            if let Some(func) = self.result.step_bullet_frame {
                                if func.as_u64() == 0 {
                                    self.result.step_bullet_frame = Some(dest);
                                }
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(mem), value, None) = *op {
                    if mem.size == E::WORD_SIZE && self.result.active_iscript_bullet.is_none() {
                        let value = ctrl.resolve(value);
                        if value == self.first_active_bullet {
                            let address = ctrl.resolve(mem.address);
                            let dest_op = ctrl.mem_word(address);
                            if Some(dest_op) != self.result.active_iscript_flingy {
                                self.result.active_iscript_bullet = Some(dest_op);
                            }
                        }
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_gt()
                        .and_either(|x| x.if_mem8())
                        .and_then(|x| x.0.if_arithmetic_add_const(0x4d))
                        .filter(|&x| x == self.first_active_bullet)
                        .is_some();
                    if ok {
                        self.result.step_bullet_frame = Some(E::VirtualAddress::from_u64(0));
                    }
                    // Only check first jump at depth 2
                    if self.inline_depth == 2 {
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> StepObjectsAnalyzer<'a, 'acx, 'e, E> {
    /// Replaces a trivial function call which only returns something without side effects
    /// with a move to eax.
    ///
    /// Returns true if was able to simulate.
    fn simulate_func(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        func: E::VirtualAddress,
    ) -> bool {
        let entry = self.simulated_funcs.entry(func);
        let &mut result = entry.or_insert_with(|| {
            analyze_simulate_short::<E>(ctrl.ctx(), ctrl.binary(), func)
        });
        if let Some(result) = result {
            let result = ctrl.resolve(result);
            ctrl.skip_operation();
            let state = ctrl.exec_state();
            state.move_to(
                &DestOperand::Register64(scarf::operand::Register(0)),
                result,
            );
            true
        } else {
            false
        }
    }

    fn check_large_stack_alloc(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        if self.first_call_of_func {
            self.first_call_of_func = false;
            let ctx = ctrl.ctx();
            let maybe_stack_alloc = ctrl.resolve(ctx.register(0))
                .if_constant()
                .filter(|&c| c >= 0x1000)
                .is_some();
            if maybe_stack_alloc {
                ctrl.skip_operation();
                return true;
            }
        }
        false
    }
}

fn analyze_simulate_short<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    func: E::VirtualAddress,
) -> Option<Operand<'e>> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }
    impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match op {
                Operation::Jump { .. } | Operation::Call(..) => {
                    ctrl.end_analysis();
                }
                Operation::Move(DestOperand::Memory(mem), _, _) => {
                    let address = ctrl.resolve(mem.address);
                    if !is_stack_address(address) {
                        ctrl.end_analysis();
                    }
                }
                Operation::Return(..) => {
                    let ctx = ctrl.ctx();
                    self.result = Some(ctrl.resolve(ctx.register(0)));
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }

    let mut exec = E::initial_state(ctx, binary);
    exec.move_resolved(
        &DestOperand::Memory(
            scarf::operand::MemAccess { size: E::WORD_SIZE, address: ctx.register(4) }
        ),
        ctx.mem_variable_rc(E::WORD_SIZE, ctx.register(4)),
    );
    exec.move_to(
        &DestOperand::Register64(scarf::operand::Register(4)),
        ctx.sub_const(ctx.register(4), E::VirtualAddress::SIZE as u64),
    );
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, func, exec, Default::default());
    let mut analyzer: Analyzer<E> = Analyzer {
        result: None,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn is_stack_address(addr: Operand<'_>) -> bool {
    if let Some((l, r)) = addr.if_arithmetic_sub() {
        r.if_constant().is_some() && l.if_register().map(|x| x.0) == Some(4)
    } else {
        addr.if_register().map(|x| x.0) == Some(4)
    }
}
