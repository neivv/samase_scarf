use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{
    BinaryFile, BinarySection, OperandCtx, Operand, DestOperand, Operation, MemAccess,
    MemAccessSize,
};

use crate::analysis::{ArgCache, AnalysisCtx};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::call_tracker::CallTracker;
use crate::linked_list::DetectListAdd;
use crate::util::{
    ControlExt, OperandExt, OptionExt, MemAccessExt, bumpvec_with_capacity, if_arithmetic_eq_neq,
    single_result_assign, is_stack_address, is_global, ExecStateExt,
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
    pub allocator: Option<Operand<'e>>,
}

pub(crate) struct StepObjectsAnalysis<'e, Va: VirtualAddress> {
    pub step_active_frame: Option<Va>,
    pub step_hidden_frame: Option<Va>,
    pub step_bullet_frame: Option<Va>,
    pub step_bullets: Option<Va>,
    pub reveal_area: Option<Va>,
    pub order_timer_reset_counter: Option<Operand<'e>>,
    pub secondary_order_timer_reset_counter: Option<Operand<'e>>,
    pub vision_update_counter: Option<Operand<'e>>,
    pub vision_updated: Option<Operand<'e>>,
    pub first_dying_unit: Option<Operand<'e>>,
    pub first_revealer: Option<Operand<'e>>,
    pub first_invisible_unit: Option<Operand<'e>>,
    pub active_iscript_flingy: Option<Operand<'e>>,
    pub active_iscript_bullet: Option<Operand<'e>>,
    pub update_unit_visibility: Option<Va>,
    pub update_cloak_state: Option<Va>,
    pub dcreep_next_update: Option<Operand<'e>>,
    pub dcreep_list_size: Option<Operand<'e>>,
    pub dcreep_list_begin: Option<Operand<'e>>,
    pub dcreep_lookup: Option<Operand<'e>>,
    pub creep_funcs: Option<Operand<'e>>,
    pub creep_modify_state: Option<Va>,
    pub for_each_surrounding_tile: Option<Va>,
    pub creep_update_border_for_tile: Option<Va>,
    pub dcreep_unit_next_update: Option<Operand<'e>>,
    pub unit_count: Option<Operand<'e>>,
    pub last_dying_unit: Option<Operand<'e>>,
    pub first_free_unit: Option<Operand<'e>>,
    pub last_free_unit: Option<Operand<'e>>,
    pub get_creep_spread_area: Option<Va>,
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
        if let Some(enable_addr) = part.if_memory().and_then(|x| x.if_constant_address()) {
            let enable_addr = E::VirtualAddress::from_u64(enable_addr);
            let globals = functions.find_functions_using_global(analysis, enable_addr);
            for global_ref in globals {
                let entry = global_ref.func_entry;
                if is_branchless_leaf(analysis, entry) {
                    let callers = functions.find_callers(analysis, entry);
                    rng_refs.extend_from_slice_copy(&callers);
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
            let res = entry_of_until(binary, &funcs, addr, |entry| {
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
                if let Some(dest) = ctrl.resolve_va(dest) {
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
            Operation::Move(ref dest, val) => {
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
            Operation::Move(ref dest, val) => {
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
                if let Some(_addr) = mem.if_constant_address() {
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
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindGame<'e, E: ExecutionState<'e>> {
    call_depth: u8,
    jump_limit: u8,
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindGame<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.call_depth < 3 {
                    if let Some(dest) = ctrl.resolve_va(dest) {
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
            Operation::Move(_, val) => {
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
            Some((l.if_mem16()?, r.if_mem16()?))
        }).filter_map(|(l, r)| {
            let (l_base, l_offset) = l.address();
            let (r_base, r_offset) = r.address();
            if l_base == r_base {
                if l_offset.wrapping_add(2) == r_offset {
                    Some(ctx.add_const(l_base, l_offset.wrapping_sub(0xe4)))
                } else if r_offset.wrapping_add(2) == l_offset {
                    Some(ctx.add_const(r_base, r_offset.wrapping_sub(0xe4)))
                } else {
                    None
                }
            } else {
                None
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
            entry_esp: ctx.register(4),
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
    entry_esp: Operand<'e>,
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
                let old_esp = self.entry_esp;
                self.entry_esp = ctrl.get_new_esp_for_call();
                ctrl.analyze_with_current_state(self, dest);
                self.entry_esp = old_esp;
            } else {
                self.check_result_at_call(ctrl, dest);
            }
            if self.result.is_some() {
                ctrl.end_analysis();
            }
        } else if let Operation::Jump { condition, to } = *op {
            let ctx = ctrl.ctx();
            if condition == ctx.const_1() {
                if self.entry_esp == ctrl.resolve_register(4) {
                    // Tail call
                    let to = ctrl.resolve(to);
                    if to.if_constant().is_none() {
                        self.check_result_at_call(ctrl, to);
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

impl<'e, E: ExecutionState<'e>> AllocatorFromSMemAlloc<'e, E> {
    fn check_result_at_call(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, dest: Operand<'e>) {
        // Check for allocator.vtable.alloc(size, align)
        // Ok if dest is MemWord[[this] + 1 * word_size]
        let ecx = ctrl.resolve_register(1);
        self.result = ctrl.if_mem_word_offset(dest, 1 * E::VirtualAddress::SIZE as u64)
            .and_then(|x| ctrl.if_mem_word_offset(x, 0))
            .filter(|&x| x == ecx);
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

impl<'a, 'acx, 'e: 'a + 'acx, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    FindSetLimits<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest) => {
                let dest = match ctrl.resolve(dest).if_constant() {
                    Some(s) => E::VirtualAddress::from_u64(s),
                    None => return,
                };
                let arg1 = ctrl.resolve_arg(0);
                if let Some(offset) = Self::esp_offset(arg1, ctx).filter(|&x| x >= 6 * 4) {
                    let u32_offset = offset / 4;
                    if (0..7).all(|i| self.is_local_u32_set(u32_offset - i)) {
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
            Operation::Move(DestOperand::Memory(ref mem), _) => {
                let dest_mem = ctrl.resolve_mem(mem);
                if let Some(offset) = Self::esp_offset_mem(&dest_mem, ctx) {
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

impl<'a, 'acx, 'e: 'a + 'acx, E: ExecutionState<'e>> FindSetLimits<'a, 'acx, 'e, E> {
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
        self.game_loop_set_local_u32s[index >> 3].0[index & 7] |= 1 << bit;
    }

    fn check_esp(esp: Operand<'e>, ctx: OperandCtx<'e>) -> bool {
        // Allow esp and
        // ((esp - y) & 0xffff_fff0)
        let reg4 = ctx.register(4);
        esp == reg4 ||
            esp.if_arithmetic_and()
                .filter(|&(_, r)| r.if_constant().is_some())
                .filter(|&(l, _)| {
                    l == reg4 || l.if_arithmetic_sub()
                        .filter(|&(l, r)| l == reg4 && r.if_constant().is_some())
                        .is_some()
                })
                .is_some()
    }

    fn esp_offset(val: Operand<'e>, ctx: OperandCtx<'e>) -> Option<u32> {
        val.if_arithmetic_sub()
            .filter(|&(l, _)| Self::check_esp(l, ctx))
            .and_then(|(_, r)| r.if_constant())
            .map(|c| c as u32)
    }

    fn esp_offset_mem(val: &MemAccess<'e>, ctx: OperandCtx<'e>) -> Option<u32> {
        let (base, offset) = val.address();
        let sext_offset = match E::VirtualAddress::SIZE == 4 {
            true => offset as i32 as i64,
            false => offset as i64,
        };
        if sext_offset > 0 || sext_offset < -0x20000 {
            return None;
        }
        if Self::check_esp(base, ctx) {
            Some(0i32.wrapping_sub(sext_offset as i32) as u32)
        } else {
            None
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    SetLimitsAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(dest_unres) => {
                let dest_op = ctrl.resolve(dest_unres);
                let arg1 = ctrl.resolve_arg_thiscall(0);
                let arg1_not_this = ctrl.resolve_arg(0);
                let ecx = ctrl.resolve_register(1);
                let mut inline = false;
                let word_size = E::VirtualAddress::SIZE;
                if self.check_malloc_free && self.result.allocator.is_none() {
                    // Note: Assuming this is inside image vector resize.
                    // alloc image_count * 0x40
                    let is_alloc = E::struct_layouts().if_mul_image_size(arg1_not_this).is_some();
                    if is_alloc {
                        if let Some(s) = dest_op.if_constant() {
                            self.result.smem_alloc = Some(E::VirtualAddress::from_u64(s));
                            return;
                        }
                    }
                    let is_thiscall_alloc = E::struct_layouts().if_mul_image_size(arg1).is_some();
                    if is_thiscall_alloc {
                        // Check for call word[word[ecx] + 4],
                        // allocator.vtable.alloc(size, align)
                        let allocator = ctrl.if_mem_word_offset(dest_op, 1 * word_size as u64)
                            .and_then(|x| ctrl.if_mem_word_offset(x, 0))
                            .filter(|&x| x == ecx);
                        if let Some(allocator) = allocator {
                            self.result.allocator =
                                Some(self.call_tracker.resolve_calls(allocator));
                            return;
                        }
                    }
                    let is_free = arg1_not_this.if_memory()
                        .and_then(|mem| {
                            Some(mem.address_op(ctx) == self.result.arrays.get(0)?.get(0)?.0)
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
                if !inline &&
                    E::VirtualAddress::SIZE == 8 &&
                    self.arg1_off(arg1_not_this).is_some()
                {
                    inline = true;
                }
                if !inline && self.check_malloc_free && ecx.if_constant().is_some() {
                    inline = true;
                }
                if inline || self.inline_depth == 0 {
                    if self.inline_depth < 3 {
                        let exec_state = ctrl.exec_state();
                        if self.inline_depth == 0 {
                            for &(dest, value) in &self.depth_0_arg1_global_stores {
                                exec_state.write_memory(&ctx.mem_access32(dest, 0), value);
                            }
                        }

                        self.inline_depth += 1;
                        let was_inlining_object_subfunc = self.inlining_object_subfunc;
                        let was_checking_malloc_free = self.check_malloc_free;
                        self.inlining_object_subfunc = inline;
                        let esp = self.func_initial_esp;
                        self.func_initial_esp = ctx.sub_const(
                            ctrl.resolve_register(4),
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
            Operation::Jump { condition, to } => {
                let ctx = ctrl.ctx();
                let esp = ctrl.resolve_register(4);
                if condition == ctx.const_1() && esp == self.func_initial_esp {
                    // Tail call
                    ctrl.end_branch();
                    let new_esp = ctx.add_const(esp, E::VirtualAddress::SIZE as u64);
                    ctrl.set_register(4, new_esp);
                    self.operation(ctrl, &Operation::Call(to));
                }
            }
            Operation::Move(ref dest, value) => {
                match *dest {
                    DestOperand::Arch(arch) if E::VirtualAddress::SIZE == 4 => {
                        if arch.if_register() == Some(5) && value.if_memory().is_some() {
                            // Make pop ebp always be mov esp, orig_esp
                            // even if current esp is considered unknown
                            let ctx = ctrl.ctx();
                            ctrl.set_register(
                                4,
                                ctx.sub_const(
                                    self.func_initial_esp,
                                    E::VirtualAddress::SIZE as u64,
                                ),
                            );
                        }
                    }
                    DestOperand::Memory(ref mem) if !self.redo_check_malloc_free => {
                        let value = ctrl.resolve(value);
                        // Generally vector.resize(limits.x) is caught at call
                        // but check also for inlined vector.size = limits.x
                        if let Some((off, add, mul)) = self.arg1_off(value) {
                            if off & 3 != 0 {
                                return;
                            }
                            let dest = ctrl.resolve_mem(mem);
                            let ctx = ctrl.ctx();
                            if let Some(c) = dest.if_constant_address() {
                                if self.inlining_object_subfunc {
                                    let vector = ctx.constant(
                                        c.wrapping_sub(E::VirtualAddress::SIZE as u64)
                                    );
                                    self.add_result(off, add, mul, vector);
                                    // off == 0 => images
                                    if self.result.smem_alloc.is_none() &&
                                        self.result.allocator.is_none() &&
                                        off == 0
                                    {
                                        self.redo_check_malloc_free = true;
                                    }
                                } else if self.inline_depth == 0 {
                                    let dest_op = ctx.constant(c);
                                    self.depth_0_arg1_global_stores.push((dest_op, value));
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
        Some(Operand::and_masked(val.unwrap_sext()).0)
            .map(|val| {
                val.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        r.if_constant().map(|c| (l, c as u32, 0))
                    })
                    .or_else(|| {
                        val.if_arithmetic_mul()
                            .and_then(|(l, r)| {
                                r.if_constant().map(|c| (Operand::and_masked(l).0, 0, c as u32))
                            })
                    })
                    .unwrap_or_else(|| (val, 0, 0))
            })
            .and_then(|(x, add, mul)| {
                x.if_mem32()
                    .and_then(|x| {
                        let self_arg1 = self.arg_cache.on_entry(0);
                        let (base, offset) = x.address();
                        if base == self_arg1 {
                            Some((offset as u32, add, mul))
                        } else {
                            None
                        }
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
        step_bullets: None,
        reveal_area: None,
        order_timer_reset_counter: None,
        secondary_order_timer_reset_counter: None,
        vision_update_counter: None,
        vision_updated: None,
        first_dying_unit: None,
        first_revealer: None,
        first_invisible_unit: None,
        active_iscript_flingy: None,
        active_iscript_bullet: None,
        update_unit_visibility: None,
        update_cloak_state: None,
        dcreep_next_update: None,
        dcreep_list_size: None,
        dcreep_list_begin: None,
        dcreep_lookup: None,
        creep_funcs: None,
        creep_modify_state: None,
        for_each_surrounding_tile: None,
        creep_update_border_for_tile: None,
        dcreep_unit_next_update: None,
        unit_count: None,
        last_dying_unit: None,
        first_free_unit: None,
        last_free_unit: None,
        get_creep_spread_area: None,
    };

    let ctx = actx.ctx;
    let binary = actx.binary;
    let arg_cache = &actx.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    let mut analyzer = StepObjectsAnalyzer::<E> {
        result: &mut result,
        arg_cache,
        inline_depth: 0,
        max_inline_depth: 0,
        inline_limit: 0,
        step_units_depth: 0,
        step_dying_unit_depth: 0,
        needs_inline_verify: false,
        game,
        first_active_unit,
        first_hidden_unit,
        first_active_bullet,
        active_iscript_unit,
        state: StepObjectsAnalysisState::DcreepUpdateCounter,
        continue_state: None,
        active_iscript_flingy_candidate: None,
        invisible_unit_inline_depth: 0,
        invisible_unit_checked_fns: bumpvec_with_capacity(0x10, &actx.bump),
        first_call_of_func: false,
        cloak_state_checked: false,
        func_entry: step_objects,
        text: actx.binary_sections.text,
        dcreep_next_update_candidate: None,
        unit_count_candidate: None,
        list_add_tracker: DetectListAdd::new(None),
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 32),
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
    arg_cache: &'acx ArgCache<'e, E>,
    inline_depth: u8,
    max_inline_depth: u8,
    inline_limit: u8,
    step_units_depth: u8,
    step_dying_unit_depth: u8,
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
    // (Value stored, operand stored to)
    active_iscript_flingy_candidate: Option<(Operand<'e>, Operand<'e>)>,
    invisible_unit_inline_depth: u8,
    invisible_unit_checked_fns: BumpVec<'acx, E::VirtualAddress>,
    first_call_of_func: bool,
    cloak_state_checked: bool,
    func_entry: E::VirtualAddress,
    text: &'e BinarySection<E::VirtualAddress>,
    dcreep_next_update_candidate: Option<Operand<'e>>,
    unit_count_candidate: Option<Operand<'e>>,
    list_add_tracker: DetectListAdd<'e, E>,
    call_tracker: CallTracker<'acx, 'e, E>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum StepObjectsAnalysisState {
    // Search for update_counter = [const_arr[dcreep_list_size[9] >> 7]]
    // Inline once to update_dcreep
    DcreepUpdateCounter,
    // dcreep_list_begin[n] = [dcreep_list_begin[n]]
    // dcreep_lookup[n] = [dcreep_lookup[n] + 2 * WORD]
    DcreepLists,
    // Search for modify_creep_state(x_tile, y_tile, callback, 0)
    // May inline once to clear_creep(x_tile, y_tile)
    CreepModifyState,
    // Search for call of creep_funcs[2](x_tile, y_tile)
    CreepFuncs,
    // Search for call of
    // for_each_surrounding_tile(x_tile, y_tile, creep_update_border_for_tile, 0)
    CreepUpdateBorderForTile,
    // (Stop inlining back to depth 0)
    // Search for move of 0x64 to Mem32[vision_update_counter]
    VisionUpdateCounter,
    // Search for move 0 to Mem8[vision_updated], followed by comparision of that
    // against 0.
    VisionUpdated,
    // Inline once to depth 1 (step_units), but require the function to start with store of 0
    // to global value (interceptor_focused_this_frame), or a call to such function.
    // Then find a store of 0x96 to a global
    OrderTimerReset,
    // Store of 0x12c to a global
    SecondaryOrderTimerReset,
    // Assume any comparision against first_active_unit != 0 to be false, as well
    // as completed_unit_count(0xb, 0x69) (Pl12 Dweb)
    // Assume first_dying_unit to be first write to active_iscript_unit.
    FirstDyingUnit,
    // Find check for first_dying_unit.flags & 0x4000, continue at nonzero branch
    DcreepCheck,
    // Inline to step_dying_unit(first_dying_unit) {
    //      step_unit_dcreep(first_dying_unit)
    // }
    // Find write of 3 to global that was just before checked to be 0
    DcreepUnitNextUpdate,
    // Find get_creep_spread_area(
    //      first_dying.unit_id, first_dying.flingy_x, flingy_y, &rect, first_dying.flags & 1
    // )
    // Stop inlining step_unit_dcreep afterwards
    GetCreepSpreadArea,
    // Find check for first_dying_unit.sprite == 0, continue at zero branch
    DyingUnitNoSpriteCheck,
    // Inline to delete_dying_unit(first_dying_unit), find removal from dying_units
    LastDyingUnit,
    // May have to inline to release_unit(first_dying_unit), find list addition to free units
    FreeUnits,
    // First call where active_iscript_unit is set to first_active_unit and ecx is that too
    StepActiveUnitFrame,
    // Same as first_dying_unit, write something new to active_iscript_unit.
    // Calls reveal_area(this = first_revealer)
    FirstRevealer,
    // Next call with this = first_active_unit
    UpdateVisibilityArea,
    // Next call with this = first_active_unit, a1 = 0
    // Preceded by check for cloak state (flags & 0x300)
    UpdateCloakState,
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
        let dcreep_list_index_offset = E::struct_layouts().dcreep_list_index();
        let dcreep_x_offset = E::struct_layouts().dcreep_x();
        match self.state {
            StepObjectsAnalysisState::DcreepUpdateCounter => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            if self.state != StepObjectsAnalysisState::DcreepUpdateCounter {
                                self.state = StepObjectsAnalysisState::VisionUpdateCounter;
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref dest), value) = *op {
                    let value = ctrl.resolve(value);
                    let result = value.if_mem8()
                        .and_then(|mem| {
                            let (index, _) = mem.address();
                            let list_index9 = index.if_arithmetic_rsh_const(7)?
                                .if_mem16()?;
                            let list_start = list_index9.with_offset_size(
                                0u64.wrapping_sub(9 * 2),
                                MemAccessSize::Mem16,
                            );
                            Some(list_start.address_op(ctx))
                        });
                    if let Some(list) = result {
                        let dest = ctrl.resolve_mem(dest);
                        self.result.dcreep_list_size = Some(list);
                        self.result.dcreep_next_update = Some(ctx.memory(&dest));
                        self.state = StepObjectsAnalysisState::DcreepLists;
                    }
                }
            }
            StepObjectsAnalysisState::DcreepLists => {
                if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    // Match either
                    // MemWord[dcreep_list_begin + a.list_index * W] == a
                    // or
                    // MemWord[dcreep_lookup + ((a.x + a.y * 0x11) & 0x3ff) * W] == a
                    // So start with extracting MemWord[result + index * W] == _
                    let result = condition.if_arithmetic_eq_neq()
                        .map(|x| (x.0, x.1))
                        .and_either(|x| {
                            let mem = ctrl.if_mem_word(x)?;
                            mem.if_add_either(ctx, |x| {
                                x.if_arithmetic_mul_const(E::VirtualAddress::SIZE as u64)
                            })
                        })
                        .map(|x| x.0);
                    if let Some((index, result)) = result {
                        if let Some(_) = index.if_mem8_offset(dcreep_list_index_offset) {
                            single_result_assign(
                                Some(result),
                                &mut self.result.dcreep_list_begin,
                            );
                        } else {
                            let ok = index.if_arithmetic_and_const(0x3ff)
                                .and_then(|x| {
                                    x.if_arithmetic_add()
                                        .and_either_other(|x| x.if_arithmetic_mul_const(0x11))?
                                        .if_mem8_offset(dcreep_x_offset)
                                })
                                .is_some();
                            if ok {
                                single_result_assign(
                                    Some(result),
                                    &mut self.result.dcreep_lookup,
                                );
                            }
                        }
                        if self.result.dcreep_list_begin.is_some() &&
                            self.result.dcreep_lookup.is_some()
                        {
                            self.state = StepObjectsAnalysisState::CreepModifyState;
                            self.max_inline_depth = self.inline_depth.wrapping_add(1);
                        }
                    }
                }
            }
            StepObjectsAnalysisState::CreepModifyState | StepObjectsAnalysisState::CreepFuncs |
                StepObjectsAnalysisState::CreepUpdateBorderForTile =>
            {
                if let Operation::Call(dest) = *op {
                    let dest = ctrl.resolve(dest);
                    let arg1 = ctrl.resolve_arg(0);
                    let is_x = arg1.if_mem8_offset(dcreep_x_offset).is_some();
                    if is_x {
                        if self.state == StepObjectsAnalysisState::CreepFuncs {
                            if let Some(mem) = ctrl.if_mem_word(dest) {
                                let base = mem.with_offset(
                                    0u64.wrapping_sub(E::VirtualAddress::SIZE as u64 * 2),
                                );
                                self.result.creep_funcs = Some(base.address_op(ctx));
                                ctrl.clear_all_branches();
                                self.state = StepObjectsAnalysisState::CreepUpdateBorderForTile;
                            }
                        } else if let Some(dest) = dest.if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            if let Some(arg3) = ctrl.resolve_va(self.arg_cache.on_call(2)) {
                                if self.text.contains(arg3) {
                                    if self.state == StepObjectsAnalysisState::CreepModifyState {
                                        self.result.creep_modify_state = Some(dest);
                                        self.state = StepObjectsAnalysisState::CreepFuncs;
                                        ctrl.clear_all_branches();
                                        return;
                                    } else {
                                        self.result.for_each_surrounding_tile = Some(dest);
                                        self.result.creep_update_border_for_tile = Some(arg3);
                                        self.state = StepObjectsAnalysisState::VisionUpdateCounter;
                                        if self.inline_depth != 0 {
                                            ctrl.end_analysis();
                                        }
                                        return;
                                    }
                                }
                            }
                            if self.state == StepObjectsAnalysisState::CreepModifyState &&
                                self.inline_depth < self.max_inline_depth
                            {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state != StepObjectsAnalysisState::CreepModifyState
                                {
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::VisionUpdateCounter => {
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == MemAccessSize::Mem32 {
                        let value = ctrl.resolve(value);
                        if value.if_constant() == Some(0x64) {
                            let mem = ctrl.resolve_mem(mem);
                            self.result.vision_update_counter = Some(ctx.memory(&mem));
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
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == MemAccessSize::Mem8 {
                        let value = ctrl.resolve(value);
                        if value == ctx.const_0() {
                            let mem = ctrl.resolve_mem(mem);
                            if !is_stack_address(mem.address().0) {
                                self.result.vision_updated = Some(ctx.memory(&mem));
                                self.state = StepObjectsAnalysisState::OrderTimerReset;
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::OrderTimerReset => {
                ctrl.aliasing_memory_fix(op);
                if self.needs_inline_verify {
                    match *op {
                        Operation::Move(DestOperand::Memory(mem), value) => {
                            if mem.size == MemAccessSize::Mem32 {
                                let value = ctrl.resolve(value);
                                if value == ctx.const_0() {
                                    let addr = ctrl.resolve(mem.address().0);
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
                    }
                }
                if !self.needs_inline_verify {
                    if let Some(result) = self.check_global_store_const(ctrl, op, 0x96) {
                        self.result.order_timer_reset_counter = Some(result);
                        ctrl.clear_unchecked_branches();
                        self.state = StepObjectsAnalysisState::SecondaryOrderTimerReset;
                    }
                }
            }
            StepObjectsAnalysisState::SecondaryOrderTimerReset => {
                if let Some(result) = self.check_global_store_const(ctrl, op, 0x12c) {
                    self.result.secondary_order_timer_reset_counter = Some(result);
                    ctrl.clear_unchecked_branches();
                    self.state = StepObjectsAnalysisState::FirstDyingUnit;
                }
            }
            StepObjectsAnalysisState::FirstDyingUnit => {
                ctrl.aliasing_memory_fix(op);
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.simulate_func(ctrl, dest);
                    }
                }
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((cmp, eq_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        let assume_zero = cmp == self.first_active_unit ||
                            cmp.if_mem32_offset(0x70d0) == Some(self.game);
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
                } else if let Operation::Move(ref dest, value) = *op {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == E::WORD_SIZE {
                            let mem = ctrl.resolve_mem(mem);
                            let dest_op = ctx.memory(&mem);
                            let value = ctrl.resolve(value);
                            if dest_op == self.active_iscript_unit {
                                self.result.first_dying_unit = Some(value);
                                if let Some((val2, dest2)) = self.active_iscript_flingy_candidate {
                                    if val2 == value {
                                        self.result.active_iscript_flingy = Some(dest2);
                                        self.step_units_depth = self.inline_depth;
                                        self.max_inline_depth = self.inline_depth.wrapping_add(1);
                                        self.state = StepObjectsAnalysisState::DcreepCheck;
                                    }
                                }
                            } else {
                                if self.result.first_dying_unit == Some(value) {
                                    self.result.active_iscript_flingy = Some(dest_op);
                                    self.step_units_depth = self.inline_depth;
                                    self.max_inline_depth = self.inline_depth.wrapping_add(1);
                                    self.state = StepObjectsAnalysisState::DcreepCheck;
                                } else {
                                    self.active_iscript_flingy_candidate = Some((value, dest_op));
                                }
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::DcreepCheck |
                StepObjectsAnalysisState::DyingUnitNoSpriteCheck =>
            {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.simulate_func(ctrl, dest) {
                            return;
                        }
                        if self.inline_depth != self.max_inline_depth {
                            let this = ctrl.resolve_register(1);
                            if Some(this) == self.result.first_dying_unit {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                            }
                        }
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((inner, eq_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        let ok = if self.state == StepObjectsAnalysisState::DcreepCheck {
                            inner.if_arithmetic_and_const(0x40)
                                .and_then(|x| {
                                    let flags_offset = E::struct_layouts().unit_flags();
                                    x.if_mem8_offset(flags_offset + 1)
                                })
                                .is_some_and(|x| Some(x) == self.result.first_dying_unit)
                        } else {
                            let sprite_offset = E::struct_layouts().unit_sprite();
                            ctrl.if_mem_word_offset(inner, sprite_offset)
                                .is_some_and(|x| Some(x) == self.result.first_dying_unit)
                        };
                        if ok {
                            let continue_on_zero;
                            if self.state == StepObjectsAnalysisState::DcreepCheck {
                                self.state = StepObjectsAnalysisState::DcreepUnitNextUpdate;
                                self.step_dying_unit_depth = self.inline_depth;
                                self.max_inline_depth = self.inline_depth.wrapping_add(1);
                                continue_on_zero = false;
                            } else {
                                self.state = StepObjectsAnalysisState::LastDyingUnit;
                                self.max_inline_depth = self.inline_depth.wrapping_add(2);
                                continue_on_zero = true;
                            }
                            let dest = match continue_on_zero ^ eq_zero {
                                false => match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                },
                                true => ctrl.current_instruction_end(),
                            };
                            ctrl.continue_at_address(dest);
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), _) = *op {
                    // Block moves to first_dying_unit.sprite so that it can be
                    // matched later on.
                    let mem = ctrl.resolve_mem(mem);
                    let (base, offset) = mem.address();
                    if offset == E::struct_layouts().unit_sprite() &&
                        Some(base) == self.result.first_dying_unit
                    {
                        ctrl.skip_operation();
                    }
                }
            }
            StepObjectsAnalysisState::DcreepUnitNextUpdate => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < self.max_inline_depth {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let arg1 = ctrl.resolve_arg(0);
                            if Some(arg1) == self.result.first_dying_unit {
                                let old_inline_limit = self.inline_limit;
                                self.inline_limit = 5;
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                self.inline_limit = old_inline_limit;
                                if self.state != StepObjectsAnalysisState::DcreepUnitNextUpdate {
                                    self.state = StepObjectsAnalysisState::DyingUnitNoSpriteCheck;
                                    self.max_inline_depth = self.step_dying_unit_depth;
                                }
                            }
                        }
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    if self.inline_limit != 0 {
                        if self.inline_limit == 1 {
                            ctrl.end_analysis();
                            return;
                        }
                        self.inline_limit -= 1;
                    }
                    let condition = ctrl.resolve(condition);
                    if let Some((x, _eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if is_global(x) {
                            self.dcreep_next_update_candidate = Some(x);
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if ctrl.resolve(value).if_constant() == Some(3) {
                        let mem = ctrl.resolve_mem(mem);
                        if let Some(cand) = self.dcreep_next_update_candidate {
                            if let Some(mem2) = cand.if_memory() {
                                if mem == *mem2 {
                                    self.result.dcreep_unit_next_update = Some(cand);
                                    self.state = StepObjectsAnalysisState::GetCreepSpreadArea;
                                }
                            }
                        }
                    }
                }
            }
            StepObjectsAnalysisState::GetCreepSpreadArea => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let first_dying = match self.result.first_dying_unit {
                            Some(s) => s,
                            None => return,
                        };
                        let unit_id_offset = E::struct_layouts().unit_id();
                        let x_offset = E::struct_layouts().flingy_pos();
                        let y_offset = x_offset + 2;

                        let ok = ctrl.resolve_arg(0)
                                .if_mem16_offset(unit_id_offset) == Some(first_dying) &&
                            ctrl.resolve_arg(1)
                                .unwrap_sext()
                                .if_mem16_offset(x_offset) == Some(first_dying) &&
                            ctrl.resolve_arg(2)
                                .unwrap_sext()
                                .if_mem16_offset(y_offset) == Some(first_dying);
                        if ok {
                            self.result.get_creep_spread_area = Some(dest);
                            self.state = StepObjectsAnalysisState::DyingUnitNoSpriteCheck;
                            self.max_inline_depth = self.step_dying_unit_depth;
                            if self.inline_depth > self.step_dying_unit_depth {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                        self.simulate_func(ctrl, dest);
                    }
                }
            }
            StepObjectsAnalysisState::LastDyingUnit | StepObjectsAnalysisState::FreeUnits => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth < self.max_inline_depth {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            if Some(this) == self.result.first_dying_unit {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.state == StepObjectsAnalysisState::StepActiveUnitFrame {
                                    if self.inline_depth != self.step_units_depth {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if self.state == StepObjectsAnalysisState::LastDyingUnit {
                        let value = ctrl.resolve(value);
                        let ok = ctrl.if_mem_word_offset(value, 0)
                            .is_some_and(|x| Some(x) == self.result.first_dying_unit);
                        if ok {
                            let mem = ctrl.resolve_mem(mem);
                            self.result.last_dying_unit = Some(ctx.memory(&mem));
                            self.result.unit_count = self.unit_count_candidate;
                            self.state = StepObjectsAnalysisState::FreeUnits;
                            if let Some(dying) = self.result.first_dying_unit {
                                self.list_add_tracker.reset(dying);
                            }
                            if self.inline_depth == self.max_inline_depth {
                                ctrl.end_analysis();
                            }
                            self.max_inline_depth = self.max_inline_depth.wrapping_add(1);
                            return;
                        }
                        // Check for unit_count -= 1
                        if mem.size == MemAccessSize::Mem32 {
                            let unit_count = Operand::and_masked(value).0
                                .if_arithmetic_sub_const(1);
                            if let Some(unit_count) = unit_count {
                                if is_global(unit_count) {
                                    if let Some(mem2) = unit_count.if_memory() {
                                        let mem = ctrl.resolve_mem(mem);
                                        if *mem2 == mem {
                                            self.unit_count_candidate = Some(unit_count);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if self.state == StepObjectsAnalysisState::FreeUnits {
                    self.list_add_tracker.operation(ctrl, op);
                }
            }
            StepObjectsAnalysisState::StepActiveUnitFrame |
                StepObjectsAnalysisState::StepHiddenUnitFrame =>
            {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
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
                                ctrl.clear_unchecked_branches();
                                if let Some(vision_updated) = self.result.vision_updated {
                                    // Has to be done for revealer loop to run
                                    if let Some(mem) = vision_updated.if_memory() {
                                        ctrl.write_memory(mem, ctx.const_1());
                                    }
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
                        let this = ctrl.resolve_register(1);
                        let active_iscript_unit = ctrl.resolve(self.active_iscript_unit);
                        // The not Mem[x + 4] check is to avoid confusing other_list.next
                        // from loops.
                        let is_unit_next = this.if_memory()
                            .and_then(|x| x.if_offset(E::VirtualAddress::SIZE.into()))
                            .is_some();
                        if this == active_iscript_unit &&
                            this != self.first_active_unit &&
                            !is_unit_next &&
                            !this.is_undefined()
                        {
                            self.result.first_revealer = Some(this);
                            self.result.reveal_area = Some(dest);
                            self.state = StepObjectsAnalysisState::UpdateVisibilityArea;
                            return;
                        }
                        self.simulate_func(ctrl, dest);
                    }
                }
            }
            StepObjectsAnalysisState::UpdateVisibilityArea => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let this = ctrl.resolve_register(1);
                        if this == self.first_active_unit {
                            ctrl.clear_unchecked_branches();
                            self.result.update_unit_visibility = Some(dest);
                            self.state = StepObjectsAnalysisState::UpdateCloakState;
                            return;
                        }
                        self.simulate_func(ctrl, dest);
                    }
                }
            }
            StepObjectsAnalysisState::UpdateCloakState => {
                if let Operation::Jump { condition, ..} = *op {
                    if !self.cloak_state_checked {
                        let condition = ctrl.resolve(condition);
                        let ok = if_arithmetic_eq_neq(condition)
                            .filter(|x| x.1 == ctx.const_0())
                            .and_then(|x| {
                                x.0.if_arithmetic_and_const(0x3)?
                                    .if_mem8_offset(E::struct_layouts().unit_flags() + 1)
                            })
                            .is_some_and(|x| x == self.first_active_unit);
                        if ok {
                            self.cloak_state_checked = true;
                            ctrl.clear_unchecked_branches();
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if Some(dest) != self.result.update_unit_visibility {
                            if self.cloak_state_checked {
                                let this = ctrl.resolve_register(1);
                                if this == self.first_active_unit {
                                    let arg1 = ctrl.resolve_arg_thiscall(0);
                                    if arg1 == ctx.const_0() {
                                        self.result.update_cloak_state = Some(dest);
                                        self.state = StepObjectsAnalysisState::StepHiddenUnitFrame;
                                        return;
                                    }
                                }
                            }
                            self.simulate_func(ctrl, dest);
                        }
                    }
                }
            }
            StepObjectsAnalysisState::FirstInvisibleUnit => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if Some(dest) == self.result.step_hidden_frame {
                            ctrl.end_branch();
                            return;
                        }
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
                    let offset = E::struct_layouts().unit_invisibility_effects();
                    let result = if_arithmetic_eq_neq(condition)
                        .filter(|x| x.1 == ctx.const_0())
                        .and_then(|x| x.0.if_mem8_offset(offset));
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
                            let old_entry = self.func_entry;
                            self.inline_depth += 1;
                            self.func_entry = dest;
                            ctrl.analyze_with_current_state(self, dest);
                            self.func_entry = old_entry;
                            self.inline_depth = old_inline_depth;
                            if self.result.step_bullet_frame.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Move(ref dest, value) = *op {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if mem.size == E::WORD_SIZE && self.result.active_iscript_bullet.is_none() {
                            let value = ctrl.resolve(value);
                            if value == self.first_active_bullet {
                                let mem = ctrl.resolve_mem(mem);
                                let dest_op = ctx.memory(&mem);
                                if Some(dest_op) != self.result.active_iscript_flingy {
                                    self.result.active_iscript_bullet = Some(dest_op);
                                }
                            }
                        }
                    } else if let Some(_) = ctrl.if_mem_word(value) {
                        // If the instruction is a memory load from first_active_bullet,
                        // assume that this function is step_bullets
                        let value = ctrl.resolve(value);
                        if value == self.first_active_bullet {
                            self.result.step_bullets = Some(self.func_entry);
                        }
                    }
                } else if let Operation::Jump { condition, .. } = *op {
                    let condition = ctrl.resolve(condition);
                    let ok = condition.if_arithmetic_gt()
                        .and_either(|x| x.if_mem8_offset(E::struct_layouts().unit_order()))
                        .is_some_and(|x| x.0 == self.first_active_bullet);
                    if ok {
                        if Some(self.func_entry) != self.result.step_bullets {
                            self.result.step_bullet_frame = Some(self.func_entry);
                        }
                        return;
                    }
                    // Only check first jump at depth 2
                    if self.inline_depth == 2 {
                        ctrl.end_analysis();
                    }
                }
            }
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.state == StepObjectsAnalysisState::FreeUnits {
            self.list_add_tracker.branch_start(ctrl);
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.state == StepObjectsAnalysisState::FreeUnits {
            let ctx = ctrl.ctx();
            if let Some(result) = self.list_add_tracker.result(ctx) {
                self.result.first_free_unit = Some(result.head);
                self.result.last_free_unit = Some(result.tail);
                self.state = StepObjectsAnalysisState::StepActiveUnitFrame;
                if self.inline_depth != self.step_units_depth {
                    ctrl.end_analysis();
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
        let esp = ctrl.resolve_register(4);
        let ret = self.call_tracker.add_call_resolve_with_branch_limit(ctrl, func, 1, false);
        if E::VirtualAddress::SIZE == 4 {
            // Assume that the calls won't offset stack
            ctrl.set_register(4, esp);
        }
        ret
    }

    fn check_large_stack_alloc(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
        if self.first_call_of_func {
            self.first_call_of_func = false;
            return ctrl.check_stack_probe();
        }
        false
    }

    fn check_global_store_const(
        &self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
        constant: u64,
    ) -> Option<Operand<'e>> {
        if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
            let value = ctrl.resolve(value);
            if value.if_constant() == Some(constant) {
                let mem = ctrl.resolve_mem(mem);
                if mem.is_global() {
                    let ctx = ctrl.ctx();
                    return Some(ctx.memory(&mem));
                }
            }
        }
        None
    }
}
