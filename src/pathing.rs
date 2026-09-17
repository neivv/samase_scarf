use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::ArithOpType;
use scarf::{DestOperand, MemAccess, MemAccessSize, Operand, Operation};

use bumpalo::collections::Vec as BumpVec;

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::call_tracker::CallTracker;
use crate::switch::simple_switch_branch;
use crate::switch::CompleteSwitch;
use crate::util::{
    ControlExt, ExecStateExt, OperandExt, OptionExt, bumpvec_with_capacity, single_result_assign,
};

#[derive(Clone, Debug)]
pub struct RegionRelated<'e, Va: VirtualAddress> {
    pub get_region: Option<Va>,
    pub ai_regions: Option<Operand<'e>>,
    pub change_ai_region_state: Option<Va>,
}

pub(crate) struct StepUnitMovement<Va: VirtualAddress> {
    pub make_path: Option<Va>,
}

pub(crate) struct MakePath<Va: VirtualAddress> {
    pub calculate_path: Option<Va>,
}

pub(crate) fn regions<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    aiscript_hook: &crate::AiScriptHook<'e, E::VirtualAddress>,
) -> RegionRelated<'e, E::VirtualAddress> {
    let mut result = RegionRelated {
        get_region: None,
        ai_regions: None,
        change_ai_region_state: None,
    };

    // Find things through aiscript value_area
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let value_area = match simple_switch_branch(binary, aiscript_hook.switch_table, 0x2a) {
        Some(s) => s,
        None => return result,
    };
    // Set script->player to 0, x to 999 and y to 998
    let mut state = E::initial_state(ctx, binary);
    let player = ctx.mem_access32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_player(),
    );
    let x = ctx.mem_access32(
        aiscript_hook.script_operand_at_switch,
        E::struct_layouts().ai_script_center(),
    );
    let y = x.with_offset(4);
    state.write_memory(&player, ctx.const_0());
    state.write_memory(&x, ctx.constant(999));
    state.write_memory(&y, ctx.constant(998));
    let mut analysis = FuncAnalysis::with_state(
        binary,
        ctx,
        value_area,
        state,
    );
    let mut analyzer = RegionsAnalyzer {
        result: &mut result,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct RegionsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut RegionRelated<'e, E::VirtualAddress>,
    inlining: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for RegionsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let handled = self.check_call(dest, ctrl);
                    if !handled && !self.inlining{
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inlining = false;
                    }
                }
            }
            Operation::Jump { to, .. } => {
                if !self.inlining {
                    let to = ctrl.resolve(to);
                    if to.if_constant().is_none() {
                        // Avoid switch
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> RegionsAnalyzer<'a, 'e, E> {
    /// Return true if something was added to result
    fn check_call(
        &mut self,
        dest: E::VirtualAddress,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> bool {
        let ctx = ctrl.ctx();
        match ctrl.resolve_arg_u16(1).if_constant() {
            // GetRegion(x, y) call?
            Some(998) => {
                if ctrl.resolve_arg_u16(0).if_constant() == Some(999) {
                    self.result.get_region = Some(dest);
                    return true;
                }
            }
            // SetAiRegionState call?
            Some(5) => {
                let arg1 =  ctrl.resolve_arg(0);
                let ai_regions = arg1.if_arithmetic_add()
                    .and_either_other(|x| {
                        x.if_arithmetic_mul_const(E::struct_layouts().ai_region_size())
                            .filter(|x| x.contains_undefined())
                    })
                    .and_then(|x| ctrl.if_mem_word(x));
                if let Some(ai_regions_mem) = ai_regions {
                    self.result.ai_regions = Some(ai_regions_mem.address_op(ctx));
                    self.result.change_ai_region_state = Some(dest);
                }
            }
            _ => (),
        }
        false
    }
}

pub(crate) fn pathing<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    get_region: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;

    let mut analysis = FuncAnalysis::new(binary, ctx, get_region);
    let mut analyzer = FindPathing::<E> {
        result: None,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindPathing<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindPathing<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                // Match against u16 arr pathing.map_tile_regions[]
                // So `(pathing + x * 2) + const_regions_offset`
                let addr = condition.iter_no_mem_addr()
                    .flat_map(|x| {
                        x.if_mem16_offset(E::struct_layouts().pathing_map_tile_regions())
                    })
                    .next();
                if let Some(addr) = addr {
                    let val = addr.if_arithmetic_add()
                        .and_either_other(|x| x.if_arithmetic_mul_const(2));
                    if single_result_assign(val, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn analyze_step_unit_movement<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    step_unit_movement: E::VirtualAddress,
) -> StepUnitMovement<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = StepUnitMovement {
        make_path: None,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, step_unit_movement);
    let mut analyzer = StepUnitMovementAnalyzer::<E> {
        result: &mut result,
        state: StepUnitMovementState::Switch,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct StepUnitMovementAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepUnitMovement<E::VirtualAddress>,
    inline_depth: u8,
    state: StepUnitMovementState,
}

enum StepUnitMovementState {
    /// Find switch on this.movement_state
    Switch,
    /// On branch 0x11, inline once to movement_state_11(this) if needed,
    /// and first call should be make_path(a1 = this, a2 = this.move_target)
    ///
    /// There can be extra calls with this = this and jumps if assertions are enabled.
    MakePath,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    StepUnitMovementAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            StepUnitMovementState::Switch => {
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        let exec = ctrl.exec_state();
                        if let Some(switch) = CompleteSwitch::new(to, ctx, exec) {
                            let binary = ctrl.binary();
                            if let Some(branch) = switch.branch(binary, ctx, 0x11) {
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(branch);
                                self.state = StepUnitMovementState::MakePath;
                            }
                        }
                    }
                }
            }
            StepUnitMovementState::MakePath => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve_arg(0);
                        let a2 = ctrl.resolve_arg(1);
                        let ok = a1 == ctx.register(1) &&
                            a2.if_mem32_offset(E::struct_layouts().flingy_move_target()) ==
                                Some(ctx.register(1));
                        if ok {
                            self.result.make_path = Some(dest);
                        } else {
                            if ctrl.resolve_register(1) == ctx.register(1) &&
                                self.inline_depth == 0
                            {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                                if self.result.make_path.is_some() {
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

pub(crate) fn analyze_make_path<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    make_path: E::VirtualAddress,
) -> MakePath<E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let bump = &actx.bump;

    let mut result = MakePath {
        calculate_path: None,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, make_path);
    let mut analyzer = MakePathAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: MakePathState::CollisionFlag,
        inline_depth: 0,
        call_tracker: CallTracker::with_capacity(actx, 0, 32),
        path_null_jump_seen: false,
        this_is_a1: bump.alloc_slice_copy(
            &[(DestOperand::register(1), actx.arg_cache.on_entry(0))]
        ),
        maybe_region_ids: bumpvec_with_capacity(0x20, bump),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct MakePathAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut MakePath<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    state: MakePathState,
    call_tracker: CallTracker<'acx, 'e, E>,
    path_null_jump_seen: bool,
    /// For call_tracker(this = a1) calls
    this_is_a1: &'acx [(DestOperand<'e>, Operand<'e>)],
    maybe_region_ids: BumpVec<'acx, Operand<'e>>,
}

enum MakePathState {
    /// Find jump on a1.flags & 0010_0000, follow neq
    CollisionFlag,
    /// Inline once to create_complex_path(a1 = a1, a2, _)
    /// find at least one (usually two) a1.path == 0 jump, follow zero branches
    /// After that inline to calculate_path_for_unit(a1 = path_ctx), with
    /// path_ctx.x0 == a1
    /// Then find path_ctx.start_region != path_ctx.end_region jump, follow neq branch
    PathIsNullJumps,
    /// Should be next call with func(a1 = path_ctx)
    CalculatePath,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    MakePathAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            MakePathState::CollisionFlag => {
                self.track_call_if_this_unit(ctrl, op);
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let condition =
                        self.call_tracker.resolve_calls_with_branch_limit(condition, 4);
                    let ok = condition.if_and_mask_eq_neq(0x10)
                        .filter(|x| {
                            x.0.if_mem8_offset(E::struct_layouts().unit_flags() + 2) ==
                                Some(self.arg_cache.on_entry(0))
                        })
                        .map(|x| x.1);
                    if let Some(eq) = ok {
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_neq_address(eq, to);
                        self.state = MakePathState::PathIsNullJumps;
                    }
                }
            }
            MakePathState::PathIsNullJumps => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let condition =
                        self.call_tracker.resolve_calls_with_branch_limit(condition, 4);
                    let ok = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| {
                            ctrl.if_mem_word_offset(x.0, E::struct_layouts().unit_path()) ==
                                Some(self.arg_cache.on_entry(0))
                        })
                        .map(|x| x.1);
                    if let Some(eq) = ok {
                        self.path_null_jump_seen = true;
                        ctrl.clear_unchecked_branches();
                        ctrl.continue_at_eq_address(eq, to);
                        return;
                    }
                }
                if !self.path_null_jump_seen {
                    if self.inline_depth == 0 {
                        if let Operation::Call(dest) = *op {
                            let inline = ctrl.resolve_arg(0) ==
                                self.arg_cache.on_entry(0) &&
                                ctrl.resolve_arg_u32(1) ==
                                    ctx.and_const(self.arg_cache.on_entry(1), 0xffff_ffff);
                            if inline {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.inline_depth = 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth = 0;
                                    if self.result.calculate_path.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                } else {
                    if self.inline_depth < 2 {
                        if let Operation::Call(dest) = *op {
                            let a1 = ctrl.resolve_arg(0);
                            let mem = ctx.mem_access(a1, 0, E::WORD_SIZE);
                            let is_path_ctx = ctrl.read_memory(&mem) ==
                                self.arg_cache.on_entry(0);
                            if is_path_ctx {
                                if let Some(dest) = ctrl.resolve_va(dest) {
                                    self.inline_depth += 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                    if self.result.calculate_path.is_some() {
                                        ctrl.end_analysis();
                                    }
                                }
                            }
                        }
                    }
                    if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                        // Skip past potential u16 stores from func returns to path_ctx so that
                        // it's simpler to check the jump condition
                        if mem.size == MemAccessSize::Mem16 {
                            let value = ctrl.resolve(value).unwrap_and_mask();
                            if value.is_undefined() || value.if_custom().is_some() {
                                ctrl.skip_operation();
                                if value.is_undefined() {
                                    self.maybe_region_ids.push(value);
                                }
                            }
                        }
                    } else if let Operation::Jump { condition, to } = *op {
                        let condition = ctrl.resolve(condition);
                        let ok = condition.if_arithmetic_eq_neq()
                            .and_then(|x| {
                                (|| {
                                    let a = x.0.if_mem16()?;
                                    let b = x.1.if_mem16()?;
                                    let (a_base, a_offset) = a.address();
                                    let (b_base, b_offset) = b.address();
                                    if a_base == b_base && (
                                        a_offset.wrapping_add(2) == b_offset ||
                                        b_offset.wrapping_add(2) == a_offset
                                    ) {
                                        Some(x.2)
                                    } else {
                                        None
                                    }
                                })().or_else(|| {
                                    if self.maybe_region_ids.is_empty() {
                                        return None;
                                    }
                                    // Allow one be undef due to codegen doing
                                    // ctx.start_region = func()
                                    // register = func()
                                    // ctx.end_region = register
                                    // if ctx.start_region == register
                                    let first = x.0.unwrap_and_mask();
                                    if first.is_undefined() &&
                                        self.maybe_region_ids.contains(&first)
                                    {
                                        x.1.if_mem16()?;
                                        return Some(x.2);
                                    }
                                    let first = x.1.unwrap_and_mask();
                                    if first.is_undefined() &&
                                        self.maybe_region_ids.contains(&first)
                                    {
                                        x.0.if_mem16()?;
                                        return Some(x.2);
                                    }
                                    None
                                })
                            });
                        if let Some(eq) = ok {
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_neq_address(eq, to);
                            self.state = MakePathState::CalculatePath;
                        }
                    }
                }
                self.track_call_if_this_unit(ctrl, op);
            }
            MakePathState::CalculatePath => {
                if let Operation::Call(dest) = *op {
                    let a1 = ctrl.resolve_arg(0);
                    let mem = ctrl.mem_access_word(a1, 0);
                    let is_path_ctx = ctrl.read_memory(&mem) == self.arg_cache.on_entry(0);
                    if is_path_ctx {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.result.calculate_path = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> MakePathAnalyzer<'a, 'acx, 'e, E> {
    fn track_call_if_this_unit(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: &Operation<'e>,
    ) {
        if let Operation::Call(dest) = *op {
            if ctrl.resolve_register(1) == self.arg_cache.on_entry(0) {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    self.call_tracker.add_call_with_state(ctrl, dest, self.this_is_a1);
                }
            }
        }
    }
}

/// Layout of the pathfinder's dynamically sized obstacle edge arrays.
///
/// The arrays do not live in the pathing state block itself; the block ends with a pointer to
/// a small heap struct that owns them, so copying the pathing state means following that
/// pointer and sizing each array from the count stored next to it.
#[derive(Copy, Clone, Default, Debug)]
pub struct DynamicPathing {
    /// Offset of the pointer to the edge array struct inside the pathing state block.
    pub state_offset: u32,
    /// Byte size of the struct that pointer points at.
    pub struct_size: u32,
    /// In the order their pointers are laid out in the struct.
    pub edge_arrays: [DynamicPathingEdgeArray; 4],
}

/// One obstacle edge array, as offsets inside the struct that owns the four of them.
#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub struct DynamicPathingEdgeArray {
    pub ptr_offset: u16,
    pub count_offset: u16,
    pub capacity_offset: u16,
    /// Byte size of one edge, from the scaling applied to the count and the capacity.
    pub entry_size: u16,
}

impl DynamicPathingEdgeArray {
    fn unset() -> DynamicPathingEdgeArray {
        DynamicPathingEdgeArray {
            ptr_offset: u16::MAX,
            count_offset: u16::MAX,
            capacity_offset: u16::MAX,
            entry_size: 0,
        }
    }

    fn is_complete(&self) -> bool {
        self.entry_size != 0 &&
            self.ptr_offset != u16::MAX &&
            self.count_offset != u16::MAX &&
            self.capacity_offset != u16::MAX
    }
}

/// Finds the edge array struct that hangs off the end of the pathing state block.
///
/// The pathing state's allocation is followed by the calls that set the block up, one of which
/// allocates the edge array struct and stores it near the block's end; that store gives the
/// offset and the struct's size. The four arrays are then set up and grown by functions taking
/// the struct, and growing one both zero fills it to its capacity and copies its live entries
/// over, scaling both by the edge size; those two calls name the capacity, the count and the
/// pointer of each array.
pub(crate) fn dynamic_pathing<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    pathing: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> DynamicPathing {
    let binary = actx.binary;
    let ctx = actx.ctx;
    let mut result = DynamicPathing::default();
    let address = match pathing.if_memory().and_then(|x| x.if_constant_address()) {
        Some(s) => s,
        None => return result,
    };
    let funcs = functions.functions();
    let global_refs = functions.find_functions_using_global(
        actx,
        E::VirtualAddress::from_u64(address),
    );
    let mut setup_funcs = FuncList::<E>::new();
    let mut allocators = FuncList::<E>::new();
    for global_ref in &global_refs {
        let allocator = entry_of_until(binary, &funcs, global_ref.use_address, |entry| {
            let mut analyzer = FindPathingStateSetup::<E> {
                pathing_address: address,
                allocated: false,
                setup_funcs: &mut setup_funcs,
                phantom: Default::default(),
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            match analyzer.allocated {
                true => EntryOf::Ok(entry),
                false => EntryOf::Retry,
            }
        }).into_option();
        if let Some(allocator) = allocator {
            allocators.push(allocator);
        }
    }
    // Some builds keep the allocation and its zero fill in a function of their own, leaving
    // the setup calls in its caller.
    for &allocator in allocators.iter() {
        for &caller in functions.find_callers(actx, allocator).iter() {
            entry_of_until(binary, &funcs, caller, |entry| {
                let mut analyzer = FindPathingStateSetup::<E> {
                    pathing_address: address,
                    allocated: true,
                    setup_funcs: &mut setup_funcs,
                    phantom: Default::default(),
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, entry);
                analysis.analyze(&mut analyzer);
                EntryOf::Stop::<()>
            });
        }
    }
    let mut users = FuncList::<E>::new();
    let mut tail_users = FuncList::<E>::new();
    for &func in setup_funcs.iter() {
        let mut analyzer = FindEdgeArrayStruct::<E> {
            state_offset: 0,
            struct_size: 0,
            dynamic_state: None,
            users: &mut users,
            tail_users: &mut tail_users,
            call_sizes: [0; 0x20],
            call_count: 0,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if analyzer.struct_size != 0 {
            result.state_offset = analyzer.state_offset;
            result.struct_size = analyzer.struct_size;
            break;
        }
        users.clear();
        tail_users.clear();
    }
    if result.struct_size == 0 {
        return result;
    }
    let arrays = edge_arrays(actx, &users, &tail_users);
    if arrays.iter().all(|x| x.is_complete()) {
        result.edge_arrays = arrays;
        result.edge_arrays.sort_unstable_by_key(|x| x.ptr_offset);
    }
    result
}

/// Small set of function addresses, kept in call order and without duplicates.
struct FuncList<'e, E: ExecutionState<'e>> {
    funcs: [E::VirtualAddress; 0x20],
    len: usize,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> FuncList<'e, E> {
    fn new() -> FuncList<'e, E> {
        FuncList {
            funcs: [E::VirtualAddress::from_u64(0); 0x20],
            len: 0,
            phantom: Default::default(),
        }
    }

    fn push(&mut self, func: E::VirtualAddress) {
        if self.len < self.funcs.len() && !self.funcs[..self.len].contains(&func) {
            self.funcs[self.len] = func;
            self.len += 1;
        }
    }

    fn clear(&mut self) {
        self.len = 0;
    }

    fn iter(&self) -> impl Iterator<Item = &E::VirtualAddress> {
        self.funcs[..self.len].iter()
    }
}

/// Collects the functions the pathing state is handed to once it has been allocated.
struct FindPathingStateSetup<'a, 'e, E: ExecutionState<'e>> {
    pathing_address: u64,
    allocated: bool,
    setup_funcs: &'a mut FuncList<'e, E>,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindPathingStateSetup<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.allocated {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.setup_funcs.push(dest);
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), _) => {
                if !self.allocated {
                    let mem = ctrl.resolve_mem(mem);
                    if mem.if_constant_address() == Some(self.pathing_address) {
                        self.allocated = true;
                    }
                }
            }
            _ => (),
        }
    }
}

/// Looks for the allocation of the edge array struct into the block the function was given.
struct FindEdgeArrayStruct<'a, 'e, E: ExecutionState<'e>> {
    state_offset: u32,
    struct_size: u32,
    /// Value that was stored to the edge array struct pointer inside the state.
    dynamic_state: Option<Operand<'e>>,
    /// Functions that are handed the edge array struct.
    users: &'a mut FuncList<'e, E>,
    /// Functions the struct is jumped to with rather than called.
    tail_users: &'a mut FuncList<'e, E>,
    /// Constant first arguments of the calls made so far, in Custom id order.
    call_sizes: [u64; 0x20],
    call_count: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindEdgeArrayStruct<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        // The builder is reached by a tail jump from the function that allocates the struct.
        // Whether esp is back at its entry value cannot be told after a 32-bit call of unknown
        // stack cleanup, so the jump is recognized by it carrying the struct instead.
        if let Operation::Jump { condition, to } = *op {
            if condition == ctx.const_1() &&
                self.dynamic_state == Some(ctrl.resolve_register(1))
            {
                if let Some(dest) = ctrl.resolve_va(to) {
                    self.tail_users.push(dest);
                }
            }
        }
        match *op {
            Operation::Call(dest) => {
                let arg1 = ctrl.resolve_arg(0);
                // The struct is passed on the stack by some of these functions and in a
                // register by others, so accept either.
                let takes_struct = self.dynamic_state.is_some() &&
                    (self.dynamic_state == Some(arg1) ||
                        self.dynamic_state == Some(ctrl.resolve_register(1)));
                if takes_struct {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.users.push(dest);
                    }
                    return;
                }
                // Tag every allocation's return value with the size it was asked for, so that
                // the store into the block says which call made it.
                if let Some(size) = arg1.if_constant().filter(|&x| x > 0x8 && x < 0x8000_0000) {
                    let used = self.call_count as usize;
                    let index = match self.call_sizes[..used].iter().position(|&x| x == size) {
                        Some(s) => Some(s),
                        None if used < self.call_sizes.len() => {
                            self.call_sizes[used] = size;
                            self.call_count += 1;
                            Some(used)
                        }
                        None => None,
                    };
                    if let Some(index) = index {
                        ctrl.do_call_with_result(ctx.custom(index as u32));
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                if self.dynamic_state.is_some() {
                    return;
                }
                let value = ctrl.resolve(value);
                let size = value.if_custom()
                    .and_then(|x| self.call_sizes.get(x as usize).copied());
                let Some(size) = size else {
                    return;
                };
                let mem = ctrl.resolve_mem(mem);
                let (base, offset) = mem.address();
                // The pointer is the last field of a block megabytes in size, so an offset
                // that large cannot belong to some other struct being built here.
                if base.if_constant().is_none() && offset > 0x1000 && offset < 0x8000_0000 {
                    self.state_offset = offset as u32;
                    self.struct_size = size as u32;
                    self.dynamic_state = Some(value);
                }
            }
            _ => (),
        }
    }
}

/// Reads the four edge arrays' fields out of the functions that size them.
///
/// Analyzed one function at a time so that the struct's fields stay unknown memory instead of
/// the values its own setup code would have simulated into them. No single function has to
/// name every field: the one that fills a fresh array names its capacity, the one that copies
/// a live array names its count, and the results merge on the array's pointer offset. A
/// function that only passes the struct on adds its callees to the ones left to look at.
fn edge_arrays<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    users: &FuncList<'e, E>,
    tail_users: &FuncList<'e, E>,
) -> [DynamicPathingEdgeArray; 4] {
    let mut result = [DynamicPathingEdgeArray::unset(); 4];
    let mut array_count = 0;
    let mut queue = FuncList::<E>::new();
    for &user in users.iter().chain(tail_users.iter()) {
        queue.push(user);
    }
    let direct = queue.len;
    let mut index = 0;
    while index < queue.len {
        let func = queue.funcs[index];
        // The builder passes the struct on to the function that resizes one array, so its
        // callees are looked at too when it does not name every field itself.
        let expand = index < direct;
        index += 1;
        let mut analyzer = EdgeArrayAnalyzer::<E> {
            base: None,
            result: &mut result,
            array_count: &mut array_count,
            queue: &mut queue,
            expand,
            pending_fills: [(None, 0, 0); 8],
            pending_fill_count: 0,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(actx.binary, actx.ctx, func);
        analysis.analyze(&mut analyzer);
        if result.iter().all(|x| x.is_complete()) {
            break;
        }
    }
    result
}

struct EdgeArrayAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    /// Operand the struct's fields are read relative to; whatever the function was passed in.
    base: Option<Operand<'e>>,
    result: &'a mut [DynamicPathingEdgeArray; 4],
    array_count: &'a mut u8,
    queue: &'a mut FuncList<'e, E>,
    /// Whether the callees of this function should be looked at as well.
    expand: bool,
    /// (destination, capacity offset, entry size) of zero fills whose destination has not
    /// been tied to an array pointer yet.
    pending_fills: [(Option<Operand<'e>>, u16, u16); 8],
    pending_fill_count: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'a, 'e, E: ExecutionState<'e>> EdgeArrayAnalyzer<'a, 'e, E> {
    /// Slot for the array whose pointer is at `ptr_offset`, allocating one if it is new.
    fn array_mut(&mut self, ptr_offset: u16) -> Option<&mut DynamicPathingEdgeArray> {
        let count = *self.array_count as usize;
        let existing = self.result[..count].iter().position(|x| x.ptr_offset == ptr_offset);
        let index = match existing {
            Some(s) => s,
            None => {
                if count >= self.result.len() {
                    return None;
                }
                self.result[count].ptr_offset = ptr_offset;
                *self.array_count = count as u8 + 1;
                count
            }
        };
        Some(&mut self.result[index])
    }

    /// Offset of the struct field that `op` reads, if it reads one.
    fn field_offset(&self, op: Operand<'e>) -> Option<u16> {
        self.mem_field_offset(op.if_memory()?)
    }

    fn mem_field_offset(&self, mem: &MemAccess<'e>) -> Option<u16> {
        let (base, offset) = mem.address();
        if Some(base) != self.base {
            return None;
        }
        u16::try_from(offset).ok()
    }

    /// Records what a zero fill or a copy of one array says about its fields.
    fn check_resize_call(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let ctx = ctrl.ctx();
        let Some((field, entry_size)) = scaled_struct_field(ctrl.resolve_arg(2)) else {
            return;
        };
        if self.base.is_none() {
            let (base, _) = field.address();
            if base.if_constant().is_some() {
                return;
            }
            self.base = Some(base);
        }
        let Some(field_offset) = self.mem_field_offset(field) else {
            return;
        };
        let dest = ctrl.resolve_arg(0);
        let source = ctrl.resolve_arg(1);
        if source == ctx.const_0() {
            // memset(array, 0, capacity * entry_size). A growing array is zeroed before it is
            // copied into, so there the destination is the new buffer, not the field.
            if let Some(ptr_offset) = self.field_offset(dest) {
                if let Some(array) = self.array_mut(ptr_offset) {
                    array.capacity_offset = field_offset;
                    array.entry_size = entry_size;
                }
            } else {
                let index = self.pending_fill_count as usize;
                if index < self.pending_fills.len() {
                    self.pending_fills[index] = (Some(dest), field_offset, entry_size);
                    self.pending_fill_count += 1;
                }
            }
        } else if let Some(ptr_offset) = self.field_offset(source) {
            // memmove(new_array, array, count * entry_size)
            let capacity = self.pending_fills.iter()
                .take(self.pending_fill_count as usize)
                .find(|x| x.0 == Some(dest))
                .map(|&(_, capacity_offset, _)| capacity_offset);
            if let Some(array) = self.array_mut(ptr_offset) {
                array.count_offset = field_offset;
                array.entry_size = entry_size;
                if let Some(capacity_offset) = capacity {
                    array.capacity_offset = capacity_offset;
                }
            }
        }
    }
}

/// Splits `sext(Mem[base + offset]) * entry_size` into the field access and the multiplier.
///
/// A field that was just stepped reads as `field + step`, so a constant added to it is
/// dropped; the field is what names the array, not the value being asked for.
fn scaled_struct_field<'e>(op: Operand<'e>) -> Option<(&'e MemAccess<'e>, u16)> {
    let (inner, scale) = op.if_arithmetic(ArithOpType::Lsh)
        .and_then(|(l, r)| Some((l, 1u64.checked_shl(u32::try_from(r.if_constant()?).ok()?)?)))
        .or_else(|| {
            let (l, r) = op.if_arithmetic(ArithOpType::Mul)?;
            Some((l, r.if_constant()?))
        })?;
    let scale = u16::try_from(scale).ok().filter(|&x| x > 1)?;
    let unscaled = inner.unwrap_and_mask().unwrap_sext().unwrap_and_mask();
    Some((unscaled.add_sub_offset().0.if_memory()?, scale))
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for EdgeArrayAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let Operation::Call(dest) = *op else {
            return;
        };
        // The builders reserve their scratch with a stack probe, which has to be stepped over
        // for the rest of the function to make any sense.
        if ctrl.check_stack_probe() {
            return;
        }
        if self.expand {
            if let Some(dest) = ctrl.resolve_va(dest) {
                self.queue.push(dest);
            }
        }
        self.check_resize_call(ctrl);
        if self.result.iter().all(|x| x.is_complete()) {
            ctrl.end_analysis();
        }
    }
}
