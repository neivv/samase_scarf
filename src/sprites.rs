use bumpalo::collections::Vec as BumpVec;

use scarf::{MemAccessSize, Operand, Operation, DestOperand, Rva, BinaryFile, OperandCtx};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{MemAccess};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::hash_map::HashMap;
use crate::linked_list::DetectListAdd;
use crate::util::{
    ControlExt, ExecStateExt, OperandExt, OptionExt, single_result_assign, bumpvec_with_capacity
};

pub struct Sprites<'e, Va: VirtualAddress> {
    pub sprite_hlines: Option<Operand<'e>>,
    pub sprite_hlines_end: Option<Operand<'e>>,
    pub first_free_sprite: Option<Operand<'e>>,
    pub last_free_sprite: Option<Operand<'e>>,
    pub first_lone: Option<Operand<'e>>,
    pub last_lone: Option<Operand<'e>>,
    pub first_free_lone: Option<Operand<'e>>,
    pub last_free_lone: Option<Operand<'e>>,
    pub sprite_x_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    pub sprite_y_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    pub create_lone_sprite: Option<Va>,
}

#[derive(Default)]
pub struct FowSprites<'e> {
    pub first_active: Option<Operand<'e>>,
    pub last_active: Option<Operand<'e>>,
    pub first_free: Option<Operand<'e>>,
    pub last_free: Option<Operand<'e>>,
}

#[derive(Clone)]
pub struct InitSprites<'e, Va: VirtualAddress> {
    pub init_sprites: Option<Va>,
    // U32 is sprite struct size
    pub sprites: Option<(Operand<'e>, u32)>,
}

// The functions can be inlined, so first lone can be found during either NukeTrack or
// CreateLone, but not CreateSprite
#[allow(bad_style)]
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Copy, Clone)]
enum FindSpritesState {
    NukeTrack,
    CreateLone,
    CreateSprite,
    CreateLone_Post,
}

pub(crate) fn sprites<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    order_nuke_track: E::VirtualAddress,
) -> Sprites<'e, E::VirtualAddress> {
    let mut result = Sprites {
        sprite_hlines: None,
        sprite_hlines_end: None,
        first_free_sprite: None,
        last_free_sprite: None,
        first_lone: None,
        last_lone: None,
        first_free_lone: None,
        last_free_lone: None,
        sprite_x_position: None,
        sprite_y_position: None,
        create_lone_sprite: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let arg_cache = &analysis.arg_cache;
    let mut analyzer = SpriteAnalyzer::<E> {
        state: FindSpritesState::NukeTrack,
        lone_free: Default::default(),
        lone_active: Default::default(),
        sprites_free: Default::default(),
        hlines: Default::default(),
        last_ptr_candidates: BumpVec::new_in(bump),
        create_lone_sprite: None,
        function_to_custom_map: HashMap::with_capacity_and_hasher(16, Default::default()),
        custom_to_function_map: bumpvec_with_capacity(16, bump),
        sprite_x_position: None,
        sprite_y_position: None,
        binary,
        arg_cache,
        ctx,
        list_add_tracker: DetectListAdd::new(None),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, order_nuke_track);
    analysis.analyze(&mut analyzer);
    if let Some((head, tail)) = analyzer.lone_active.get() {
        result.first_lone = Some(head);
        result.last_lone = Some(tail);
    }
    if let Some((head, tail)) = analyzer.lone_free.get() {
        result.first_free_lone = Some(head);
        result.last_free_lone = Some(tail);
    }
    if let Some((head, tail)) = analyzer.hlines.get() {
        result.sprite_hlines = Some(head);
        result.sprite_hlines_end = Some(tail);
    }
    if let Some((head, tail)) = analyzer.sprites_free.get() {
        result.first_free_sprite = Some(head);
        result.last_free_sprite = Some(tail);
    }
    result.create_lone_sprite = analyzer.create_lone_sprite;
    result.sprite_x_position = analyzer.sprite_x_position;
    result.sprite_y_position = analyzer.sprite_y_position;
    result
}

#[derive(Default)]
struct IncompleteList<'e> {
    head: Option<Operand<'e>>,
    tail: Option<Operand<'e>>,
}

impl<'e> IncompleteList<'e> {
    fn get(self) -> Option<(Operand<'e>, Operand<'e>)> {
        match (self.head, self.tail) {
            (Some(h), Some(t)) => Some((h, t)),
            _ => None,
        }
    }
}

struct SpriteAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    state: FindSpritesState,
    lone_free: IncompleteList<'e>,
    lone_active: IncompleteList<'e>,
    sprites_free: IncompleteList<'e>,
    hlines: IncompleteList<'e>,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
    create_lone_sprite: Option<E::VirtualAddress>,
    // Dest, arg1, arg2 if Mem32[x] where the resolved value is a constant
    function_to_custom_map: HashMap<(Rva, Option<u64>, Option<u64>), u32>,
    custom_to_function_map: BumpVec<'acx, ChildFunctionFormula<'e>>,
    sprite_x_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    sprite_y_position: Option<(Operand<'e>, u32, MemAccessSize)>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    arg_cache: &'acx ArgCache<'e, E>,
    ctx: OperandCtx<'e>,
    list_add_tracker: DetectListAdd<'e, E>,
}

enum ChildFunctionFormula<'e> {
    NotDone(Rva, Option<u64>, Option<u64>),
    Done(Option<Operand<'e>>, Option<Operand<'e>>, Option<Operand<'e>>),
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for SpriteAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if matches!(
            self.state,
            FindSpritesState::CreateLone_Post | FindSpritesState::CreateSprite,
        ) {
            self.list_add_tracker.operation(ctrl, op);
        }
        match *op {
            Operation::Call(to) => {
                if let Some(dest) = ctrl.resolve_va(to) {
                    let ctx = ctrl.ctx();
                    let arg1 = ctrl.resolve_arg(0);
                    if arg1.if_constant() == Some(0xe7) {
                        // Nuke dot sprite, either calling create lone or create sprite
                        // Their args are the same though, so cannot verify much here.
                        let old_state = self.state;
                        match self.state {
                            FindSpritesState::NukeTrack => {
                                self.state = FindSpritesState::CreateLone;
                            }
                            FindSpritesState::CreateLone => {
                                self.switch_to_create_sprite();
                            }
                            FindSpritesState::CreateSprite => {
                                // Going to inline this, likely initialize_sprite
                                // which will contain x/y pos
                            }
                            FindSpritesState::CreateLone_Post => {
                                ctrl.end_analysis();
                                return;
                            }
                        };
                        if self.state == FindSpritesState::CreateLone {
                            self.create_lone_sprite = Some(dest);
                        }
                        ctrl.analyze_with_current_state(self, dest);
                        match old_state {
                            FindSpritesState::NukeTrack | FindSpritesState::CreateLone_Post =>
                            {
                                ctrl.end_analysis();
                            }
                            FindSpritesState::CreateLone => {
                                self.switch_to_create_lone_post();
                            }
                            // Guess nothing changed
                            FindSpritesState::CreateSprite => (),
                        }
                        return;
                    }
                    let ecx = ctrl.resolve_register(1);
                    let tc_arg1 = ctrl.resolve_arg_thiscall(0);
                    if self.is_list_call(tc_arg1, ecx) {
                        ctrl.analyze_with_current_state(self, dest);
                    } else {
                        if self.state == FindSpritesState::CreateSprite {
                            // Check for fn(&mut val1, &mut val2) where
                            // val1 and val2 were inited with constants
                            let arg2 = ctrl.resolve_arg(1);
                            let arg1_mem = ctx.mem_access(arg1, 0, E::WORD_SIZE);
                            let arg2_mem = ctx.mem_access(arg2, 0, E::WORD_SIZE);
                            let arg1_c = ctrl.read_memory(&arg1_mem).if_constant();
                            let arg2_c = ctrl.read_memory(&arg2_mem).if_constant();
                            // Use custom(x) to keep track of called child functions
                            let rva = Rva((dest.as_u64() - self.binary.base.as_u64()) as u32);
                            let new_id = (self.function_to_custom_map.len() as u32 + 1) * 0x10;
                            let custom_id = *self.function_to_custom_map
                                .entry((rva, arg1_c, arg2_c))
                                .or_insert_with(|| new_id);
                            if custom_id == new_id {
                                self.custom_to_function_map.push(
                                    ChildFunctionFormula::NotDone(rva, arg1_c, arg2_c)
                                );
                            }
                            let state = ctrl.exec_state();
                            state.set_register(0, ctx.custom(custom_id));
                            state.set_register(1, ctx.new_undef());
                            state.set_register(2, ctx.new_undef());
                            if arg1_c.is_some() {
                                state.write_memory(&arg1_mem, ctx.custom(custom_id + 1));
                            }
                            if arg2_c.is_some() {
                                state.write_memory(&arg2_mem, ctx.custom(custom_id + 2));
                            }
                            ctrl.skip_operation();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                let dest = ctrl.resolve_mem(mem);
                let ctx = ctrl.ctx();
                let value = ctrl.resolve(value);
                if self.state == FindSpritesState::CreateSprite {
                    self.check_position_store(ctrl, &dest, value);
                }
                if dest.size != E::WORD_SIZE {
                    return;
                }
                let dest_addr = dest.address_op(ctx);
                // first_free_sprite = (*first_free_sprite).next, e.g.
                // mov [first_free_sprite], [[first_free_sprite] + 4]
                let first_sprite_next = ctrl.mem_word(
                    ctx.memory(&dest),
                    E::VirtualAddress::SIZE as u64,
                );
                if value == first_sprite_next {
                    self.set_first_ptr(dest_addr);
                    if let Some(last) = self.last_ptr_first_known(dest_addr) {
                        self.set_last_ptr(last);
                    }
                    return;
                }
                // last_free_sprite = (*first_free_sprite).prev
                // But not (*(*first_free_sprite).next).prev = (*first_free_sprite).prev
                if let Some(inner) = ctrl.if_mem_word_offset(value, 0)
                    .and_then(|x| ctrl.if_mem_word(x))
                {
                    let inner_op = inner.address_op(ctx);
                    if dest_addr.iter().all(|x| x != inner_op) {
                        if self.is_unpaired_first_ptr(inner) {
                            self.set_last_ptr(dest_addr);
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner_op, dest_addr));
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.list_add_tracker.branch_start(ctrl);
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        // Since hlines should be [hlines + 4 * x]
        // Prefer 4 * undefined as an 4 * (x - 1) offset will change base
        fn hlines_base<'e, Va: VirtualAddress>(
            ctx: OperandCtx<'e>,
            val: Operand<'e>,
        ) -> Option<Operand<'e>> {
            val.if_memory()?
                .if_add_either_other(ctx, |x| {
                    x.if_arithmetic_mul_const(Va::SIZE.into())
                        .filter(|&idx| {
                            idx.is_undefined() || Operand::and_masked(idx).0.if_custom().is_some()
                        })
                })
        }

        let ctx = ctrl.ctx();
        if let Some(result) = self.list_add_tracker.result(ctx) {
            // There's also code that reads back to free lists, so ignore cases where
            // we're looking at free list head.
            if Some(result.head) == self.lone_free.head ||
                Some(result.head) == self.sprites_free.head
            {
                return;
            }
            match self.state {
                FindSpritesState::CreateSprite => {
                    let head = hlines_base::<E::VirtualAddress>(ctx, result.head);
                    let tail = hlines_base::<E::VirtualAddress>(ctx, result.tail);
                    if let (Some(head), Some(tail)) = (head, tail) {
                        self.hlines.head = Some(head);
                        self.hlines.tail = Some(tail);
                        self.switch_to_create_lone_post();
                    }
                }
                FindSpritesState::CreateLone_Post => {
                    self.lone_active.head = Some(result.head);
                    self.lone_active.tail = Some(result.tail);
                    ctrl.end_analysis();
                }
                _ => (),
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> SpriteAnalyzer<'a, 'e, E> {
    fn switch_to_create_lone_post(&mut self) {
        self.state = FindSpritesState::CreateLone_Post;
        let first_free_lone = match self.lone_free.head {
            Some(s) => s,
            None => return,
        };
        self.list_add_tracker.reset(first_free_lone);
    }

    fn switch_to_create_sprite(&mut self) {
        self.state = FindSpritesState::CreateSprite;
        let first_free = match self.sprites_free.head {
            Some(s) => s,
            None => return,
        };
        self.list_add_tracker.reset(first_free);
    }

    fn check_position_store(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: &MemAccess<'e>,
        value: Operand<'e>,
    ) {
        fn mem16_related_offset<'e, E: ExecutionState<'e>>(op: Operand<'e>) -> Option<u32> {
            // Check for Mem16[Mem32[rcx + 80] + offset]
            // (unit.related.order_target.x)
            let (base, offset) = op.if_mem16()?.address();
            let offset: u32 = u32::try_from(offset).ok()?;
            let rcx = base.if_memory().filter(|mem| mem.size == E::WORD_SIZE)?
                .if_offset(E::struct_layouts().unit_related())?;
            rcx.if_register().filter(|&r| r == 1)?;
            Some(offset)
        }

        let ctx = ctrl.ctx();
        let first_free = match self.sprites_free.head {
            Some(s) => s,
            None => return,
        };
        let (base, offset) = dest.address();
        let offset = offset as u32;
        let storing_to_sprite = base == first_free;
        if !storing_to_sprite || offset < 0x10 {
            return;
        }
        let related_unit_offset = value.iter()
            .find_map(|op| mem16_related_offset::<E>(op));
        let mut ok = true;
        if let Some(off) = related_unit_offset {
            let value = ctx.transform(value, 16, |op| {
                if let Some(id) = op.if_custom() {
                    let val = self.resolve_custom(id);
                    if val.is_none() {
                        ok = false;
                    }
                    val
                } else if mem16_related_offset::<E>(op) == Some(off) {
                    // Explicit 16bit and mask here is better for result stability,
                    // as `Mem16[x] & ffff` and `Mem16[x]` are same, but replacing
                    // `Mem16` with 64-bit `Custom` makes them different.
                    // Obviously scarf gets rid of the `& ffff` mask in above simple case,
                    // but that is not necessarily the case for what the expression ends
                    // up being in practice.
                    Some(ctx.and_const(ctx.custom(0), 0xffff))
                } else {
                    None
                }
            });
            if ok {
                let result = (value, offset, dest.size);
                let order_target_offset = E::struct_layouts().unit_order_target_pos() as u32;
                if off == order_target_offset {
                    single_result_assign(Some(result), &mut self.sprite_x_position);
                } else if off == order_target_offset + 2 {
                    single_result_assign(Some(result), &mut self.sprite_y_position);
                }
            }
        }
    }

    fn resolve_custom(&mut self, id: u32) -> Option<Operand<'e>> {
        if id < 0x10 {
            return None;
        }
        let index = (id / 0x10) - 1;
        let (func_addr, arg1, arg2) = match *(self.custom_to_function_map.get(index as usize)?) {
            ChildFunctionFormula::NotDone(a, b, c) => (a, b, c),
            ChildFunctionFormula::Done(a, b, c) => return match id & 0xf {
                0 => a,
                1 => b,
                _ => c,
            },
        };
        let binary = self.binary;
        let addr = binary.base + func_addr.0;
        let ctx = self.ctx;
        let return_addr = required_return_addr::<E>(ctx, binary, addr);

        let mut exec_state = E::initial_state(ctx, binary);
        let state = Default::default();
        if let Some(ret) = return_addr {
            exec_state.write_memory(
                &ctx.mem_access(ctx.register(4), 0, E::WORD_SIZE),
                ctx.constant(ret.as_u64()),
            );
            exec_state.write_memory(
                &ctx.mem_access16(ctx.const_0(), ret.as_u64() - 2),
                ctx.constant(0xd0ff),
            );
        }
        if let Some(arg1) = arg1 {
            exec_state.write_memory(
                &ctx.mem_access(ctx.custom(0), 0, E::WORD_SIZE),
                ctx.constant(arg1),
            );
            exec_state.move_resolved(
                &DestOperand::from_oper(self.arg_cache.on_entry(0)),
                ctx.custom(0),
            );
        }
        if let Some(arg2) = arg2 {
            exec_state.write_memory(
                &ctx.mem_access(ctx.custom(1), 0, E::WORD_SIZE),
                ctx.constant(arg2),
            );
            exec_state.move_resolved(
                &DestOperand::from_oper(self.arg_cache.on_entry(1)),
                ctx.custom(1),
            );
        }
        let mut analyzer = ResolveCustom::<E> {
            ret: ResolveCustomResult::None,
            arg1: ResolveCustomResult::None,
            arg2: ResolveCustomResult::None,
            arg1_loc: E::operand_mem_word(ctx, ctx.custom(0), 0),
            arg2_loc: E::operand_mem_word(ctx, ctx.custom(1), 0),
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::custom_state(binary, ctx, addr, exec_state, state);
        analysis.analyze(&mut analyzer);
        let a = analyzer.ret.to_option();
        let b = analyzer.arg1.to_option();
        let c = analyzer.arg2.to_option();
        self.custom_to_function_map[index as usize] = ChildFunctionFormula::Done(a, b, c);
        match id & 0xf {
            0 => a,
            1 => b,
            _ => c,
        }
    }

    fn is_list_call(&self, arg1: Operand<'e>, ecx: Operand<'e>) -> bool {
        let word_size = E::VirtualAddress::SIZE as u64;
        if let Some(mem) = ecx.if_memory().filter(|x| x.size == E::WORD_SIZE) {
            let (base, offset) = mem.address();
            // It's remove call if ecx == [arg1], (item == [head])
            if base == arg1 && offset == 0 || Some(offset) == arg1.if_constant() {
                return true;
            }
            // Add call if ecx == [free_head]
            // Check to not go into AddOverlay, as ecx == sprite == [free_head]
            // AddOverlay's first argument is Mem16, and a pointer can obviously never be Mem16
            let arg1_ok = arg1.if_constant().is_some() ||
                arg1.if_arithmetic_add()
                    .and_either_other(|x| x.if_constant())
                    .and_then(|x| x.if_arithmetic_mul())
                    .filter(|(_, r)| r.if_constant() == Some(word_size))
                    .is_some();
            if arg1_ok {
                if let Some(head) = self.lone_free.head {
                    if ecx == head {
                        return true;
                    }
                }
                if let Some(head) = self.sprites_free.head {
                    if ecx == head {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1)
    }

    fn is_unpaired_first_ptr(&self, first: &MemAccess<'e>) -> bool {
        match self.state {
            FindSpritesState::CreateLone => {
                if let Some(_) = self.lone_free.head
                    .and_then(|x| x.if_memory())
                    .filter(|&x| x.address() == first.address())
                {
                    return self.lone_free.tail.is_none();
                }
            }
            FindSpritesState::CreateSprite => {
                if let Some(_) = self.sprites_free.head
                    .and_then(|x| x.if_memory())
                    .filter(|&x| x.address() == first.address())
                {
                    return self.sprites_free.tail.is_none();
                }
            }
            _ => (),
        }
        false
    }

    fn set_first_ptr(&mut self, value: Operand<'e>) {
        let value = E::operand_mem_word(self.ctx, value, 0);
        if self.lone_free.head.is_none() {
            self.state = FindSpritesState::CreateLone;
            self.lone_free.head = Some(value);
        } else if self.sprites_free.head.is_none() {
            // Check for duplicate lone set
            if self.lone_free.head.filter(|&x| x == value).is_none() {
                self.sprites_free.head = Some(value);
                self.switch_to_create_sprite();
            }
        }
    }

    fn set_last_ptr(&mut self, value: Operand<'e>) {
        let out = match self.state {
            FindSpritesState::CreateLone => &mut self.lone_free.tail,
            FindSpritesState::CreateSprite => &mut self.sprites_free.tail,
            x => {
                if crate::test_assertions() {
                    panic!("Setting sprite last ptr with invalid state {:?}", x);
                }
                return;
            }
        };
        let value = E::operand_mem_word(self.ctx, value, 0);
        if let Some(_old) = out {
            test_assert_eq!(*_old, value);
            return;
        }
        *out = Some(value);
    }
}

#[derive(Copy, Clone, Debug)]
enum ResolveCustomResult<'e> {
    None,
    One(Operand<'e>),
    Many,
}

impl<'e> ResolveCustomResult<'e> {
    fn update(&mut self, new: Operand<'e>) {
        match *self {
            ResolveCustomResult::None => *self = ResolveCustomResult::One(new),
            ResolveCustomResult::One(old) => if old != new {
                *self = ResolveCustomResult::Many;
            }
            ResolveCustomResult::Many => (),
        }
    }

    fn to_option(self) -> Option<Operand<'e>> {
        match self {
            ResolveCustomResult::One(op) => {
                if op.iter().any(|x| {
                    x.is_undefined() || x.if_custom().is_some() || x.if_register().is_some()
                }) {
                    None
                } else {
                    Some(op)
                }
            }
            _ => None,
        }
    }
}

struct ResolveCustom<'e, E: ExecutionState<'e>> {
    ret: ResolveCustomResult<'e>,
    arg1: ResolveCustomResult<'e>,
    arg2: ResolveCustomResult<'e>,
    arg1_loc: Operand<'e>,
    arg2_loc: Operand<'e>,
    phantom: std::marker::PhantomData<(&'e (), *const E)>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for ResolveCustom<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Return(..) => {
                let ret = ctrl.resolve_register(0);
                self.ret.update(ret);
                let arg1 = ctrl.resolve(self.arg1_loc);
                self.arg1.update(arg1);
                let arg2 = ctrl.resolve(self.arg2_loc);
                self.arg2.update(arg2);
            }
            _ => (),
        }
    }
}

fn required_return_addr<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    func: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let mut analyzer = RequiredReturnAddress::<E> {
        first: None,
        result: None,
        min_addr: func,
        max_addr: func,
    };
    let mut exec_state = E::initial_state(ctx, binary);
    let state = Default::default();
    exec_state.write_memory(
        &ctx.mem_access(ctx.register(4), 0, E::WORD_SIZE),
        ctx.custom(0),
    );
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, func, exec_state, state);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct RequiredReturnAddress<'e, E: ExecutionState<'e>> {
    first: Option<E::VirtualAddress>,
    result: Option<E::VirtualAddress>,
    min_addr: E::VirtualAddress,
    max_addr: E::VirtualAddress,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for RequiredReturnAddress<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        self.min_addr = ctrl.address().min(self.min_addr);
        self.max_addr = ctrl.address().max(self.max_addr);
        match *op {
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                let addr = condition.if_arithmetic_gt()
                    .and_either_other(|x| Operand::and_masked(x).0.if_custom())
                    .and_then(|x| x.if_constant());
                if let Some(addr) = addr {
                    match self.first {
                        None => self.first = Some(E::VirtualAddress::from_u64(addr)),
                        Some(first) => {
                            let second = E::VirtualAddress::from_u64(addr);
                            let mut result = if first < second {
                                first + 0x80
                            } else {
                                second + 0x80
                            };
                            if result >= self.min_addr && result < self.max_addr {
                                result = self.max_addr + 0x40;
                            }
                            self.result = Some(result);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn fow_sprites<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_objects: E::VirtualAddress,
    first_lone: Operand<'e>,
) -> FowSprites<'e> {
    // step_orders calls a function that loops through
    // lone sprites, followed by a loop through fow sprites.
    // That fow stepping code can also move from active -> free list,
    // so can get all 4 pointers from that.
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let mut result = FowSprites::default();

    let mut analyzer = FowSpriteAnalyzer::<E> {
        state: FowSpritesState::InStepOrders,
        inline_depth: 0,
        first_lone,
        free: Default::default(),
        active: Default::default(),
        last_ptr_candidates: BumpVec::new_in(bump),
        list_add_tracker: DetectListAdd::new(None),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, step_objects);
    analysis.analyze(&mut analyzer);
    if let Some((head, tail)) = analyzer.free.get() {
        result.first_free = Some(head);
        result.last_free = Some(tail);
    }
    if let Some((head, tail)) = analyzer.active.get() {
        result.first_active = Some(head);
        result.last_active = Some(tail);
    }
    result
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
enum FowSpritesState {
    /// In step orders.
    /// Inline to child functions, and search for a [first_lone] == 0 jump.
    InStepOrders,
    /// Found [first_lone] == 0, inline to functions that have ecx == [x] (FowSprite)
    /// or ecx == [[x] + c] (FowSprite -> sprite)
    StepLoneSpritesFound,
}

struct FowSpriteAnalyzer<'acx, 'e, E: ExecutionState<'e>> {
    state: FowSpritesState,
    inline_depth: u8,
    free: IncompleteList<'e>,
    active: IncompleteList<'e>,
    // Explanation for these is at SpriteAnalyzer
    list_add_tracker: DetectListAdd<'e, E>,
    last_ptr_candidates: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
    first_lone: Operand<'e>,
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FowSpriteAnalyzer<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.state == FowSpritesState::InStepOrders {
            // Check for x <= [first_lone_sprite],
            // if found write 0 to [first_lone_sprite]
            // (Skipping lone sprite loop) and switch to StepLoneSpritesFound
            // Ideally the next thing being handled should be fow sprites.
            if let Operation::Move(_, value) = *op {
                let value = ctrl.resolve(value);
                if value == self.first_lone {
                    if let Some(memory) = value.if_memory() {
                        self.state = FowSpritesState::StepLoneSpritesFound;
                        self.inline_depth = 0;
                        let ctx = ctrl.ctx();
                        ctrl.write_memory(memory, ctx.const_0());
                    }
                }
                return;
            }
        }
        if self.state == FowSpritesState::StepLoneSpritesFound {
            if self.active.head.is_some() {
                self.list_add_tracker.operation(ctrl, op);
            }
        }
        match *op {
            Operation::Call(to) => {
                if self.inline_depth >= 2 {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(to) {
                    match self.state {
                        FowSpritesState::InStepOrders => {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.state != FowSpritesState::InStepOrders {
                                ctrl.end_analysis();
                            } else {
                                self.inline_depth -= 1;
                            }
                        }
                        FowSpritesState::StepLoneSpritesFound => {
                            let ecx = ctrl.resolve_register(1);
                            if ctrl.if_mem_word(ecx).is_none() {
                                return;
                            }
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.active.head.is_some() && self.free.head.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                if mem.size != E::WORD_SIZE {
                    return;
                }
                if self.state != FowSpritesState::StepLoneSpritesFound {
                    return;
                }
                // The free/active logic is opposite from SpriteAnalyzer, as this function
                // frees fow sprites while the function SpriteAnalyzer checks allocates sprites
                let (address, offset) = mem.address();
                let dest_addr = ctrl.resolve(address);
                let dest_value = ctrl.mem_word(dest_addr, offset);
                let value = ctrl.resolve(value);
                // first_active_sprite = (*first_active_sprite).next, e.g.
                // mov [first_active_sprite], [[first_active_sprite] + 4]
                let first_sprite_next = ctrl.mem_word(
                    dest_value,
                    E::VirtualAddress::SIZE as u64,
                );
                if value == first_sprite_next {
                    self.active.head = Some(dest_value);
                    if let Some(last) = self.last_ptr_first_known(dest_value) {
                        self.active.tail = Some(last);
                    }
                    self.list_add_tracker.reset(dest_value);
                    return;
                }
                // last_active_sprite = (*first_active_sprite).prev
                // But not (*(*first_active_sprite).next).prev = (*first_active_sprite).prev
                if let Some(inner) = ctrl.if_mem_word_offset(value, 0)
                    .and_then(|x| ctrl.if_mem_word(x))
                {
                    let ctx = ctrl.ctx();
                    let inner_op = inner.address_op(ctx);
                    if dest_addr.iter().all(|x| x != inner_op) {
                        if self.is_unpaired_first_ptr(&inner) {
                            self.active.tail = Some(dest_value);
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner_op, dest_value));
                        }
                    }
                }
            }
            _ => (),
        }
        ctrl.aliasing_memory_fix(op);
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.active.head.is_some() {
            self.list_add_tracker.branch_start(ctrl);
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.active.head.is_some() {
            let ctx = ctrl.ctx();
            if let Some(result) = self.list_add_tracker.result(ctx) {
                self.free.head = Some(result.head);
                self.free.tail = Some(result.tail);
                ctrl.end_analysis();
            }
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> FowSpriteAnalyzer<'acx, 'e, E> {
    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1)
    }

    fn is_unpaired_first_ptr(&self, first: &MemAccess<'e>) -> bool {
        if let Some(_) = self.active.head
            .and_then(|x| x.if_memory())
            .filter(|&x| x.address() == first.address())
        {
            return self.active.tail.is_none();
        }
        false
    }
}

pub(crate) fn init_sprites<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    first_free_sprite: Operand<'e>,
    last_free_sprite: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> InitSprites<'e, E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let mut result = InitSprites {
        init_sprites: None,
        sprites: None,
    };
    let first_free_sprite_addr = match first_free_sprite.if_memory() {
        Some(s) => *s,
        None => return result,
    };
    let last_free_sprite_addr = match last_free_sprite.if_memory() {
        Some(s) => s.address_op(ctx),
        None => return result,
    };
    let str_refs = functions.string_refs(analysis, b"arr\\sprites.dat\0");
    let functions = functions.functions();
    for str_ref in str_refs {
        let val = entry_of_until(binary, &functions, str_ref.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = InitSpritesAnalyzer::<E> {
                result: &mut result,
                inlining: false,
                use_address: str_ref.use_address,
                str_ref_found: false,
                first_free_sprite_addr,
                last_free_sprite_addr,
                array_candidates: BumpVec::new_in(bump),
            };
            analysis.analyze(&mut analyzer);
            if analyzer.str_ref_found {
                if analyzer.result.sprites.is_some() {
                    EntryOf::Ok(())
                } else {
                    EntryOf::Stop
                }
            } else {
                EntryOf::Retry
            }
        }).into_option_with_entry();
        if result.sprites.is_some() {
            if let Some((addr, ())) = val {
                result.init_sprites = Some(addr);
                break;
            }
        }
    }
    result
}

struct InitSpritesAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitSprites<'e, E::VirtualAddress>,
    inlining: bool,
    use_address: E::VirtualAddress,
    str_ref_found: bool,
    first_free_sprite_addr: MemAccess<'e>,
    last_free_sprite_addr: Operand<'e>,
    array_candidates: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    InitSpritesAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.use_address >= ctrl.address() &&
            self.use_address < ctrl.current_instruction_end()
        {
            self.str_ref_found = true;
        }
        match *op {
            Operation::Call(to) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        let arg2 = ctrl.resolve_arg_thiscall(1);
                        let should_inline = arg2 == self.last_free_sprite_addr;
                        if should_inline {
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.sprites.is_some() {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                if mem.size != E::WORD_SIZE {
                    return;
                }
                let value = ctrl.resolve(value);
                let dest = ctrl.resolve_mem(mem);
                let ctx = ctrl.ctx();
                let dest_addr = dest.address_op(ctx);
                // Check for [first_free_sprite].prev = sprite_array + 1 * sprite_size
                let dest_ok = self.array_candidates.iter().any(|&(_, next)| dest_addr == next);
                if !dest_ok {
                    // Skip over initial [first_free_sprite] = &sprite_array[0]
                    if dest == self.first_free_sprite_addr {
                        let next_value = ctx.add_const(value, E::VirtualAddress::SIZE as u64);
                        self.array_candidates.push((value, next_value));
                    }
                    return;
                }
                let base_offset = value.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        let offset = r.if_constant().filter(|&c| c > 0x20 && c < 0x80)?;
                        if self.array_candidates.iter().any(|&cand| cand.0 == l) {
                            Some((l, offset as u32))
                        } else {
                            None
                        }
                    })
                    .or_else(|| {
                        let val = value.if_constant()?;
                        self.array_candidates.iter()
                            .filter_map(|&(op, _)| {
                                let base = op.if_constant()?;
                                if val > base {
                                    let offset = val - base;
                                    if offset > 0x20 && offset < 0x80 {
                                        return Some((op, offset as u32));
                                    }
                                }
                                None
                            })
                            .next()
                    });
                if let Some((base, offset)) = base_offset {
                    self.result.sprites = Some((base, offset));
                    ctrl.end_analysis();
                    return;
                }
            }
            _ => (),
        }
    }
}
