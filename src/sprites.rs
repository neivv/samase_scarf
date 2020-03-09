use fxhash::FxHashMap;

use scarf::{MemAccessSize, Operand, Operation, DestOperand};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{Analysis, OptionExt};

pub struct Sprites<'e, Va: VirtualAddress> {
    pub sprite_hlines: Option<Operand<'e>>,
    pub sprite_hlines_end: Option<Operand<'e>>,
    pub first_free_sprite: Option<Operand<'e>>,
    pub last_free_sprite: Option<Operand<'e>>,
    pub first_lone: Option<Operand<'e>>,
    pub last_lone: Option<Operand<'e>>,
    pub first_free_lone: Option<Operand<'e>>,
    pub last_free_lone: Option<Operand<'e>>,
    pub create_lone_sprite: Option<Va>,
}

#[derive(Default)]
pub struct FowSprites<'e> {
    pub first_active: Option<Operand<'e>>,
    pub last_active: Option<Operand<'e>>,
    pub first_free: Option<Operand<'e>>,
    pub last_free: Option<Operand<'e>>,
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

pub fn sprites<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
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
        create_lone_sprite: None,
    };
    let order_nuke_track = match crate::step_order::find_order_nuke_track(analysis) {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = SpriteAnalyzer::<E> {
        state: FindSpritesState::NukeTrack,
        lone_free: Default::default(),
        lone_active: Default::default(),
        sprites_free: Default::default(),
        hlines: Default::default(),
        last_ptr_candidates: Vec::new(),
        active_list_candidate_branches: Default::default(),
        is_checking_active_list_candidate: None,
        active_list_candidate_head: None,
        active_list_candidate_tail: None,
        arg1: ctx.mem32(ctx.register(4)),
        ecx: ctx.register(1),
        create_lone_sprite: None,
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

struct SpriteAnalyzer<'e, E: ExecutionState<'e>> {
    state: FindSpritesState,
    lone_free: IncompleteList<'e>,
    lone_active: IncompleteList<'e>,
    sprites_free: IncompleteList<'e>,
    hlines: IncompleteList<'e>,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: Vec<(Operand<'e>, Operand<'e>)>,
    // Adding to active sprites is detected as
    // if (*first_active == null) {
    //     *first_active = *first_free;
    //     *last_active = *first_free;
    // }
    // If detecting such branch, store its address and first_active
    active_list_candidate_branches: FxHashMap<E::VirtualAddress, Operand<'e>>,
    is_checking_active_list_candidate: Option<Operand<'e>>,
    active_list_candidate_head: Option<Operand<'e>>,
    active_list_candidate_tail: Option<Operand<'e>>,
    // These are from looking at caller side, so arg1 == [esp]
    arg1: Operand<'e>,
    ecx: Operand<'e>,
    create_lone_sprite: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for SpriteAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(to) => {
                if let Some(dest) = ctrl.resolve(to).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let arg1 = ctrl.resolve(self.arg1);
                    if let Some(c) = arg1.if_constant() {
                        // Nuke dot sprite, either calling create lone or create sprite
                        // Their args are the same though, so cannot verify much here.
                        if c == 0xe7 {
                            let old_state = self.state;
                            self.state = match self.state {
                                FindSpritesState::NukeTrack => FindSpritesState::CreateLone,
                                FindSpritesState::CreateLone => FindSpritesState::CreateSprite,
                                FindSpritesState::CreateSprite => {
                                    // Going to inline this just in case
                                    FindSpritesState::CreateSprite
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
                                    self.state = FindSpritesState::CreateLone_Post;
                                }
                                // Guess nothing changed
                                FindSpritesState::CreateSprite => (),
                            }
                            return;
                        }
                    }
                    let ecx = ctrl.resolve(self.ecx);
                    if self.is_list_call(arg1, ecx) {
                        ctrl.analyze_with_current_state(self, dest);
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value, _) => {
                if mem.size != MemAccessSize::Mem32 {
                    return;
                }
                let ctx = ctrl.ctx();
                let dest_addr = ctrl.resolve(mem.address);
                let value = ctrl.resolve(value);
                // first_free_sprite = (*first_free_sprite).next, e.g.
                // mov [first_free_sprite], [[first_free_sprite] + 4]
                let first_sprite_next = ctx.mem32(
                    ctx.add(ctx.mem32(dest_addr), ctx.const_4()),
                );
                if value == first_sprite_next {
                    self.set_first_ptr(dest_addr.clone());
                    if let Some(last) = self.last_ptr_first_known(dest_addr) {
                        self.set_last_ptr(last);
                    }
                    return;
                }
                // last_free_sprite = (*first_free_sprite).prev
                // But not (*(*first_free_sprite).next).prev = (*first_free_sprite).prev
                if let Some(inner) = value.if_mem32().and_then(|x| x.if_mem32()) {
                    if dest_addr.iter().all(|x| x != inner) {
                        if self.is_unpaired_first_ptr(inner) {
                            self.set_last_ptr(dest_addr.clone());
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner.clone(), dest_addr.clone()));
                        }
                    }
                }
                if let Some(head_candidate) = self.is_checking_active_list_candidate {
                    // Adding to active sprites is detected as
                    // if (*first_active == null) {
                    //     *first_active = *first_free;
                    //     *last_active = *first_free;
                    // }
                    let free_list = match self.state {
                        FindSpritesState::CreateLone_Post => {
                            Some(&self.lone_free)
                        }
                        FindSpritesState::CreateSprite => {
                            Some(&self.sprites_free)
                        }
                        _ => None
                    };
                    if let Some(first_free) = free_list.and_then(|x| x.head) {
                        if let Some(_) = value.if_mem32().filter(|&x| x == first_free) {
                            if dest_addr == head_candidate {
                                self.active_list_candidate_head = Some(dest_addr.clone());
                            } else {
                                self.active_list_candidate_tail = Some(dest_addr.clone());
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                match self.state {
                    FindSpritesState::CreateLone_Post | FindSpritesState::CreateSprite => (),
                    FindSpritesState::CreateLone | FindSpritesState::NukeTrack => return,
                }
                let condition = ctrl.resolve(condition);
                let dest_addr = match ctrl.resolve(to).if_constant() {
                    Some(s) => VirtualAddress::from_u64(s),
                    None => return,
                };
                fn if_arithmetic_eq_zero<'e>(op: Operand<'e>) -> Option<Operand<'e>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                };
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(condition) {
                    Some(other) => match if_arithmetic_eq_zero(other) {
                        Some(other) => (other, false),
                        None => (other, true),
                    }
                    None => return,
                };
                if let Some(val) = val.if_mem32() {
                    let addr = match jump_if_null {
                        true => dest_addr,
                        false => ctrl.current_instruction_end(),
                    };
                    // There's also code that reads back to free lists, so ignore cases where
                    // we're looking at free list head.
                    let is_free_list_head =
                        self.lone_free.head.filter(|&x| x == val).is_some() ||
                        self.sprites_free.head.filter(|&x| x == val).is_some();
                    if !is_free_list_head {
                        self.active_list_candidate_branches.insert(addr, val.clone());
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let head_candidate = self.active_list_candidate_branches.get(&ctrl.address());
        self.is_checking_active_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        // Since hlines should be [hlines + 4 * x]
        // Prefer 4 * undefined as an 4 * (x - 1) offset will change base
        fn hlines_base<'e>(val: Operand<'e>) -> Option<Operand<'e>> {
            val.if_arithmetic_add()
                .and_either(|x| x.if_arithmetic_mul())
                .filter(|&((l, r), _)| {
                    Operand::either(l, r, |x| x.if_constant().filter(|&x| x == 4))
                        .filter(|(_, other)| other.is_undefined())
                        .is_some()
                })
                .map(|(_, base)| base)
        }

        if let Some(_) = self.is_checking_active_list_candidate.take() {
            let head = self.active_list_candidate_head.take();
            let tail = self.active_list_candidate_tail.take();
            if let (Some(head), Some(tail)) = (head, tail) {
                match self.state {
                    FindSpritesState::CreateSprite => {
                        let head = hlines_base(head);
                        let tail = hlines_base(tail);
                        if let (Some(head), Some(tail)) = (head, tail) {
                            self.hlines.head = Some(head);
                            self.hlines.tail = Some(tail);
                            self.state = FindSpritesState::CreateLone_Post;
                        }
                    }
                    FindSpritesState::CreateLone_Post => {
                        self.lone_active.head = Some(head);
                        self.lone_active.tail = Some(tail);
                        ctrl.end_analysis();
                    }
                    _ => (),
                }
            }
        }
    }
}

impl<'e, E: ExecutionState<'e>> SpriteAnalyzer<'e, E> {
    fn is_list_call(&self, arg1: Operand<'e>, ecx: Operand<'e>) -> bool {
        if let Some(addr) = ecx.if_mem32() {
            // It's remove call if ecx == [arg1], (item == [head])
            if addr == arg1 {
                return true;
            }
            // Add call if ecx == [free_head]
            // Check to not go into AddOverlay, as ecx == sprite == [free_head]
            // AddOverlay's first argument is Mem16, and a pointer can obviously never be Mem16
            if arg1.if_memory().filter(|x| x.size != MemAccessSize::Mem32).is_none() {
                if let Some(head) = self.lone_free.head {
                    if addr == head {
                        return true;
                    }
                }
                if let Some(head) = self.sprites_free.head {
                    if addr == head {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1.clone())
    }

    fn is_unpaired_first_ptr(&self, first: Operand<'e>) -> bool {
        match self.state {
            FindSpritesState::CreateLone => {
                if let Some(_) = self.lone_free.head.filter(|&x| x == first) {
                    return self.lone_free.tail.is_none();
                }
            }
            FindSpritesState::CreateSprite => {
                if let Some(_) = self.sprites_free.head.filter(|&x| x == first) {
                    return self.sprites_free.tail.is_none();
                }
            }
            _ => (),
        }
        false
    }

    fn set_first_ptr(&mut self, value: Operand<'e>) {
        if self.lone_free.head.is_none() {
            self.state = FindSpritesState::CreateLone;
            self.lone_free.head = Some(value);
        } else if self.sprites_free.head.is_none() {
            // Check for duplicate lone set
            if self.lone_free.head.filter(|&x| x == value).is_none() {
                self.state = FindSpritesState::CreateSprite;
                self.sprites_free.head = Some(value);
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
        if let Some(_old) = out {
            test_assert_eq!(*_old, value);
            return;
        }
        *out = Some(value);
    }
}

pub fn fow_sprites<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> FowSprites<'e> {
    // step_orders calls a function that loops through
    // lone sprites, followed by a loop through fow sprites.
    // That fow stepping code can also move from active -> free list,
    // so can get all 4 pointers from that.
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let mut result = FowSprites::default();
    let step_objects = match analysis.step_objects() {
        Some(s) => s,
        None => return result,
    };
    let first_lone = match analysis.sprites().first_lone {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = FowSpriteAnalyzer::<E> {
        state: FowSpritesState::InStepOrders,
        inline_depth: 0,
        first_lone,
        free: Default::default(),
        active: Default::default(),
        last_ptr_candidates: Vec::new(),
        free_list_candidate_branches: Default::default(),
        is_checking_free_list_candidate: None,
        free_list_candidate_head: None,
        free_list_candidate_tail: None,
        ecx: ctx.register(1),
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

struct FowSpriteAnalyzer<'e, E: ExecutionState<'e>> {
    state: FowSpritesState,
    inline_depth: u8,
    free: IncompleteList<'e>,
    active: IncompleteList<'e>,
    // Explanation for these is at SpriteAnalyzer
    last_ptr_candidates: Vec<(Operand<'e>, Operand<'e>)>,
    free_list_candidate_branches: FxHashMap<E::VirtualAddress, Operand<'e>>,
    is_checking_free_list_candidate: Option<Operand<'e>>,
    free_list_candidate_head: Option<Operand<'e>>,
    free_list_candidate_tail: Option<Operand<'e>>,
    ecx: Operand<'e>,
    first_lone: Operand<'e>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FowSpriteAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.state == FowSpritesState::InStepOrders {
            // Check for x <= [first_lone_sprite],
            // if found write 0 to [first_lone_sprite]
            // (Skipping lone sprite loop) and switch to StepLoneSpritesFound
            // Ideally the next thing being handled should be fow sprites.
            if let Operation::Move(_, value, None) = *op {
                let value = ctrl.resolve(value);
                let is_first_lone = value.if_mem32()
                    .filter(|&x| x == self.first_lone)
                    .is_some();
                if is_first_lone {
                    self.state = FowSpritesState::StepLoneSpritesFound;
                    self.inline_depth = 0;
                    let ctx = ctrl.ctx();
                    let state = ctrl.exec_state();
                    state.move_to(&DestOperand::from_oper(value), ctx.const_0());
                }
                return;
            }
        }
        match *op {
            Operation::Call(to) => {
                if self.inline_depth >= 2 {
                    return;
                }
                if let Some(dest) = ctrl.resolve(to).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
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
                            let ecx = ctrl.resolve(self.ecx);
                            if ecx.if_mem32().is_none() {
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
            Operation::Move(DestOperand::Memory(ref mem), value, _) => {
                if mem.size != MemAccessSize::Mem32 {
                    return;
                }
                if self.state != FowSpritesState::StepLoneSpritesFound {
                    return;
                }
                // The free/active logic is opposite from SpriteAnalyzer, as this function
                // frees fow sprites while the function SpriteAnalyzer checks allocates sprites
                let ctx = ctrl.ctx();
                let dest_addr = ctrl.resolve(mem.address);
                let value = ctrl.resolve(value);
                // first_active_sprite = (*first_active_sprite).next, e.g.
                // mov [first_active_sprite], [[first_active_sprite] + 4]
                let first_sprite_next = ctx.mem32(
                    ctx.add(ctx.mem32(dest_addr), ctx.const_4())
                );
                if value == first_sprite_next {
                    self.active.head = Some(dest_addr);
                    if let Some(last) = self.last_ptr_first_known(dest_addr) {
                        self.active.tail = Some(last);
                    }
                    return;
                }
                // last_active_sprite = (*first_active_sprite).prev
                // But not (*(*first_active_sprite).next).prev = (*first_active_sprite).prev
                if let Some(inner) = value.if_mem32().and_then(|x| x.if_mem32()) {
                    if dest_addr.iter().all(|x| x != inner) {
                        if self.is_unpaired_first_ptr(inner) {
                            self.active.tail = Some(dest_addr);
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner.clone(), dest_addr));
                        }
                    }
                }
                if let Some(head_candidate) = self.is_checking_free_list_candidate {
                    // Adding to free sprites is detected as
                    // if (*first_free == null) {
                    //     *first_free = *first_active;
                    //     *last_free = *first_active;
                    // }
                    let active_list = &self.active;
                    if let Some(first_active) = active_list.head {
                        if let Some(_) = value.if_mem32().filter(|&x| x == first_active) {
                            if dest_addr == head_candidate {
                                self.free_list_candidate_head = Some(dest_addr);
                            } else {
                                self.free_list_candidate_tail = Some(dest_addr);
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if self.state != FowSpritesState::StepLoneSpritesFound {
                    return;
                }
                let condition = ctrl.resolve(condition);
                let dest_addr = match ctrl.resolve(to).if_constant() {
                    Some(s) => VirtualAddress::from_u64(s),
                    None => return,
                };
                fn if_arithmetic_eq_zero<'e>(op: Operand<'e>) -> Option<Operand<'e>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                };
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(condition) {
                    Some(other) => match if_arithmetic_eq_zero(other) {
                        Some(other) => (other, false),
                        None => (other, true),
                    }
                    None => return,
                };
                if let Some(val) = val.if_mem32() {
                    let addr = match jump_if_null {
                        true => dest_addr,
                        false => ctrl.current_instruction_end(),
                    };
                    self.free_list_candidate_branches.insert(addr, val.clone());
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let head_candidate = self.free_list_candidate_branches.get(&ctrl.address());
        self.is_checking_free_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if let Some(_) = self.is_checking_free_list_candidate.take() {
            let head = self.free_list_candidate_head.take();
            let tail = self.free_list_candidate_tail.take();
            if let (Some(head), Some(tail)) = (head, tail) {
                self.free.head = Some(head);
                self.free.tail = Some(tail);
                ctrl.end_analysis();
            }
        }
    }
}

impl<'e, E: ExecutionState<'e>> FowSpriteAnalyzer<'e, E> {
    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1.clone())
    }

    fn is_unpaired_first_ptr(&self, first: Operand<'e>) -> bool {
        if let Some(_) = self.active.head.filter(|&x| x == first) {
            return self.active.tail.is_none();
        }
        false
    }
}
