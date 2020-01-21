use std::rc::Rc;

use fxhash::FxHashMap;

use scarf::{
    MemAccessSize, Operand, OperandType, OperandContext, Operation, VirtualAddress, DestOperand,
    ExecutionStateX86,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress as VirtualAddressTrait};

use crate::{Analysis, OptionExt};

#[derive(Default)]
pub struct Sprites {
    pub sprite_hlines: Option<Rc<Operand>>,
    pub sprite_hlines_end: Option<Rc<Operand>>,
    pub first_free_sprite: Option<Rc<Operand>>,
    pub last_free_sprite: Option<Rc<Operand>>,
    pub first_lone: Option<Rc<Operand>>,
    pub last_lone: Option<Rc<Operand>>,
    pub first_free_lone: Option<Rc<Operand>>,
    pub last_free_lone: Option<Rc<Operand>>,
    pub create_lone_sprite: Option<VirtualAddress>,
}

#[derive(Default)]
pub struct FowSprites {
    pub first_active: Option<Rc<Operand>>,
    pub last_active: Option<Rc<Operand>>,
    pub first_free: Option<Rc<Operand>>,
    pub last_free: Option<Rc<Operand>>,
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

pub fn sprites<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> Sprites {
    use scarf::operand_helpers::*;

    let mut result = Sprites::default();
    let order_nuke_track = match crate::step_order::find_order_nuke_track(analysis, ctx) {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let mut analyzer = SpriteAnalyzer {
        ctx,
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
        arg1: mem32(ctx.register(4)),
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
struct IncompleteList {
    head: Option<Rc<Operand>>,
    tail: Option<Rc<Operand>>,
}

impl IncompleteList {
    fn get(self) -> Option<(Rc<Operand>, Rc<Operand>)> {
        match (self.head, self.tail) {
            (Some(h), Some(t)) => Some((h, t)),
            _ => None,
        }
    }
}

struct SpriteAnalyzer<'a> {
    ctx: &'a OperandContext,
    state: FindSpritesState,
    lone_free: IncompleteList,
    lone_active: IncompleteList,
    sprites_free: IncompleteList,
    hlines: IncompleteList,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: Vec<(Rc<Operand>, Rc<Operand>)>,
    // Adding to active sprites is detected as
    // if (*first_active == null) {
    //     *first_active = *first_free;
    //     *last_active = *first_free;
    // }
    // If detecting such branch, store its address and first_active
    active_list_candidate_branches: FxHashMap<VirtualAddress, Rc<Operand>>,
    is_checking_active_list_candidate: Option<Rc<Operand>>,
    active_list_candidate_head: Option<Rc<Operand>>,
    active_list_candidate_tail: Option<Rc<Operand>>,
    // These are from looking at caller side, so arg1 == [esp]
    arg1: Rc<Operand>,
    ecx: Rc<Operand>,
    create_lone_sprite: Option<VirtualAddress>,
}

impl<'a> scarf::Analyzer<'a> for SpriteAnalyzer<'a> {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        use scarf::operand_helpers::*;

        match *op {
            Operation::Call(ref to) => {
                if let Some(dest) = ctrl.resolve(&to).if_constant() {
                    let arg1 = ctrl.resolve(&self.arg1);
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
                                self.create_lone_sprite = Some(VirtualAddress::from_u64(dest));
                            }
                            ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
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
                    let ecx = ctrl.resolve(&self.ecx);
                    if self.is_list_call(&arg1, &ecx) {
                        ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), ref value, _) => {
                if mem.size != MemAccessSize::Mem32 {
                    return;
                }
                let dest_addr = ctrl.resolve(&mem.address);
                let value = ctrl.resolve(&value);
                // first_free_sprite = (*first_free_sprite).next, e.g.
                // mov [first_free_sprite], [[first_free_sprite] + 4]
                let first_sprite_next = Operand::simplified(
                    mem32(operand_add(mem32(dest_addr.clone()), self.ctx.const_4()))
                );
                if value == first_sprite_next {
                    self.set_first_ptr(dest_addr.clone());
                    if let Some(last) = self.last_ptr_first_known(&dest_addr) {
                        self.set_last_ptr(last);
                    }
                    return;
                }
                // last_free_sprite = (*first_free_sprite).prev
                // But not (*(*first_free_sprite).next).prev = (*first_free_sprite).prev
                if let Some(inner) = value.if_mem32().and_then(|x| x.if_mem32()) {
                    if dest_addr.iter().all(|x| *x != **inner) {
                        if self.is_unpaired_first_ptr(&inner) {
                            self.set_last_ptr(dest_addr.clone());
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner.clone(), dest_addr.clone()));
                        }
                    }
                }
                if let Some(ref head_candidate) = self.is_checking_active_list_candidate {
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
                    if let Some(first_free) = free_list.and_then(|x| x.head.as_ref()) {
                        if let Some(_) = value.if_mem32().filter(|x| *x == first_free) {
                            if dest_addr == *head_candidate {
                                self.active_list_candidate_head = Some(dest_addr.clone());
                            } else {
                                self.active_list_candidate_tail = Some(dest_addr.clone());
                            }
                        }
                    }
                }
            }
            Operation::Jump { ref condition, ref to } => {
                match self.state {
                    FindSpritesState::CreateLone_Post | FindSpritesState::CreateSprite => (),
                    FindSpritesState::CreateLone | FindSpritesState::NukeTrack => return,
                }
                let condition = ctrl.resolve(&condition);
                let dest_addr = match ctrl.resolve(&to).if_constant() {
                    Some(s) => VirtualAddress::from_u64(s),
                    None => return,
                };
                fn if_arithmetic_eq_zero(op: &Rc<Operand>) -> Option<&Rc<Operand>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                };
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(&condition) {
                    Some(other) => match if_arithmetic_eq_zero(&other) {
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
                        self.lone_free.head.as_ref().filter(|x| *x == val).is_some() ||
                        self.sprites_free.head.as_ref().filter(|x| *x == val).is_some();
                    if !is_free_list_head {
                        self.active_list_candidate_branches.insert(addr, val.clone());
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'a, '_, '_, Self>) {
        let head_candidate = self.active_list_candidate_branches.get(&ctrl.address());
        self.is_checking_active_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, ctrl: &mut Control<'a, '_, '_, Self>) {
        // Since hlines should be [hlines + 4 * x]
        // Prefer 4 * undefined as an 4 * (x - 1) offset will change base
        fn hlines_base(val: &Rc<Operand>) -> Option<&Rc<Operand>> {
            val.if_arithmetic_add()
                .and_either(|x| x.if_arithmetic_mul())
                .filter(|((l, r), _)| {
                    Operand::either(l, r, |x| x.if_constant().filter(|&x| x == 4))
                        .filter(|(_, other)| match other.ty {
                            OperandType::Undefined(_) => true,
                            _ => false,
                        })
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
                        let head = hlines_base(&head);
                        let tail = hlines_base(&tail);
                        if let (Some(head), Some(tail)) = (head, tail) {
                            self.hlines.head = Some(head.clone());
                            self.hlines.tail = Some(tail.clone());
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

impl<'a> SpriteAnalyzer<'a> {
    fn is_list_call(&self, arg1: &Rc<Operand>, ecx: &Rc<Operand>) -> bool {
        if let Some(addr) = ecx.if_mem32() {
            // It's remove call if ecx == [arg1], (item == [head])
            if addr == arg1 {
                return true;
            }
            // Add call if ecx == [free_head]
            // Check to not go into AddOverlay, as ecx == sprite == [free_head]
            // AddOverlay's first argument is Mem16, and a pointer can obviously never be Mem16
            if arg1.if_memory().filter(|x| x.size != MemAccessSize::Mem32).is_none() {
                if let Some(ref head) = self.lone_free.head {
                    if addr == head {
                        return true;
                    }
                }
                if let Some(ref head) = self.sprites_free.head {
                    if addr == head {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn last_ptr_first_known(&self, first: &Rc<Operand>) -> Option<Rc<Operand>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == *first).map(|x| x.1.clone())
    }

    fn is_unpaired_first_ptr(&self, first: &Rc<Operand>) -> bool {
        match self.state {
            FindSpritesState::CreateLone => {
                if let Some(_) = self.lone_free.head.as_ref().filter(|x| *x == first) {
                    return self.lone_free.tail.is_none();
                }
            }
            FindSpritesState::CreateSprite => {
                if let Some(_) = self.sprites_free.head.as_ref().filter(|x| *x == first) {
                    return self.sprites_free.tail.is_none();
                }
            }
            _ => (),
        }
        false
    }

    fn set_first_ptr(&mut self, value: Rc<Operand>) {
        if self.lone_free.head.is_none() {
            self.state = FindSpritesState::CreateLone;
            self.lone_free.head = Some(value);
        } else if self.sprites_free.head.is_none() {
            // Check for duplicate lone set
            if self.lone_free.head.as_ref().filter(|x| **x == value).is_none() {
                self.state = FindSpritesState::CreateSprite;
                self.sprites_free.head = Some(value);
            }
        }
    }

    fn set_last_ptr(&mut self, value: Rc<Operand>) {
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

pub fn fow_sprites<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
) -> FowSprites {
    // step_orders calls a function that loops through
    // lone sprites, followed by a loop through fow sprites.
    // That fow stepping code can also move from active -> free list,
    // so can get all 4 pointers from that.
    let ctx = &OperandContext::new();
    let binary = analysis.binary;
    let mut result = FowSprites::default();
    let step_objects = match analysis.step_objects() {
        Some(s) => s,
        None => return result,
    };
    let first_lone = match analysis.sprites().first_lone {
        Some(ref s) => s.clone(),
        None => return result,
    };

    let mut analyzer = FowSpriteAnalyzer {
        ctx,
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

struct FowSpriteAnalyzer<'a> {
    ctx: &'a OperandContext,
    state: FowSpritesState,
    inline_depth: u8,
    free: IncompleteList,
    active: IncompleteList,
    // Explanation for these is at SpriteAnalyzer
    last_ptr_candidates: Vec<(Rc<Operand>, Rc<Operand>)>,
    free_list_candidate_branches: FxHashMap<VirtualAddress, Rc<Operand>>,
    is_checking_free_list_candidate: Option<Rc<Operand>>,
    free_list_candidate_head: Option<Rc<Operand>>,
    free_list_candidate_tail: Option<Rc<Operand>>,
    ecx: Rc<Operand>,
    first_lone: Rc<Operand>,
}

impl<'a> scarf::Analyzer<'a> for FowSpriteAnalyzer<'a> {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        use scarf::operand_helpers::*;

        if self.state == FowSpritesState::InStepOrders {
            // Check for x <= [first_lone_sprite],
            // if found write 0 to [first_lone_sprite]
            // (Skipping lone sprite loop) and switch to StepLoneSpritesFound
            // Ideally the next thing being handled should be fow sprites.
            if let Operation::Move(_, ref value, None) = op {
                let value = ctrl.resolve(value);
                let is_first_lone = value.if_mem32()
                    .filter(|x| **x == self.first_lone)
                    .is_some();
                if is_first_lone {
                    self.state = FowSpritesState::StepLoneSpritesFound;
                    self.inline_depth = 0;
                    let (state, i) = ctrl.exec_state();
                    state.move_to(&DestOperand::from_oper(&value), self.ctx.const_0(), i);
                }
                return;
            }
        }
        match *op {
            Operation::Call(ref to) => {
                if self.inline_depth >= 2 {
                    return;
                }
                if let Some(dest) = ctrl.resolve(&to).if_constant() {
                    match self.state {
                        FowSpritesState::InStepOrders => {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
                            if self.state != FowSpritesState::InStepOrders {
                                ctrl.end_analysis();
                            } else {
                                self.inline_depth -= 1;
                            }
                        }
                        FowSpritesState::StepLoneSpritesFound => {
                            let ecx = ctrl.resolve(&self.ecx);
                            if ecx.if_mem32().is_none() {
                                return;
                            }
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
                            self.inline_depth -= 1;
                            if self.active.head.is_some() && self.free.head.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), ref value, _) => {
                if mem.size != MemAccessSize::Mem32 {
                    return;
                }
                if self.state != FowSpritesState::StepLoneSpritesFound {
                    return;
                }
                // The free/active logic is opposite from SpriteAnalyzer, as this function
                // frees fow sprites while the function SpriteAnalyzer checks allocates sprites
                let dest_addr = ctrl.resolve(&mem.address);
                let value = ctrl.resolve(&value);
                // first_active_sprite = (*first_active_sprite).next, e.g.
                // mov [first_active_sprite], [[first_active_sprite] + 4]
                let first_sprite_next = Operand::simplified(
                    mem32(operand_add(mem32(dest_addr.clone()), self.ctx.const_4()))
                );
                if value == first_sprite_next {
                    self.active.head = Some(dest_addr.clone());
                    if let Some(last) = self.last_ptr_first_known(&dest_addr) {
                        self.active.tail = Some(last);
                    }
                    return;
                }
                // last_active_sprite = (*first_active_sprite).prev
                // But not (*(*first_active_sprite).next).prev = (*first_active_sprite).prev
                if let Some(inner) = value.if_mem32().and_then(|x| x.if_mem32()) {
                    if dest_addr.iter().all(|x| *x != **inner) {
                        if self.is_unpaired_first_ptr(&inner) {
                            self.active.tail = Some(dest_addr.clone());
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner.clone(), dest_addr.clone()));
                        }
                    }
                }
                if let Some(ref head_candidate) = self.is_checking_free_list_candidate {
                    // Adding to free sprites is detected as
                    // if (*first_free == null) {
                    //     *first_free = *first_active;
                    //     *last_free = *first_active;
                    // }
                    let active_list = &self.active;
                    if let Some(first_active) = active_list.head.as_ref() {
                        if let Some(_) = value.if_mem32().filter(|x| *x == first_active) {
                            if dest_addr == *head_candidate {
                                self.free_list_candidate_head = Some(dest_addr.clone());
                            } else {
                                self.free_list_candidate_tail = Some(dest_addr.clone());
                            }
                        }
                    }
                }
            }
            Operation::Jump { ref condition, ref to } => {
                if self.state != FowSpritesState::StepLoneSpritesFound {
                    return;
                }
                let condition = ctrl.resolve(&condition);
                let dest_addr = match ctrl.resolve(&to).if_constant() {
                    Some(s) => VirtualAddress::from_u64(s),
                    None => return,
                };
                fn if_arithmetic_eq_zero(op: &Rc<Operand>) -> Option<&Rc<Operand>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                };
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(&condition) {
                    Some(other) => match if_arithmetic_eq_zero(&other) {
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

    fn branch_start(&mut self, ctrl: &mut Control<'a, '_, '_, Self>) {
        let head_candidate = self.free_list_candidate_branches.get(&ctrl.address());
        self.is_checking_free_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, ctrl: &mut Control<'a, '_, '_, Self>) {
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

impl<'a> FowSpriteAnalyzer<'a> {
    fn last_ptr_first_known(&self, first: &Rc<Operand>) -> Option<Rc<Operand>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == *first).map(|x| x.1.clone())
    }

    fn is_unpaired_first_ptr(&self, first: &Rc<Operand>) -> bool {
        if let Some(_) = self.active.head.as_ref().filter(|x| *x == first) {
            return self.active.tail.is_none();
        }
        false
    }
}
