use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use scarf::{MemAccess, Operand, Operation, DestOperand};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{AnalysisCtx, ArgCache, ControlExt, OptionExt, bumpvec_with_capacity};
use crate::analysis_state::{AnalysisState, StateEnum, FindCreateBulletState};
use crate::switch;
use crate::struct_layouts;

pub struct BulletCreation<'e, Va: VirtualAddress> {
    pub first_active_bullet: Option<Operand<'e>>,
    pub last_active_bullet: Option<Operand<'e>>,
    pub first_free_bullet: Option<Operand<'e>>,
    pub last_free_bullet: Option<Operand<'e>>,
    pub create_bullet: Option<Va>,
    pub active_iscript_unit: Option<Operand<'e>>,
}

struct FindCreateBullet<'a, 'acx, 'e, E: ExecutionState<'e>> {
    is_inlining: bool,
    result: Option<E::VirtualAddress>,
    active_iscript_unit: Option<Operand<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    calls_seen: u32,
    phantom: std::marker::PhantomData<&'acx ()>,
}

impl<'a, 'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    FindCreateBullet<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve_va(to) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        if arg1.if_mem8().is_some() {
                            self.is_inlining = true;
                            let ecx = ctrl.resolve(ctx.register(1));
                            self.active_iscript_unit = Some(ecx);
                            ctrl.user_state().get::<FindCreateBulletState>().calls_seen = 0;
                            self.calls_seen = 0;
                            ctrl.analyze_with_current_state(self, dest);
                            if self.result.is_some() && self.calls_seen == 2 {
                                ctrl.end_analysis();
                            } else {
                                self.calls_seen = 0;
                                self.is_inlining = false;
                                self.result = None;
                                self.active_iscript_unit = None;
                            }
                        }
                    }
                }

                let unit = ctrl.resolve(self.arg_cache.on_call(5));
                if let Some(active_unit) = self.active_iscript_unit {
                    if unit != active_unit {
                        return;
                    }
                }
                let arg4 = ctrl.resolve(self.arg_cache.on_call(3));
                let is_player = arg4
                    .if_mem8_offset(struct_layouts::unit_player::<E::VirtualAddress>())
                    .map(|x| x == unit)
                    .unwrap_or(false);
                if !is_player {
                    return;
                }
                if let Some(dest) = ctrl.resolve_va(to) {
                    if let Some(s) = self.result {
                        if s != dest {
                            return;
                        }
                    }
                    self.result = Some(dest);
                    self.active_iscript_unit = Some(unit);
                    let state = ctrl.user_state().get::<FindCreateBulletState>();
                    let new_calls_seen = state.calls_seen + 1;
                    if new_calls_seen > self.calls_seen {
                        self.calls_seen = new_calls_seen;
                    }
                    state.calls_seen = new_calls_seen;
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if condition == ctx.const_1() {
                    if to.if_constant().is_none() {
                        // Reached switch jump?
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

struct FindBulletLists<'acx, 'e, E: ExecutionState<'e>> {
    is_inlining: bool,
    // first active, first_free
    active_bullets: Option<(Operand<'e>, Operand<'e>)>,
    active_list_candidate_branches: FxHashMap<E::VirtualAddress, Operand<'e>>,
    is_checking_active_list_candidate: Option<Operand<'e>>,
    active_list_candidate_head: Option<Operand<'e>>,
    active_list_candidate_tail: Option<Operand<'e>>,
    first_free: Option<Operand<'e>>,
    last_free: Option<Operand<'e>>,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: BumpVec<'acx, (Operand<'e>, Operand<'e>)>,
}

impl<'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindBulletLists<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve(to).if_constant() {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, E::VirtualAddress::from_u64(dest));
                        self.is_inlining = false;
                        if self.active_bullets.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                if mem.size != E::WORD_SIZE {
                    return;
                }
                let ctx = ctrl.ctx();
                let dest = ctrl.resolve_mem(mem);
                let dest_value = ctx.memory(&dest);
                let value = ctrl.resolve(value);
                // first_free_bullet = (*first_free_bullet).next, e.g.
                // mov [first_free_bullet], [[first_free_bullet] + 4]
                let first_free_next = ctrl.mem_word(
                    dest_value,
                    E::VirtualAddress::SIZE as u64,
                );
                if value == first_free_next {
                    self.first_free = Some(dest_value);
                    if let Some(last) = self.last_ptr_first_known(dest_value) {
                        self.last_free = Some(last);
                    }
                    return;
                }
                // last_free_bullet = (*first_free_bullet).prev
                // But not (*(*first_free_bullet).next).prev = (*first_free_bullet).prev
                if let Some(inner) = ctrl.if_mem_word_offset(value, 0)
                    .and_then(|x| ctrl.if_mem_word(x))
                {
                    let inner_op = inner.address_op(ctx);
                    let (dest_base, dest_offset) = dest.address();
                    if inner.if_constant_address() != Some(dest_offset) &&
                        dest_base.iter().all(|x| x != inner_op)
                    {
                        if self.is_unpaired_first_ptr(inner) {
                            self.last_free = Some(dest_value);
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner_op, dest_value));
                        }
                    }
                }
                if let Some(head_candidate) = self.is_checking_active_list_candidate {
                    // Adding to active bullets is detected as
                    // if (*first_active == null) {
                    //     *first_active = *first_free;
                    //     *last_active = *first_free;
                    // }
                    if let Some(first_free) = self.first_free {
                        if value == first_free {
                            if dest_value == head_candidate {
                                self.active_list_candidate_head = Some(dest_value);
                            } else {
                                self.active_list_candidate_tail = Some(dest_value);
                            }
                        }
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                let dest_addr = match ctrl.resolve_va(to) {
                    Some(s) => s,
                    None => return,
                };
                fn if_arithmetic_eq_zero<'e>(op: Operand<'e>) -> Option<Operand<'e>> {
                    op.if_arithmetic_eq()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                }
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match if_arithmetic_eq_zero(condition) {
                    Some(other) => match if_arithmetic_eq_zero(other) {
                        Some(other) => (other, false),
                        None => (other, true),
                    }
                    None => return,
                };
                if ctrl.if_mem_word(val).is_some() {
                    let addr = match jump_if_null {
                        true => dest_addr,
                        false => ctrl.current_instruction_end(),
                    };
                    self.active_list_candidate_branches.insert(addr, val);
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let head_candidate = self.active_list_candidate_branches.get(&ctrl.address());
        self.is_checking_active_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        if let Some(_) = self.is_checking_active_list_candidate.take() {
            let head = self.active_list_candidate_head.take();
            let tail = self.active_list_candidate_tail.take();
            if let (Some(head), Some(tail)) = (head, tail) {
                self.active_bullets = Some((head, tail));
            }
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> FindBulletLists<'acx, 'e, E> {
    fn last_ptr_first_known(&self, first: Operand<'e>) -> Option<Operand<'e>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == first).map(|x| x.1)
    }

    fn is_unpaired_first_ptr(&self, first: &MemAccess<'e>) -> bool {
        if let Some(_) = self.first_free
            .and_then(|x| x.if_memory())
            .filter(|x| x.address() == first.address())
        {
            return self.last_free.is_none();
        }
        false
    }
}

pub(crate) fn bullet_creation<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    iscript_switch: E::VirtualAddress,
) -> BulletCreation<'e, E::VirtualAddress> {
    let mut result = BulletCreation {
        first_active_bullet: None,
        last_active_bullet: None,
        first_free_bullet: None,
        last_free_bullet: None,
        create_bullet: None,
        active_iscript_unit: None,
    };
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let useweapon = match switch::simple_switch_branch(binary, iscript_switch, 0x28) {
        Some(o) => o,
        None => return result,
    };
    let mut analyzer = FindCreateBullet {
        is_inlining: false,
        result: None,
        active_iscript_unit: None,
        calls_seen: 0,
        arg_cache: &analysis.arg_cache,
        phantom: Default::default(),
    };
    let exec_state = E::initial_state(ctx, binary);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        useweapon,
        exec_state,
        AnalysisState::new(
            bump,
            StateEnum::CreateBullet(FindCreateBulletState {
                calls_seen: 0,
            }),
        ),
    );
    analysis.analyze(&mut analyzer);
    result.create_bullet = analyzer.result;
    result.active_iscript_unit = analyzer.active_iscript_unit;
    if let Some(create_bullet) = analyzer.result {
        let mut analyzer = FindBulletLists::<E> {
            is_inlining: false,
            active_bullets: None,
            first_free: None,
            last_free: None,
            is_checking_active_list_candidate: None,
            active_list_candidate_head: None,
            active_list_candidate_tail: None,
            last_ptr_candidates: bumpvec_with_capacity(8, bump),
            active_list_candidate_branches: FxHashMap::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, create_bullet);
        analysis.analyze(&mut analyzer);
        if let Some((first, last)) = analyzer.active_bullets {
            result.first_active_bullet = Some(first);
            result.last_active_bullet = Some(last);
        }
        result.first_free_bullet = analyzer.first_free;
        result.last_free_bullet = analyzer.last_free;
    }
    result
}
