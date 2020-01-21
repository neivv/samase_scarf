use std::rc::Rc;

use fxhash::FxHashMap;

use scarf::{
    MemAccessSize, Operand, OperandContext, Operation, VirtualAddress, DestOperand,
    ExecutionStateX86,
};
use scarf::analysis::{self, AnalysisState, Control, FuncAnalysis};
use scarf::exec_state::{VirtualAddress as VirtualAddressTrait};

use crate::{Analysis, OptionExt};

#[derive(Default)]
pub struct BulletCreation {
    pub first_active_bullet: Option<Rc<Operand>>,
    pub last_active_bullet: Option<Rc<Operand>>,
    pub first_free_bullet: Option<Rc<Operand>>,
    pub last_free_bullet: Option<Rc<Operand>>,
    pub create_bullet: Option<VirtualAddress>,
    pub active_iscript_unit: Option<Rc<Operand>>,
}

struct FindCreateBullet<'a> {
    ctx: &'a OperandContext,
    is_inlining: bool,
    result: Option<VirtualAddress>,
    active_iscript_unit: Option<Rc<Operand>>,
    arg1: Rc<Operand>,
    arg4: Rc<Operand>,
    arg6: Rc<Operand>,
    calls_seen: u32,
}

#[derive(Copy, Clone)]
struct FindCreateBulletState {
    calls_seen: u32,
}
impl AnalysisState for FindCreateBulletState {
    fn merge(&mut self, newer: FindCreateBulletState) {
        self.calls_seen = self.calls_seen.max(newer.calls_seen);
    }
}

impl<'a> scarf::Analyzer<'a> for FindCreateBullet<'a> {
    type State = FindCreateBulletState;
    type Exec = scarf::ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        match *op {
            Operation::Call(ref to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve(&to).if_constant() {
                        let arg1 = ctrl.resolve(&self.arg1);
                        if arg1.if_mem8().is_some() {
                            self.is_inlining = true;
                            let ecx = ctrl.resolve(&self.ctx.register(1));
                            self.active_iscript_unit = Some(ecx);
                            ctrl.user_state().calls_seen = 0;
                            self.calls_seen = 0;
                            ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
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

                let unit = ctrl.resolve(&self.arg6);
                if let Some(ref active_unit) = self.active_iscript_unit {
                    if unit != *active_unit {
                        return;
                    }
                }
                let arg4 = ctrl.resolve(&self.arg4);
                let is_player = arg4.if_mem8()
                    .and_then(|x| x.if_arithmetic_add())
                    .and_either_other(|x| x.if_constant().filter(|&c| c == 0x4c))
                    .map(|x| *x == unit)
                    .unwrap_or(false);
                if !is_player {
                    return;
                }
                if let Some(dest) = ctrl.resolve(&to).if_constant() {
                    if let Some(s) = self.result {
                        if s.as_u64() != dest {
                            return;
                        }
                    }
                    self.result = Some(VirtualAddress::from_u64(dest));
                    self.active_iscript_unit = Some(unit);
                    let new_calls_seen = ctrl.user_state().calls_seen + 1;
                    if new_calls_seen > self.calls_seen {
                        self.calls_seen = new_calls_seen;
                    }
                    ctrl.user_state().calls_seen = new_calls_seen;
                }
            }
            Operation::Jump { ref condition, ref to } => {
                let condition = ctrl.resolve(condition);
                if condition.if_constant().unwrap_or(0) != 0 {
                    if to.if_memory().is_some() {
                        // Reached switch jump?
                        ctrl.end_branch();
                    }
                }
            }
            _ => (),
        }
    }
}

struct FindBulletLists<'a> {
    ctx: &'a OperandContext,
    is_inlining: bool,
    // first active, first_free
    active_bullets: Option<(Rc<Operand>, Rc<Operand>)>,
    active_list_candidate_branches: FxHashMap<VirtualAddress, Rc<Operand>>,
    is_checking_active_list_candidate: Option<Rc<Operand>>,
    active_list_candidate_head: Option<Rc<Operand>>,
    active_list_candidate_tail: Option<Rc<Operand>>,
    first_free: Option<Rc<Operand>>,
    last_free: Option<Rc<Operand>>,
    // Since last ptr for free lists (removing) is detected as
    // *last = (*first).prev
    // If this pattern is seen before first is confirmed, store (first, last) here.
    last_ptr_candidates: Vec<(Rc<Operand>, Rc<Operand>)>,
}

impl<'a> scarf::Analyzer<'a> for FindBulletLists<'a> {
    type State = analysis::DefaultState;
    type Exec = scarf::ExecutionStateX86<'a>;
    fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
        use scarf::operand_helpers::*;
        match op {
            Operation::Call(to) => {
                if !self.is_inlining {
                    if let Some(dest) = ctrl.resolve(&to).if_constant() {
                        self.is_inlining = true;
                        ctrl.analyze_with_current_state(self, VirtualAddress::from_u64(dest));
                        self.is_inlining = false;
                        if self.active_bullets.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), ref value, None) => {
                if mem.size != MemAccessSize::Mem32 {
                    return;
                }
                let dest_addr = ctrl.resolve(&mem.address);
                let value = ctrl.resolve(&value);
                // first_free_bullet = (*first_free_bullet).next, e.g.
                // mov [first_free_bullet], [[first_free_bullet] + 4]
                let first_free_next = Operand::simplified(
                    mem32(operand_add(mem32(dest_addr.clone()), self.ctx.const_4()))
                );
                if value == first_free_next {
                    self.first_free = Some(dest_addr.clone());
                    if let Some(last) = self.last_ptr_first_known(&dest_addr) {
                        self.last_free = Some(last);
                    }
                    return;
                }
                // last_free_bullet = (*first_free_bullet).prev
                // But not (*(*first_free_bullet).next).prev = (*first_free_bullet).prev
                if let Some(inner) = value.if_mem32().and_then(|x| x.if_mem32()) {
                    if dest_addr.iter().all(|x| *x != **inner) {
                        if self.is_unpaired_first_ptr(&inner) {
                            self.last_free = Some(dest_addr.clone());
                            return;
                        } else {
                            self.last_ptr_candidates.push((inner.clone(), dest_addr.clone()));
                        }
                    }
                }
                if let Some(ref head_candidate) = self.is_checking_active_list_candidate {
                    // Adding to active bullets is detected as
                    // if (*first_active == null) {
                    //     *first_active = *first_free;
                    //     *last_active = *first_free;
                    // }
                    if let Some(ref first_free) = self.first_free {
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
                    self.active_list_candidate_branches.insert(addr, val.clone());
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'a, '_, '_, Self>) {
        let head_candidate = self.active_list_candidate_branches.get(&ctrl.address());
        self.is_checking_active_list_candidate = head_candidate.cloned();
    }

    fn branch_end(&mut self, _ctrl: &mut Control<'a, '_, '_, Self>) {
        if let Some(_) = self.is_checking_active_list_candidate.take() {
            let head = self.active_list_candidate_head.take();
            let tail = self.active_list_candidate_tail.take();
            if let (Some(head), Some(tail)) = (head, tail) {
                self.active_bullets = Some((head, tail));
            }
        }
    }
}

impl<'a> FindBulletLists<'a> {
    fn last_ptr_first_known(&self, first: &Rc<Operand>) -> Option<Rc<Operand>> {
        self.last_ptr_candidates.iter().find(|x| x.0 == *first).map(|x| x.1.clone())
    }

    fn is_unpaired_first_ptr(&self, first: &Rc<Operand>) -> bool {
        if let Some(_) = self.first_free.as_ref().filter(|x| *x == first) {
            return self.last_free.is_none();
        }
        false
    }
}

pub fn bullet_creation<'a>(
    analysis: &mut Analysis<'a, ExecutionStateX86<'a>>,
    ctx: &OperandContext,
) -> BulletCreation {
    use scarf::operand_helpers::*;

    let mut result = BulletCreation::default();
    let iscript_switch = match analysis.step_iscript().switch_table {
        Some(s) => s,
        None => return result,
    };
    let binary = analysis.binary;
    let useweapon = match binary.read_u32(iscript_switch + 0x28 * 4) {
        Ok(o) => VirtualAddress(o),
        Err(_) => return result,
    };
    let mut analyzer = FindCreateBullet {
        ctx,
        is_inlining: false,
        result: None,
        active_iscript_unit: None,
        calls_seen: 0,
        arg1: Operand::simplified(mem32(ctx.register(4))),
        arg4: Operand::simplified(mem32(operand_add(ctx.register(4), ctx.constant(12)))),
        arg6: Operand::simplified(mem32(operand_add(ctx.register(4), ctx.constant(20)))),
    };
    let mut interner = scarf::exec_state::InternMap::new();
    let exec_state = scarf::ExecutionStateX86::new(ctx, &mut interner);
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        useweapon,
        exec_state,
        FindCreateBulletState {
            calls_seen: 0,
        },
        interner,
    );
    analysis.analyze(&mut analyzer);
    result.create_bullet = analyzer.result;
    result.active_iscript_unit = analyzer.active_iscript_unit;
    if let Some(create_bullet) = analyzer.result {
        let mut analyzer = FindBulletLists {
            ctx,
            is_inlining: false,
            active_bullets: None,
            first_free: None,
            last_free: None,
            is_checking_active_list_candidate: None,
            active_list_candidate_head: None,
            active_list_candidate_tail: None,
            last_ptr_candidates: Vec::new(),
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
