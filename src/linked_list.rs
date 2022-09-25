
use scarf::analysis::{Analyzer, Control};
use scarf::exec_state::{ExecutionState};
use scarf::{DestOperand, Operand, OperandCtx, Operation, MemAccess};

use crate::hash_map::HashMap;
use crate::util::{ControlExt, OperandExt};

/// Finds linked list head and tail variables when given value to be added to list
/// Relies on the linked list add code doing
/// if (*head == 0) {
///     *head = value;
///     *tail = value;
/// }
pub(crate) struct DetectListAdd<'e, E: ExecutionState<'e>> {
    head: Option<MemAccess<'e>>,
    tail: Option<MemAccess<'e>>,
    value: Operand<'e>,
    head_candidate: Option<MemAccess<'e>>,
    head_candidate_branches: HashMap<E::VirtualAddress, MemAccess<'e>>,
}

pub(crate) struct ListHeadTail<'e> {
    pub head: Operand<'e>,
    pub tail: Operand<'e>,
}

impl<'e, E: ExecutionState<'e>> DetectListAdd<'e, E> {
    pub fn new(value: Operand<'e>) -> DetectListAdd<'e, E> {
        DetectListAdd {
            head: None,
            tail: None,
            value,
            head_candidate: None,
            head_candidate_branches: Default::default(),
        }
    }

    pub fn reset(&mut self, value: Operand<'e>) {
        self.head = None;
        self.tail = None;
        self.head_candidate = None;
        self.value = value;
        self.head_candidate_branches.clear();
    }

    pub fn operation<A>(&mut self, ctrl: &mut Control<'e, '_, '_, A>, op: &Operation<'e>)
    where A: Analyzer<'e, Exec = E>,
    {
        match *op {
            Operation::Jump { condition, to } => {
                let ctx = ctrl.ctx();
                let condition = ctrl.resolve(condition);
                // jump cond x == 0 jumps if x is 0, (x == 0) == 0 jumps if it is not
                let (val, jump_if_null) = match condition.if_arithmetic_eq_neq_zero(ctx) {
                    Some(x) => x,
                    None => return,
                };
                if let Some(inner) = ctrl.if_mem_word(val) {
                    let addr = match jump_if_null {
                        true => match ctrl.resolve_va(to) {
                            Some(s) => s,
                            None => return,
                        },
                        false => ctrl.current_instruction_end(),
                    };
                    self.head_candidate_branches.insert(addr, *inner);
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                if mem.size != E::WORD_SIZE {
                    return;
                }
                let dest = ctrl.resolve_mem(mem);
                if let Some(head_candidate) = self.head_candidate {
                    let value = ctrl.resolve(value);
                    if value == self.value {
                        if dest == head_candidate {
                            self.head = Some(dest);
                        } else {
                            self.tail = Some(dest);
                        }
                    }
                }
            }
            _ => (),
        }
    }

    pub fn branch_start<A>(&mut self, ctrl: &mut Control<'e, '_, '_, A>)
    where A: Analyzer<'e, Exec = E>,
    {
        self.head_candidate = self.head_candidate_branches.get(&ctrl.address()).copied();
        self.head = None;
        self.tail = None;
    }

    /// Expected to be called on branch_end
    pub fn result(&self, ctx: OperandCtx<'e>) -> Option<ListHeadTail<'e>> {
        self.head_candidate?;
        Some(ListHeadTail {
            head: ctx.memory(&self.head?),
            tail: ctx.memory(&self.tail?),
        })
    }
}
