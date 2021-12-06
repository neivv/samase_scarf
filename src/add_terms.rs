use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;
use scarf::operand::{OperandCtx, OperandType, Operand, ArithOpType};

use crate::bumpvec_with_capacity;

pub fn collect_arith_add_terms<'e, 'acx>(
    operand: Operand<'e>,
    bump: &'acx Bump,
) -> AddTerms<'acx, 'e> {
    let mut terms = AddTerms {
        terms: bumpvec_with_capacity(8, bump),
        constant: 0,
    };
    terms.collect(operand, false);
    terms
}

pub struct AddTerms<'acx, 'e> {
    pub terms: BumpVec<'acx, (Operand<'e>, bool)>,
    pub constant: u64,
}

impl<'acx, 'e> AddTerms<'acx, 'e> {
    fn collect(&mut self, operand: Operand<'e>, negate: bool) {
        match *operand.ty() {
            OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Add => {
                self.collect(arith.left, negate);
                self.collect(arith.right, negate);
            }
            OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Sub => {
                self.collect(arith.left, negate);
                self.collect(arith.right, !negate);
            }
            OperandType::Constant(c) => {
                if negate {
                    self.constant = self.constant.wrapping_sub(c);
                } else {
                    self.constant = self.constant.wrapping_add(c);
                }
            }
            _ => self.terms.push((operand, negate)),
        }
    }

    /// If exactly one term returns true from callback, remove it and return true.
    /// Otherwise do nothing and return false.
    pub fn remove_one<F>(&mut self, func: F) -> bool
    where F: FnMut(Operand<'e>, bool) -> bool
    {
        self.remove_get(func).is_some()
    }

    pub fn remove_get<F>(&mut self, mut func: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>, bool) -> bool
    {
        let remove_index = match self.terms.iter().position(|x| func(x.0, x.1)) {
            Some(s) => s,
            None => return None,
        };
        if self.terms.iter().skip(remove_index + 1).any(|x| func(x.0, x.1)) {
            return None;
        }
        Some(self.terms.remove(remove_index).0)
    }

    pub fn get_if_single(self) -> Option<Operand<'e>> {
        if self.terms.len() == 1 {
            Some(self.terms[0].0)
        } else {
            None
        }
    }

    pub fn join(&self, ctx: OperandCtx<'e>) -> Operand<'e> {
        let mut tree = match self.terms.get(0) {
            Some(&(op, negate)) => if negate {
                ctx.sub(ctx.constant(self.constant), op)
            } else {
                if self.constant == 0 {
                    op.clone()
                } else {
                    ctx.add(ctx.constant(self.constant), op)
                }
            },
            None => return ctx.constant(self.constant),
        };
        for &(op, neg) in self.terms.iter().skip(1) {
            tree = match neg {
                false => ctx.add(tree, op),
                true => ctx.sub(tree, op),
            };
        }
        tree
    }
}

