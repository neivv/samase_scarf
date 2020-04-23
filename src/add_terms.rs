use scarf::operand::{OperandCtx, OperandType, Operand, ArithOpType};
use smallvec::SmallVec;

pub fn collect_arith_add_terms<'e>(operand: Operand<'e>) -> Option<AddTerms<'e>> {
    let mut terms = AddTerms {
        terms: Default::default(),
        constant: 0,
    };
    match *operand.ty() {
        OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Add => {
            terms.collect(arith.left, false);
            terms.collect(arith.right, false);
            Some(terms)
        }
        OperandType::Arithmetic(ref arith) if arith.ty == ArithOpType::Sub => {
            terms.collect(arith.left, false);
            terms.collect(arith.right, true);
            Some(terms)
        }
        _ => None,
    }
}

pub struct AddTerms<'e> {
    pub terms: SmallVec<[(Operand<'e>, bool); 8]>,
    pub constant: u64,
}

impl<'e> AddTerms<'e> {
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

    pub fn remove_one<F>(&mut self, mut func: F) -> bool
    where F: FnMut(Operand<'e>, bool) -> bool
    {
        let remove_index = match self.terms.iter().position(|x| func(x.0, x.1)) {
            Some(s) => s,
            None => return false,
        };
        if self.terms.iter().skip(remove_index + 1).any(|x| func(x.0, x.1)) {
            return false;
        }
        self.terms.remove(remove_index);
        true
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

