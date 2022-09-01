use scarf::{ArithOpType, Operand, OperandCtx, OperandType};

use crate::util::{OperandExt};

pub struct FloatEqTracker<'e> {
    state: FloatEqState<'e>,
}

#[derive(Copy, Clone)]
struct FloatEqState<'e> {
    a_nan: bool,
    b_nan: bool,
    eq: bool,
    a: Operand<'e>,
    b: Operand<'e>,
}

struct FloatEqUpdate<'e> {
    state: FloatEqState<'e>,
    follow_jump: bool,
}

#[derive(Debug)]
pub enum FloatCmpJump<'e> {
    Done(Operand<'e>, Operand<'e>, bool),
    ContinueAt(bool),
    Nothing,
}

impl<'e> FloatEqTracker<'e> {
    pub fn new(ctx: OperandCtx<'e>) -> Self {
        Self {
            state: FloatEqState {
                a_nan: false,
                b_nan: false,
                eq: false,
                a: ctx.const_0(),
                b: ctx.const_0(),
            }
        }
    }

    pub fn check_jump(&mut self, condition: Operand<'e>) -> FloatCmpJump<'e> {
        let update = self.get_update(condition, false);
        if let Some(ref update) = update {
            match self.state.merge(&update.state) {
                Some(new) => {
                    self.state = new;
                    if self.state.a_nan & self.state.b_nan & self.state.eq {
                        let a = self.state.a;
                        let b = self.state.b;
                        self.reset();
                        FloatCmpJump::Done(a, b, update.follow_jump)
                    } else {
                        FloatCmpJump::ContinueAt(update.follow_jump)
                    }
                }
                None => {
                    self.reset();
                    FloatCmpJump::Nothing
                }
            }
        } else {
            self.reset();
            FloatCmpJump::Nothing
        }
    }

    fn get_update(&self, op: Operand<'e>, negate: bool) -> Option<FloatEqUpdate<'e>> {
        match op.ty() {
            OperandType::ArithmeticFloat(arith, _size) => {
                if arith.ty == ArithOpType::Equal {
                    return Some(FloatEqUpdate {
                        state: FloatEqState {
                            // Constant nan check gets simplified out,
                            // so mark them here.
                            a_nan: arith.left.if_constant().is_some(),
                            b_nan: arith.right.if_constant().is_some(),
                            eq: true,
                            a: arith.left,
                            b: arith.right,
                        },
                        follow_jump: !negate,
                    });
                }
            }
            OperandType::Arithmetic(arith) => {
                match arith.ty {
                    ArithOpType::Equal => {
                        if arith.right.if_constant() == Some(0) {
                            return self.get_update(arith.left, !negate);
                        }
                    }
                    ArithOpType::Or => {
                        // (eq | nan) => follow, update only eq
                        // !(eq | nan) => !eq & !nan => don't follow, update only eq
                        // (!eq | !nan) => don't follow, merge
                        // !(!eq | !nan_a) => eq & nan_a => follow, merge
                        // In paths where the correct way is "one-of", assume that eq
                        // is preferred to nan checks due to how x86 instruction updates
                        // flags `Z = eq | nan`
                        let left = self.get_update(arith.left, false);
                        let right = self.get_update(arith.right, false);
                        match (left, right) {
                            (Some(ref l), Some(ref r)) => {
                                if !l.follow_jump && !r.follow_jump {
                                    return Some(FloatEqUpdate {
                                        state: l.state.merge(&r.state)?,
                                        follow_jump: negate,
                                    });
                                } else {
                                    let update = self.pick_update(l, r)?;
                                    return Some(FloatEqUpdate {
                                        state: update.state,
                                        follow_jump: update.follow_jump ^ negate,
                                    });
                                }
                            }
                            (Some(ref update), None) | (None, Some(ref update)) => {
                                return Some(FloatEqUpdate {
                                    state: update.state,
                                    follow_jump: update.follow_jump ^ negate,
                                });
                            }
                            _ => (),
                        }
                    }
                    ArithOpType::And => {
                        // (eq & nan) => follow, merge
                        // !(eq & nan) => !eq | !nan => don't follow, merge
                        // (!eq & !nan) => eq | nan
                        // !(!eq & !nan_a) => eq | nan_a
                        let left = self.get_update(arith.left, false);
                        let right = self.get_update(arith.right, false);
                        match (left, right) {
                            (Some(ref l), Some(ref r)) => {
                                if l.follow_jump && r.follow_jump {
                                    return Some(FloatEqUpdate {
                                        state: l.state.merge(&r.state)?,
                                        follow_jump: !negate,
                                    });
                                } else {
                                    let update = self.pick_update(l, r)?;
                                    return Some(FloatEqUpdate {
                                        state: update.state,
                                        follow_jump: update.follow_jump ^ !negate,
                                    });
                                }
                            }
                            (Some(ref update), None) | (None, Some(ref update)) => {
                                return Some(FloatEqUpdate {
                                    state: update.state,
                                    follow_jump: update.follow_jump ^ !negate,
                                });
                            }
                            _ => (),
                        }
                    }
                    ArithOpType::GreaterThan => {
                        if arith.right.if_constant() == Some(0x7f80_0000) {
                            if let Some(inner) = arith.left.if_arithmetic_and_const(0x7fff_ffff) {
                                return Some(FloatEqUpdate {
                                    state: FloatEqState {
                                        a_nan: true,
                                        b_nan: false,
                                        eq: false,
                                        a: inner,
                                        b: inner,
                                    },
                                    follow_jump: negate,
                                });
                            }
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }
        None
    }

    fn pick_update<'a>(
        &self,
        a: &'a FloatEqUpdate<'e>,
        b: &'a FloatEqUpdate<'e>,
    ) -> Option<&'a FloatEqUpdate<'e>> {
        if !self.state.eq {
            if a.state.eq {
                return Some(a);
            } else if b.state.eq {
                return Some(b);
            }
        }
        Some(a)
    }

    fn reset(&mut self) {
        self.state.a_nan = false;
        self.state.b_nan = false;
        self.state.eq = false;
    }
}

impl<'e> FloatEqState<'e> {
    fn merge(&self, other: &FloatEqState<'e>) -> Option<FloatEqState<'e>> {
        let mut eq = false;
        let mut nans = [false, false];
        let mut ops = [None, None];
        let in_nans = [self.a_nan, self.b_nan, other.a_nan, other.b_nan];
        let nan_ops = [Some(self.a), Some(self.b), Some(other.a), Some(other.b)];
        let self_ops = [Some(self.a), Some(self.b)];
        let other_ops = [Some(other.a), Some(other.b)];
        if self.eq {
            if other.eq {
                if self.a != other.a || self.b != other.b {
                    return None;
                }
            }
            ops = self_ops;
            eq = true;
        } else if other.eq {
            ops = other_ops;
            eq = true;
        }
        for i in 0..4 {
            if in_nans[i] {
                let nan_op = nan_ops[i];
                if ops[0] == nan_op {
                    nans[0] = true;
                } else if ops[1] == nan_op {
                    nans[1] = true;
                } else if ops[0].is_none() {
                    nans[0] = true;
                    ops[0] = nan_op;
                } else if ops[1].is_none() {
                    nans[1] = true;
                    ops[1] = nan_op;
                } else {
                    return None;
                }
            }
        }
        Some(FloatEqState {
            eq,
            a_nan: nans[0],
            b_nan: nans[1],
            a: ops[0].unwrap_or(self.a),
            b: ops[1].unwrap_or(self.b),
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn single_jump() {
        let ctx = &scarf::OperandContext::new();
        let op = ctx.and(
            ctx.float_arithmetic(
                ArithOpType::Equal,
                ctx.xmm(2, 3),
                ctx.mem32c(0x1234),
                scarf::MemAccessSize::Mem32,
            ),
            ctx.eq_const(
                ctx.or(
                    ctx.gt_const(
                        ctx.and_const(
                            ctx.mem32c(0x1234),
                            0x7fff_ffff,
                        ),
                        0x7f80_0000,
                    ),
                    ctx.gt_const(
                        ctx.and_const(
                            ctx.xmm(2, 3),
                            0x7fff_ffff,
                        ),
                        0x7f80_0000,
                    ),
                ),
                0,
            ),
        );
        let op_neg = ctx.eq_const(op, 0);
        let mut tracker = FloatEqTracker::new(ctx);
        match tracker.check_jump(op) {
            FloatCmpJump::Done(a, b, jump) => {
                if a == ctx.xmm(2, 3) {
                    assert_eq!(b, ctx.mem32c(0x1234));
                } else {
                    assert_eq!(a, ctx.mem32c(0x1234));
                    assert_eq!(b, ctx.xmm(2, 3));
                }
                assert!(jump);
            }
            ref x => panic!("Expected done, got {x:?}"),
        }

        let mut tracker = FloatEqTracker::new(ctx);
        match tracker.check_jump(op_neg) {
            FloatCmpJump::Done(a, b, jump) => {
                if a == ctx.xmm(2, 3) {
                    assert_eq!(b, ctx.mem32c(0x1234));
                } else {
                    assert_eq!(a, ctx.mem32c(0x1234));
                    assert_eq!(b, ctx.xmm(2, 3));
                }
                assert!(!jump);
            }
            ref x => panic!("Expected done, got {x:?}"),
        }
    }

    #[test]
    fn two_steps() {
        let ctx = &scarf::OperandContext::new();
        let a = ctx.xmm(3, 1);
        let b = ctx.xmm(2, 0);

        let parity = ctx.or(
            ctx.gt_const(
                ctx.and_const(
                    b,
                    0x7fff_ffff,
                ),
                0x7f80_0000,
            ),
            ctx.gt_const(
                ctx.and_const(
                    a,
                    0x7fff_ffff,
                ),
                0x7f80_0000,
            ),
        );
        let not_zero = ctx.eq_const(
            ctx.or(
                parity,
                ctx.float_arithmetic(
                    ArithOpType::Equal,
                    a,
                    b,
                    scarf::MemAccessSize::Mem32,
                ),
            ),
            0,
        );
        let mut tracker = FloatEqTracker::new(ctx);
        match tracker.check_jump(parity) {
            FloatCmpJump::ContinueAt(jump) => {
                assert!(!jump);
            }
            ref x => panic!("Expected continue, got {x:?}"),
        }

        match tracker.check_jump(not_zero) {
            FloatCmpJump::Done(a, b, jump) => {
                if a == a {
                    assert_eq!(b, b);
                } else {
                    assert_eq!(a, a);
                    assert_eq!(b, b);
                }
                assert!(!jump);
            }
            ref x => panic!("Expected done, got {x:?}"),
        }
    }

    #[test]
    fn two_steps_with_const() {
        let ctx = &scarf::OperandContext::new();
        let a = ctx.xmm(3, 1);
        let b = ctx.constant(0);

        let parity = ctx.or(
            ctx.gt_const(
                ctx.and_const(
                    b,
                    0x7fff_ffff,
                ),
                0x7f80_0000,
            ),
            ctx.gt_const(
                ctx.and_const(
                    a,
                    0x7fff_ffff,
                ),
                0x7f80_0000,
            ),
        );
        let not_zero = ctx.eq_const(
            ctx.or(
                parity,
                ctx.float_arithmetic(
                    ArithOpType::Equal,
                    a,
                    b,
                    scarf::MemAccessSize::Mem32,
                ),
            ),
            0,
        );
        let mut tracker = FloatEqTracker::new(ctx);
        match tracker.check_jump(parity) {
            FloatCmpJump::ContinueAt(jump) => {
                assert!(!jump);
            }
            ref x => panic!("Expected continue, got {x:?}"),
        }

        match tracker.check_jump(not_zero) {
            FloatCmpJump::Done(a, b, jump) => {
                if a == a {
                    assert_eq!(b, b);
                } else {
                    assert_eq!(a, a);
                    assert_eq!(b, b);
                }
                assert!(!jump);
            }
            ref x => panic!("Expected done, got {x:?}"),
        }
    }
}
