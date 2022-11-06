use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{OperandCtx, Operand, OperandType};

use crate::util::is_global;

fn unresolve_add_chain_part<'e>(
    ctx: OperandCtx<'e>,
    op: Operand<'e>,
    resolved: Operand<'e>,
    unresolved: Operand<'e>,
) -> Option<(Operand<'e>, UnresolvedAddChainComplexity)> {
    let (l, r) = resolved.if_arithmetic_add()?;
    if l == op && is_global(r) {
        let complexity = if r.if_constant().is_some() {
            UnresolvedAddChainComplexity::Constant
        } else {
            UnresolvedAddChainComplexity::Complex
        };
        return Some((ctx.sub(unresolved, r), complexity));
    } else if r == op && is_global(l) {
        let complexity = UnresolvedAddChainComplexity::Complex;
        return Some((ctx.sub(unresolved, l), complexity));
    }
    let result = unresolve_add_chain_part(ctx, op, l, unresolved)?.0;
    if is_global(r) {
        Some((ctx.sub(result, r), UnresolvedAddChainComplexity::Complex))
    } else {
        None
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum UnresolvedAddChainComplexity {
    // Subtracts just a constant from a register to get the unresolved value.
    Constant,
    // Subtracts global memory/arith (e.g. game ptr) from register to get unresolved value
    Complex,
}

pub fn unresolve<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    exec_state: &mut E,
    op: Operand<'e>,
) -> Option<Operand<'e>> {
    if op.if_constant().is_some() {
        return Some(op);
    }
    let register_count = if E::VirtualAddress::SIZE == 4 { 8 } else { 16 };
    let mut sub_cand = None;
    let mut complex_sub_cand = false;
    for i in 0..register_count {
        let reg = ctx.register(i);
        let val = exec_state.resolve(reg);
        if val == op {
            return Some(reg);
        }
        if sub_cand.is_none() || complex_sub_cand {
            if let Some((cand, complexity)) = unresolve_add_chain_part(ctx, op, val, reg) {
                if sub_cand.is_none() || complexity == UnresolvedAddChainComplexity::Constant {
                    sub_cand = Some(cand);
                    complex_sub_cand = complexity == UnresolvedAddChainComplexity::Complex;
                }
            }
        }
        if let Some((l, r)) = op.if_arithmetic_mul() {
            if let Some(c) = r.if_constant() {
                if l == val {
                    return Some(ctx.mul_const(reg, c));
                }
                if let Some((l2, r2)) = val.if_arithmetic_mul() {
                    if l == l2 {
                        if let Some(c2) = r2.if_constant() {
                            let scale = c / c2;
                            let remainder = c % c2;
                            if remainder == 0 {
                                return Some(ctx.mul_const(reg, scale));
                            }
                        }
                    }
                }
            }
        }
    }
    if !complex_sub_cand {
        // If the add chain candidate is complex, try memory candidates first
        if let Some(sub_cand) = sub_cand {
            return Some(sub_cand);
        }
    }
    if let Some(mem) = op.if_memory() {
        // Unresolving Mem[x] as Mem[unres(x)] is only valid
        // if that address hasn't been written.
        // Which is common enough for stack args that it's worth doing.
        if exec_state.read_memory(mem)
            .if_memory()
            .filter(|&x| x == mem)
            .is_some()
        {
            let (base, offset) = mem.address();
            if let Some(base) = unresolve(ctx, exec_state, base) {
                return Some(ctx.mem_any(mem.size, base, offset));
            }
        }
        return None;
    }
    if op == ctx.register(4) {
        for i in 4..6 {
            let unres = ctx.register(i);
            let esp = exec_state.resolve(unres);
            if let Some((l, r)) = esp.if_arithmetic_sub() {
                if l == ctx.register(4) {
                    return Some(ctx.add(unres, r));
                }
            }
        }
    }
    if let OperandType::Arithmetic(ref arith) = *op.ty() {
        if let Some(left) = unresolve(ctx, exec_state, arith.left) {
            if let Some(right) = unresolve(ctx, exec_state, arith.right) {
                return Some(ctx.arithmetic(arith.ty, left, right));
            }
        }
    }
    // Now return any complex add chain result
    if let Some(sub_cand) = sub_cand {
        return Some(sub_cand);
    }
    None
}
