use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{ArithOpType, BinaryFile, MemAccess, MemAccessSize, Operand, OperandCtx, OperandType};

use crate::util::{OperandExt};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CompleteSwitch<'e> {
    /// Base address added to values from table.
    base: u64,
    /// Address of the switch jump table.
    table: MemAccess<'e>,
    /// Minimum possible value for the switch jump
    low: u32,
    /// Maximum possible value (inclusive) for the switch jump
    high: u32,
}

fn extract_table_first_index<'e>(
    ctx: OperandCtx<'e>,
    table: &MemAccess<'e>,
) -> Option<(u64, Operand<'e>)> {
    // Offset should be the memory address for table base,
    // address "base" is the index in this case.
    let (index, table_addr) = table.address();
    if table_addr < 0x1000 {
        // Sanity check, could compare against binary limits too though
        return None;
    }
    let index = divide_by_const(ctx, index, table.size)?;
    Some((table_addr, index))
}

/// Like ctx.div_const(x, c) but only if remainder is 0
fn divide_by_const<'e>(
    ctx: OperandCtx<'e>,
    op: Operand<'e>,
    size: MemAccessSize,
) -> Option<Operand<'e>> {
    let bytes = size.bits() / 8;
    if let Some(inner) = op.if_arithmetic_mul_const(bytes as u64) {
        // Common path
        return Some(inner);
    }
    let shift = match size {
        MemAccessSize::Mem8 => 0u8,
        MemAccessSize::Mem16 => 1,
        MemAccessSize::Mem32 => 2,
        MemAccessSize::Mem64 => 3,
    };
    match *op.ty() {
        OperandType::Arithmetic(ref arith) => {
            if arith.ty == ArithOpType::And {
                if let Some(c) = arith.right.if_constant() {
                    if c & (bytes as u64 - 1) == 0 {
                        return Some(ctx.rsh_const(arith.left, shift as u64));
                    }
                }
            }
            match arith.ty {
                ArithOpType::Add | ArithOpType::Sub | ArithOpType::Or |
                    ArithOpType::Xor | ArithOpType::And =>
                {
                    let l = divide_by_const(ctx, arith.left, size)?;
                    let r = divide_by_const(ctx, arith.right, size)?;
                    Some(ctx.arithmetic(arith.ty, l, r))
                }
                ArithOpType::Mul => {
                    let r = divide_by_const(ctx, arith.right, size)?;
                    Some(ctx.arithmetic(arith.ty, arith.left, r))
                }
                ArithOpType::Lsh => {
                    let right = arith.right.if_constant()? as u8;
                    if right >= shift {
                        Some(ctx.lsh_const(arith.left, (right - shift) as u64))
                    } else {
                        None
                    }
                }
                ArithOpType::Rsh => {
                    let right = arith.right.if_constant()? as u8;
                    Some(ctx.rsh_const(arith.left, (right + shift) as u64))
                }
                _ => None,
            }
        }
        OperandType::Constant(c) => {
            if c & (bytes as u64 - 1) == 0 {
                Some(ctx.constant(c >> shift))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[test]
fn test_divide_by_const() {
    let ctx = &scarf::OperandContext::new();
    let op = ctx.lsh_const(
        ctx.register(0),
        0x14,
    );
    let div = divide_by_const(ctx, op, MemAccessSize::Mem32);
    let eq = ctx.lsh_const(
        ctx.register(0),
        0x12,
    );
    assert_eq!(div, Some(eq));

    let op = ctx.rsh_const(
        ctx.register(0),
        0x14,
    );
    let div = divide_by_const(ctx, op, MemAccessSize::Mem32);
    let eq = ctx.rsh_const(
        ctx.register(0),
        0x16,
    );
    assert_eq!(div, Some(eq));
}

impl<'e> CompleteSwitch<'e> {
    /// `dest` should be the operand jumped to.
    /// If it can be understood as a switch, Some(switch) is returned.
    pub fn new<E: ExecutionState<'e>>(
        dest: Operand<'e>,
        ctx: OperandCtx<'e>,
        exec_state: &mut E,
    ) -> Option<CompleteSwitch<'e>> {
        let (base, table) = match dest.if_memory() {
            Some(mem) if mem.size == E::WORD_SIZE => (0, mem),
            _ => {
                let (l, r) = dest.if_arithmetic_add()?;
                let base = r.if_constant()?;
                let mem = l.if_memory()?;
                (base, mem)
            }
        };
        // Recognize `table + index * SIZE`, and if
        // `index` is `Mem8/16[secondary_table + index * word_size]` unwrap that too.
        let (_table, index) = extract_table_first_index(ctx, table)?;
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (index2, table2) = mem.address();
                if table2 < 0x1000 {
                    return None;
                }
                if mem.size == MemAccessSize::Mem8 {
                    Some(index2)
                } else {
                    index2.if_arithmetic_mul_const(2)
                }
            })
            .unwrap_or(index);
        let limits = exec_state.value_limits(index);
        Some(CompleteSwitch {
            base,
            table: *table,
            low: limits.0.try_into().ok()?,
            high: limits.1.try_into().unwrap_or(u32::MAX),
        })
    }

    pub fn branch<Va: VirtualAddress>(
        &self,
        binary: &'e BinaryFile<Va>,
        ctx: OperandCtx<'e>,
        branch: u32,
    ) -> Option<Va> {
        if branch < self.low || branch > self.high {
            return None;
        }
        // Recognize `table + index * SIZE`, and if
        // `index` is `Mem8/16[secondary_table + index * word_size]` unwrap that too.
        let (table, index) = extract_table_first_index(ctx, &self.table)?;
        let size = self.table.size;
        let main_index_size = size.bits() / 8;
        let table = Va::from_u64(table);
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (_index2, table2) = mem.address();
                if table2 < 0x1000 {
                    // Wasn't indirection after all, just Mem index
                    return None;
                }
                let table2 = Va::from_u64(table2);
                if mem.size == MemAccessSize::Mem8 {
                    binary.read_u8(table2 + branch).ok().map(|x| x as u32)
                } else {
                    binary.read_u16(table2 + branch.checked_mul(2)?).ok().map(|x| x as u32)
                }
            })
            .unwrap_or(branch);
        let value = self.base.wrapping_add(
            binary.read_u64(table + index.checked_mul(main_index_size)?).ok()? & size.mask()
        );
        Some(Va::from_u64(value))
    }

    pub fn base(&self) -> u64 {
        self.base
    }

    pub fn switch_table(&self) -> u64 {
        self.table.address().1
    }

    pub fn as_operand(&self, ctx: OperandCtx<'e>) -> Operand<'e> {
        ctx.add_const(ctx.memory(&self.table), self.base)
    }

    pub fn index_operand(&self, ctx: OperandCtx<'e>) -> Option<Operand<'e>> {
        let (_, index) = extract_table_first_index(ctx, &self.table)?;
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (index2, table2) = mem.address();
                if table2 < 0x1000 {
                    // Wasn't indirection after all, just Mem index
                    return None;
                }
                if mem.size == MemAccessSize::Mem8 {
                    Some(index2)
                } else {
                    index2.if_arithmetic_mul_const(2)
                }
            })
            .unwrap_or(index);
        // Remove useless sign extend if high is below the extended value
        if let scarf::operand::OperandType::SignExtend(val, from, _to) = *index.ty() {
            if self.high as u64 <= (from.mask() / 2)  && self.high >= self.low {
                return Some(val);
            }
        }
        Some(index)
    }
}

pub fn simple_switch_branch<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    switch: Va,
    branch: u32,
) -> Option<Va> {
    if Va::SIZE == 4 {
        binary.read_address(switch + 4 * branch).ok()
    } else {
        Some(binary.base + binary.read_u32(switch + 4 * branch).ok()?)
    }
}
