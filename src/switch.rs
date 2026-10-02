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

    /// Returns a branch when the switch index is already the case value.
    ///
    /// Unlike [`Self::branch`], this does not interpret a memory-backed index
    /// as a packed secondary switch table. This is needed for switches over
    /// mutable lookup-table values when the lookup table happens to be
    /// readable in the analyzed binary.
    pub fn branch_case_value<Va: VirtualAddress>(
        &self,
        binary: &'e BinaryFile<Va>,
        ctx: OperandCtx<'e>,
        branch: u32,
    ) -> Option<Va> {
        if branch < self.low || branch > self.high {
            return None;
        }
        let (table, _index) = extract_table_first_index(ctx, &self.table)?;
        let size = self.table.size;
        let bytes = size.bits() / 8;
        let value = self.base.wrapping_add(
            binary.read_u64(Va::from_u64(table) + branch.checked_mul(bytes)?).ok()? & size.mask()
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

#[test]
fn branch_case_value_does_not_read_memory_backed_index() {
    const SECTION: u32 = 0x1000;
    const LOOKUP: u32 = 0x1100;
    const TABLE: u32 = 0x1800;
    let mut data = vec![0u8; 0x1000];
    data[(TABLE - SECTION) as usize..][..4].copy_from_slice(&0x2000u32.to_le_bytes());
    data[(TABLE - SECTION + 4) as usize..][..4].copy_from_slice(&0x3000u32.to_le_bytes());
    data[(LOOKUP - SECTION + 1) as usize] = 0;
    let binary = scarf::raw_bin(
        scarf::VirtualAddress(SECTION),
        vec![scarf::BinarySection {
            name: *b".data\0\0\0",
            virtual_address: scarf::VirtualAddress(SECTION),
            virtual_size: data.len() as u32,
            data,
        }],
    );
    let ctx = &scarf::OperandContext::new();
    let lookup = ctx.mem8(ctx.register(0), LOOKUP as u64);
    let table = ctx.mem32(ctx.mul_const(lookup, 4), TABLE as u64);
    let switch = CompleteSwitch {
        base: 0,
        table: *table.if_memory().unwrap(),
        low: 0,
        high: 1,
    };

    assert_eq!(
        switch.branch(&binary, ctx, 1),
        Some(scarf::VirtualAddress(0x2000)),
    );
    assert_eq!(
        switch.branch_case_value(&binary, ctx, 1),
        Some(scarf::VirtualAddress(0x3000)),
    );
}
