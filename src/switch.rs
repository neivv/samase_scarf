use std::convert::TryInto;

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, MemAccessSize, Operand};

use crate::{OperandExt};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CompleteSwitch<'e> {
    /// Base address added to values from table.
    base: u64,
    /// Address of the switch jump table.
    table: Operand<'e>,
    /// Size of the values in switch table.
    /// Should be word sized if base is zero. Otherwise can be u32 (Or technically even smaller)
    size: MemAccessSize,
    /// Minimum possible value for the switch jump
    low: u32,
    /// Maximum possible value (inclusive) for the switch jump
    high: u32,
}

impl<'e> CompleteSwitch<'e> {
    /// `dest` should be the operand jumped to.
    /// If it can be understood as a switch, Some(switch) is returned.
    pub fn new<E: ExecutionState<'e>>(
        dest: Operand<'e>,
        exec_state: &mut E,
    ) -> Option<CompleteSwitch<'e>> {
        let (base, table, size) = match dest.if_memory() {
            Some(mem) if mem.size == E::WORD_SIZE => (0, mem.address, mem.size),
            _ => {
                let (l, r) = dest.if_arithmetic_add()?;
                let base = r.if_constant()?;
                let mem = l.if_memory()?;
                (base, mem.address, mem.size)
            }
        };
        // Recognize `table + index * SIZE`, and if
        // `index` is `Mem8/16[secondary_table + index * word_size]` unwrap that too.
        let (l, r) = table.if_arithmetic_add()?;
        let _table = r.if_constant()?;
        let index = l.if_arithmetic_mul_const((size.bits() / 8) as u64)?;
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (l, r) = mem.address.if_arithmetic_add()?;
                let _table2 = r.if_constant()?;
                if mem.size == MemAccessSize::Mem8 {
                    Some(l)
                } else {
                    l.if_arithmetic_mul_const(2)
                }
            })
            .unwrap_or(index);
        let limits = exec_state.value_limits(index);
        Some(CompleteSwitch {
            base,
            table,
            size,
            low: limits.0.try_into().ok()?,
            high: limits.1.try_into().unwrap_or(u32::MAX),
        })
    }

    pub fn branch<Va: VirtualAddress>(
        &self,
        binary: &'e BinaryFile<Va>,
        branch: u32,
    ) -> Option<Va> {
        if branch < self.low || branch > self.high {
            return None;
        }
        // Recognize `table + index * SIZE`, and if
        // `index` is `Mem8/16[secondary_table + index * word_size]` unwrap that too.
        let (l, r) = self.table.if_arithmetic_add()?;
        let main_index_size = self.size.bits() / 8;
        let index = l.if_arithmetic_mul_const(main_index_size as u64)?;
        let table = Va::from_u64(r.if_constant()?);
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (l, r) = mem.address.if_arithmetic_add()?;
                let table2 = Va::from_u64(r.if_constant()?);
                if mem.size == MemAccessSize::Mem8 {
                    binary.read_u8(table2 + branch).ok().map(|x| x as u32)
                } else {
                    let _index2 = l.if_arithmetic_mul_const(2)?;
                    binary.read_u16(table2 + branch.checked_mul(2)?).ok().map(|x| x as u32)
                }
            })
            .unwrap_or(branch);
        let value = self.base.wrapping_add(
            binary.read_u64(table + index.checked_mul(main_index_size)?).ok()? & self.size.mask()
        );
        Some(Va::from_u64(value))
    }

    pub fn base(&self) -> u64 {
        self.base
    }

    pub fn switch_table(&self) -> Option<Operand<'e>> {
        Some(self.table.if_arithmetic_add()?.1)
    }

    pub fn index_operand(&self) -> Option<Operand<'e>> {
        let (l, _) = self.table.if_arithmetic_add()?;
        let index = l.if_arithmetic_mul_const((self.size.bits() / 8) as u64)?;
        let index = index.if_memory()
            .filter(|x| matches!(x.size, MemAccessSize::Mem8 | MemAccessSize::Mem16))
            .and_then(|mem| {
                let (l, r) = mem.address.if_arithmetic_add()?;
                r.if_constant()?;
                if mem.size == MemAccessSize::Mem8 {
                    Some(l)
                } else {
                    l.if_arithmetic_mul_const(2)
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
