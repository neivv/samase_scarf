use std::convert::TryInto;

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, MemAccessSize, Operand};

use crate::{OperandExt};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CompleteSwitch<'e> {
    /// Address of the switch jump,
    /// e.g. expecting there to be `Operation::Jump` with `to == MemWord[dest]`
    dest: Operand<'e>,
    /// Minimum possible value for the switch jump
    low: u32,
    /// Maximum possible value (inclusive) for the switch jump
    high: u32,
}

impl<'e> CompleteSwitch<'e> {
    pub fn new<E: ExecutionState<'e>>(
        dest: Operand<'e>,
        exec_state: &mut E,
    ) -> Option<CompleteSwitch<'e>> {
        // Recognize `table + index * SIZE`, and if
        // `index` is `Mem8/16[secondary_table + index * word_size]` unwrap that too.
        let (l, r) = dest.if_arithmetic_add()?;
        let _table = r.if_constant()?;
        let index = l.if_arithmetic_mul_const(E::VirtualAddress::SIZE as u64)?;
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
            dest,
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
        let (l, r) = self.dest.if_arithmetic_add()?;
        let index = l.if_arithmetic_mul_const(Va::SIZE as u64)?;
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
        binary.read_address(table + index.checked_mul(Va::SIZE)?).ok()
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
