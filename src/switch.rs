use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, BinarySection, Operation, Operand};

use crate::{
    Analysis, EntryOf, EntryOfResult, SwitchTable, OptionExt,
    entry_of_until, find_functions_using_global,
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CompleteSwitch<Va: VirtualAddress> {
    pub indirection: Option<Va>,
    pub address: Va,
    pub case_addresses: Vec<Va>,
    pub cases: Vec<Va>,
    pub offset: u32,
}

impl<Va: VirtualAddress> CompleteSwitch<Va> {
    pub fn branch(&self, branch: u32) -> Option<Va> {
        self.cases.get((branch.wrapping_sub(self.offset)) as usize).cloned()
    }
}

/// Also returns entry of the switch function
pub fn full_switch_info<'exec, E: ExecutionState<'exec>>(
    analysis: &mut Analysis<'exec, E>,
    switch: &SwitchTable<E::VirtualAddress>,
) -> Option<(CompleteSwitch<E::VirtualAddress>, E::VirtualAddress)> {
    let users = find_functions_using_global(analysis, switch.address);
    let funcs = analysis.functions();
    let entry = users.first().map(|x| x.func_entry)?;
    let binary = analysis.binary;
    let result = entry_of_until(binary, &funcs[..], entry, |entry| {
        match full_switch_info_in_function(analysis, switch, entry) {
            Some(s) => EntryOf::Ok(s),
            None => EntryOf::Retry,
        }
    });
    match result {
        EntryOfResult::Ok(entry, s) => Some((s, entry)),
        _ => None,
    }
}

fn full_switch_info_in_function<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    switch: &SwitchTable<E::VirtualAddress>,
    entry: E::VirtualAddress,
) -> Option<CompleteSwitch<E::VirtualAddress>> {

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analysis = FuncAnalysis::new(binary, ctx, entry);
    let mut analyzer: FullSwitchInfo<E> = FullSwitchInfo {
        result: None,
        text: binary.section(b".text\0\0\0").unwrap(),
        switch,
        binary,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FullSwitchInfo<'a, 'e, E: ExecutionState<'e>> {
    result: Option<CompleteSwitch<E::VirtualAddress>>,
    text: &'e BinarySection<E::VirtualAddress>,
    switch: &'a SwitchTable<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> FullSwitchInfo<'a, 'e, E> {
    fn cases(
        &self,
        case_addresses: &[E::VirtualAddress],
        indirection: &Option<E::VirtualAddress>,
    ) -> Vec<E::VirtualAddress> {
        match *indirection {
            Some(addr) => {
                let relative = (addr.as_u64() - self.binary.base.as_u64()) as u32;
                let bytes = match self.binary.slice_from(relative..relative + 0x100) {
                    Ok(o) => o,
                    Err(_) => return Vec::new(),
                };
                bytes.iter().cloned()
                    .take_while(|&x| (x as usize) < case_addresses.len())
                    .map(|x| case_addresses[x as usize])
                    .collect()
            }
            None => case_addresses.into(),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FullSwitchInfo<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                self.result = ctrl.if_mem_word(&to)
                    .and_then(|addr| addr.if_arithmetic_add())
                    .and_then(|(l, r)| {
                        let binary = self.binary;
                        let ((), other) = Operand::either(l, r, |x| match x.if_constant() {
                            Some(s) => match s == self.switch.address.as_u64() {
                                true => Some(()),
                                false => None,
                            },
                            None => None,
                        })?;
                        let index = other
                            .if_arithmetic_mul()
                            .and_either_other(|x| x.if_constant().filter(|&c| c == 4))?;
                        let indirection_base = index.if_mem8()
                            .and_then(|addr| addr.if_arithmetic_add())
                            .and_either(|x| x.if_constant())
                            .map(|x| E::VirtualAddress::from_u64(x.0))
                            .filter(|&indirection| {
                                let text = self.text;
                                indirection > text.virtual_address &&
                                    indirection < text.virtual_address + text.virtual_size
                            });
                        let offset = indirection_base.map(|x| {
                            switch_indirection_offset(binary, x, self.switch.cases.len() as u8)
                        }).unwrap_or(0);

                        let indirection = indirection_base.map(|x| x + offset);
                        let case_addresses = self.switch.cases.clone();
                        let cases = self.cases(&case_addresses, &indirection);
                        Some(CompleteSwitch {
                            indirection,
                            address: self.switch.address,
                            case_addresses,
                            cases,
                            offset,
                        })
                    });
                if self.result.is_some() {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

fn switch_indirection_offset<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    base: Va,
    case_limit: u8,
) -> u32 {
    let relative = (base.as_u64() - binary.base.as_u64()) as u32;
    let slice = match binary.slice_from(relative..relative + 0x100) {
        Ok(o) => o,
        // TODO: Shorter range than 0x100
        Err(_) => return 0,
    };
    let mut current_start = 0;
    let mut longest_pos = 0;
    let mut current_max = 0;
    let mut longest_size = 0;
    let mut longest_max = 0;
    for (i, val) in slice.iter().cloned().enumerate() {
        if val >= case_limit {
            if (current_max, i - current_start) > (longest_max, longest_size) {
                longest_pos = current_start;
                longest_size = i - current_start;
                longest_max = current_max;
            }
            current_start = i + 1;
            current_max = 0;
        } else {
            current_max = current_max.max(val);
        }
    }
    if (current_max, slice.len() - current_start) > (longest_max, longest_size) {
        longest_pos = current_start;
    }
    longest_pos as u32
}
