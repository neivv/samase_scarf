use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Operation};

use crate::{
    Analysis, OptionExt, read_u32_at, find_bytes, string_refs, find_functions_using_global,
    entry_of_until,
};

const BUTTONSET_BUTTON_COUNTS: [u8; 13] = [6, 9, 6, 5, 0, 7, 0, 9, 7, 8, 6, 7, 6];
/// Buttonsets are in format { button_count, pointer, linked (0xffff usually) },
/// scan for the first button count and then filter the result, allowing anything in the
/// pointer slot, unless the value is zero, in which case the pointer must be zero.
pub fn find_buttonsets<Va: VirtualAddress>(binary: &BinaryFile<Va>) -> Vec<Va> {
    let data = binary.section(b".data\0\0\0").unwrap();
    let first = [BUTTONSET_BUTTON_COUNTS[0], 0, 0, 0];
    let mut result = find_bytes(&data.data, &first[..]);
    result.retain(|&rva| {
        for (index, &expected) in BUTTONSET_BUTTON_COUNTS.iter().enumerate() {
            let index = index as u32;
            let button_count = read_u32_at(data, rva + index * 0xc);
            let linked = read_u32_at(data, rva + index * 0xc + 8);
            if button_count != Some(u32::from(expected)) || linked != Some(0xffff) {
                return false;
            }
        }
        true
    });
    result.into_iter().map(|x| data.virtual_address + x.0).collect()
}

pub fn find_unit_status_funcs<'exec, E: ExecutionState<'exec>>(
    binary: &BinaryFile<E::VirtualAddress>,
    cache: &mut Analysis<'exec, E>,
) -> Vec<E::VirtualAddress> {
    let mut str_refs = string_refs(binary, cache, b"rez\\statdata.bin\0");
    if str_refs.is_empty() {
        str_refs = string_refs(binary, cache, b"statdata.ui");
        // Currently rez and filename are separate but do this just in case.
        str_refs.extend(string_refs(binary, cache, b"rez\\statdata.ui"));
    }
    let funcs = cache.functions();
    let mut statdata_bin_globals = str_refs.iter().flat_map(|str_ref| {
        entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            crate::dialog::find_dialog_global(cache, entry, &str_ref)
        }).into_option()
    }).collect::<Vec<_>>();
    statdata_bin_globals.sort();
    statdata_bin_globals.dedup();

    let mut statdata_using_funcs = statdata_bin_globals.iter().flat_map(|&addr| {
        find_functions_using_global(cache, addr).into_iter().map(|x| x.func_entry)
    }).collect::<Vec<_>>();
    statdata_using_funcs.sort();
    statdata_using_funcs.dedup();
    let mut statdata = statdata_using_funcs.iter().flat_map(|&addr| {
        find_unit_status_func_uses(cache, addr)
    }).collect::<Vec<_>>();
    statdata.sort();
    statdata.dedup();
    statdata
}

/// If the function calls something from an 0xc-sized array, and then has another call
/// with offset 4, return the array (offset - 4, as the first u32 is unit id)
fn find_unit_status_func_uses<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    func: E::VirtualAddress,
) -> Vec<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let mut analyzer: UnitStatusFuncUses<'e, E> = UnitStatusFuncUses {
        result: Vec::new(),
        parts: Vec::new(),
    };
    let mut analysis = FuncAnalysis::new(binary, &ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result.sort();
    analyzer.result.dedup();
    analyzer.result
}

struct UnitStatusFuncUses<'e, E: ExecutionState<'e>> {
    result: Vec<E::VirtualAddress>,
    parts: Vec<u64>,
}

impl<'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitStatusFuncUses<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        match op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                let val = dest.if_memory()
                    .and_then(|mem| mem.address.if_arithmetic_add())
                    .and_either(|x| x.if_constant())
                    .filter(|(_address, other)| {
                        other.if_arithmetic_mul()
                            .and_either(|x| x.if_constant().filter(|&c| c == 0xc))
                            .is_some()
                    })
                    .map(|(address, _index_mul)| address);
                if let Some(address) = val {
                    // An valid address, check if there's another +/- 4 bytes
                    // from it, if yes, return result
                    let part_index = self.parts
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &part)| {
                            (address as i64).checked_sub(part as i64)
                                .map(|x| (i, x))
                        })
                        .find(|&(_, diff)| diff.abs() == 4);
                    if let Some((idx, diff)) = part_index {
                        self.parts.remove(idx);
                        if diff == 4 {
                            self.result.push(E::VirtualAddress::from_u64(address - 8));
                        } else {
                            self.result.push(E::VirtualAddress::from_u64(address - 4));
                        }
                    } else {
                        self.parts.push(address);
                    }
                }
            }
            _ => (),
        }
    }
}

const UNIT_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x6f, 0x00,
    0x08, 0xff, 0x05, 0xff, 0xff, 0xff, 0x01, 0x00,
    0x02, 0xff, 0x6f, 0x00, 0x08, 0xff, 0x05, 0xff,
    0x75, 0x00, 0x70, 0x00, 0xff, 0xff, 0x02, 0x00,
    0x02, 0xff, 0x71, 0x00, 0x05, 0xff, 0x08, 0xff,
    0xff, 0xff, 0x03, 0x00, 0x02, 0xff, 0x71, 0x00,
];
const UPGRADE_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xFF, 0x7A, 0x00,
    0x05, 0xFF, 0x07, 0xFF, 0x1F, 0xFF, 0xFF, 0xFF,
    0x20, 0xFF, 0x74, 0x00, 0xFF, 0xFF, 0x21, 0xFF,
    0x74, 0x00, 0xFF, 0xFF, 0x01, 0x00, 0x02, 0xFF,
    0x7B, 0x00, 0x05, 0xFF, 0x07, 0xFF, 0x1F, 0xFF,
    0xFF, 0xFF, 0x20, 0xFF, 0x74, 0x00, 0xFF, 0xFF,
];
const TECH_RESEARCH_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xFF, 0x70, 0x00,
    0x07, 0xFF, 0x05, 0xFF, 0xFF, 0xFF, 0x01, 0x00,
    0x02, 0xFF, 0x75, 0x00, 0x07, 0xFF, 0x05, 0xFF,
    0xFF, 0xFF, 0x03, 0x00, 0x02, 0xFF, 0x78, 0x00,
    0x07, 0xFF, 0x05, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x02, 0xFF, 0x78, 0x00, 0x07, 0xFF, 0x05, 0xFF,
];
const TECH_USE_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x1C, 0xFF, 0x01, 0xFF,
    0x0F, 0xFF, 0x02, 0xFF, 0x00, 0x00, 0x01, 0xFF,
    0x02, 0xFF, 0x20, 0x00, 0x01, 0xFF, 0x02, 0xFF,
    0x14, 0x00, 0x01, 0xFF, 0x02, 0xFF, 0x0A, 0x00,
    0xFF, 0xFF, 0x01, 0x00, 0x1C, 0xFF, 0x01, 0xFF,
    0x0F, 0xFF, 0x02, 0xFF, 0x01, 0x00, 0x01, 0xFF,
];
const ORDER_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x1E, 0xFF, 0xFF, 0xFF,
    0x01, 0x00, 0x1E, 0xFF, 0xFF, 0xFF, 0x02, 0x00,
    0x12, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x03, 0x00,
    0x12, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x04, 0x00,
    0x1A, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x02, 0xFF, 0x7D, 0x00, 0xFF, 0xFF, 0x06, 0x00,
];

pub fn find_requirement_table_refs<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    signature: &[u8],
) -> Vec<(E::VirtualAddress, u32)> {
    use std::cmp::Ordering;

    let data = analysis.binary.section(b".data\0\0\0").unwrap();
    let table_addresses = find_bytes(&data.data, signature);
    let relocs = analysis.relocs_with_values();
    let mut result = Vec::with_capacity(16);
    for &table_rva in &table_addresses {
        let table_va = data.virtual_address + table_rva.0;
        let mut index = relocs.binary_search_by(|x| match x.value >= table_va {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        while let Some(reloc) = relocs.get(index) {
            let offset = reloc.value.as_u64().wrapping_sub(table_va.as_u64());
            if offset >= 0x100 {
                break;
            }
            result.push((reloc.address, offset as u32));
            index += 1;
        }
    }
    result
}

pub fn find_requirement_tables<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> RequirementTables<E::VirtualAddress> {
    RequirementTables {
        units: find_requirement_table_refs(analysis, &UNIT_REQ_TABLE_BEGIN[..]),
        upgrades: find_requirement_table_refs(analysis, &UPGRADE_REQ_TABLE_BEGIN[..]),
        tech_use: find_requirement_table_refs(analysis, &TECH_USE_REQ_TABLE_BEGIN[..]),
        tech_research: find_requirement_table_refs(analysis, &TECH_RESEARCH_REQ_TABLE_BEGIN[..]),
        orders: find_requirement_table_refs(analysis, &ORDER_REQ_TABLE_BEGIN[..]),
    }
}

/// All of the addresses aren't refering to the first byte of table,
/// so there's a offset
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RequirementTables<Va: VirtualAddress> {
    pub units: Vec<(Va, u32)>,
    pub upgrades: Vec<(Va, u32)>,
    pub tech_research: Vec<(Va, u32)>,
    pub tech_use: Vec<(Va, u32)>,
    pub orders: Vec<(Va, u32)>,
}
