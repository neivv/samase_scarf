use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operation};

use crate::{
    AnalysisCtx, OperandExt, OptionExt, read_u32_at, find_bytes, FunctionFinder, entry_of_until,
    bumpvec_with_capacity,
};
use crate::struct_layouts;

const BUTTONSET_BUTTON_COUNTS: [u8; 13] = [6, 9, 6, 5, 0, 7, 0, 9, 7, 8, 6, 7, 6];
/// Buttonsets are in format { button_count, pointer, linked (0xffff usually) },
/// scan for the first button count and then filter the result, allowing anything in the
/// pointer slot, unless the value is zero, in which case the pointer must be zero.
pub(crate) fn find_buttonsets<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
) -> Vec<E::VirtualAddress> {
    let bump = &analysis.bump;
    let data = analysis.binary_sections.data;
    let first = [BUTTONSET_BUTTON_COUNTS[0], 0, 0, 0];
    let mut result = find_bytes(bump, &data.data, &first[..]);
    result.retain(|&rva| {
        let button_size = struct_layouts::button_size::<E::VirtualAddress>();
        let linked_offset = struct_layouts::button_linked::<E::VirtualAddress>();
        for (index, &expected) in BUTTONSET_BUTTON_COUNTS.iter().enumerate() {
            let index = index as u32;
            let button_count = read_u32_at(data, rva + index * button_size);
            let linked = read_u32_at(data, rva + index * button_size + linked_offset);
            if button_count != Some(u32::from(expected)) || linked != Some(0xffff) {
                return false;
            }
        }
        true
    });
    result.into_iter().map(|x| data.virtual_address + x.0).collect()
}

pub(crate) fn find_unit_status_funcs<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Vec<E::VirtualAddress> {
    let binary = analysis.binary;
    let bump = &analysis.bump;
    let mut str_refs = functions.string_refs(analysis, b"rez\\statdata.bin\0");
    if str_refs.is_empty() {
        str_refs = functions.string_refs(analysis, b"statdata.ui");
        // Currently rez and filename are separate but do this just in case.
        str_refs.extend(functions.string_refs(analysis, b"rez\\statdata.ui"));
    }
    let funcs = functions.functions();
    let statdata_bin_globals = str_refs.iter().flat_map(|str_ref| {
        entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            crate::dialog::find_dialog_global(analysis, entry, &str_ref)
        }).into_option()
    });
    let mut statdata_bin_globals = BumpVec::from_iter_in(statdata_bin_globals, bump);
    statdata_bin_globals.sort_unstable();
    statdata_bin_globals.dedup();

    let statdata_using_funcs = statdata_bin_globals.iter().flat_map(|&addr| {
        functions.find_functions_using_global(analysis, addr).into_iter().map(|x| x.func_entry)
    });
    let mut statdata_using_funcs = BumpVec::from_iter_in(statdata_using_funcs, bump);
    statdata_using_funcs.sort_unstable();
    statdata_using_funcs.dedup();
    let mut statdata = Vec::with_capacity(statdata_using_funcs.len() * 2);
    for &addr in &statdata_using_funcs {
        statdata.extend(find_unit_status_func_uses(analysis, addr));
    }
    statdata.sort_unstable();
    statdata.dedup();
    statdata
}

/// If the function calls something from an 0xc-sized array, and then has another call
/// with offset 4, return the array (offset - 4, as the first u32 is unit id)
fn find_unit_status_func_uses<'acx, 'e, E: ExecutionState<'e>>(
    analysis: &'acx AnalysisCtx<'e, E>,
    func: E::VirtualAddress,
) -> BumpVec<'acx, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;

    let mut analyzer: UnitStatusFuncUses<'acx, 'e, E> = UnitStatusFuncUses {
        result: bumpvec_with_capacity(4, bump),
        parts: bumpvec_with_capacity(4, bump),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result.sort_unstable();
    analyzer.result.dedup();
    analyzer.result
}

struct UnitStatusFuncUses<'acx, 'e, E: ExecutionState<'e>> {
    result: BumpVec<'acx, E::VirtualAddress>,
    parts: BumpVec<'acx, u64>,
}

impl<'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for UnitStatusFuncUses<'acx, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let word_size = E::VirtualAddress::SIZE as u64;
                let dest = ctrl.resolve(dest);
                let val = dest.if_memory()
                    .and_then(|mem| mem.address.if_arithmetic_add())
                    .and_either_other(|x| x.if_arithmetic_mul_const(word_size * 3))
                    .and_then(|x| x.if_constant());
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
                        .find(|&(_, diff)| diff.abs() == word_size as i64);
                    if let Some((idx, diff)) = part_index {
                        self.parts.remove(idx);
                        if diff == word_size as i64 {
                            self.result.push(E::VirtualAddress::from_u64(address - word_size * 2));
                        } else {
                            self.result.push(E::VirtualAddress::from_u64(address - word_size));
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

static UNIT_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x6f, 0x00,
    0x08, 0xff, 0x05, 0xff, 0xff, 0xff, 0x01, 0x00,
    0x02, 0xff, 0x6f, 0x00, 0x08, 0xff, 0x05, 0xff,
    0x75, 0x00, 0x70, 0x00, 0xff, 0xff, 0x02, 0x00,
    0x02, 0xff, 0x71, 0x00, 0x05, 0xff, 0x08, 0xff,
    0xff, 0xff, 0x03, 0x00, 0x02, 0xff, 0x71, 0x00,
];
static UPGRADE_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xFF, 0x7A, 0x00,
    0x05, 0xFF, 0x07, 0xFF, 0x1F, 0xFF, 0xFF, 0xFF,
    0x20, 0xFF, 0x74, 0x00, 0xFF, 0xFF, 0x21, 0xFF,
    0x74, 0x00, 0xFF, 0xFF, 0x01, 0x00, 0x02, 0xFF,
    0x7B, 0x00, 0x05, 0xFF, 0x07, 0xFF, 0x1F, 0xFF,
    0xFF, 0xFF, 0x20, 0xFF, 0x74, 0x00, 0xFF, 0xFF,
];
static TECH_RESEARCH_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x02, 0xFF, 0x70, 0x00,
    0x07, 0xFF, 0x05, 0xFF, 0xFF, 0xFF, 0x01, 0x00,
    0x02, 0xFF, 0x75, 0x00, 0x07, 0xFF, 0x05, 0xFF,
    0xFF, 0xFF, 0x03, 0x00, 0x02, 0xFF, 0x78, 0x00,
    0x07, 0xFF, 0x05, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x02, 0xFF, 0x78, 0x00, 0x07, 0xFF, 0x05, 0xFF,
];
static TECH_USE_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x1C, 0xFF, 0x01, 0xFF,
    0x0F, 0xFF, 0x02, 0xFF, 0x00, 0x00, 0x01, 0xFF,
    0x02, 0xFF, 0x20, 0x00, 0x01, 0xFF, 0x02, 0xFF,
    0x14, 0x00, 0x01, 0xFF, 0x02, 0xFF, 0x0A, 0x00,
    0xFF, 0xFF, 0x01, 0x00, 0x1C, 0xFF, 0x01, 0xFF,
    0x0F, 0xFF, 0x02, 0xFF, 0x01, 0x00, 0x01, 0xFF,
];
static ORDER_REQ_TABLE_BEGIN: [u8; 0x30] = [
    0x00, 0x00, 0x00, 0x00, 0x1E, 0xFF, 0xFF, 0xFF,
    0x01, 0x00, 0x1E, 0xFF, 0xFF, 0xFF, 0x02, 0x00,
    0x12, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x03, 0x00,
    0x12, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x04, 0x00,
    0x1A, 0xFF, 0x1E, 0xFF, 0xFF, 0xFF, 0x05, 0x00,
    0x02, 0xFF, 0x7D, 0x00, 0xFF, 0xFF, 0x06, 0x00,
];

fn find_requirement_table_refs<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    relocs: &[RelocValues<E::VirtualAddress>],
    signature: &[u8],
) -> Vec<(E::VirtualAddress, u32)> {
    use std::cmp::Ordering;

    let bump = &analysis.bump;
    let data = analysis.binary_sections.data;
    let table_addresses = find_bytes(bump, &data.data, signature);
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

pub(crate) fn find_requirement_tables<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    relocs: &[RelocValues<E::VirtualAddress>],
) -> RequirementTables<E::VirtualAddress> {
    RequirementTables {
        units: find_requirement_table_refs(analysis, relocs, &UNIT_REQ_TABLE_BEGIN[..]),
        upgrades: find_requirement_table_refs(analysis, relocs, &UPGRADE_REQ_TABLE_BEGIN[..]),
        tech_use: find_requirement_table_refs(analysis, relocs, &TECH_USE_REQ_TABLE_BEGIN[..]),
        tech_research:
            find_requirement_table_refs(analysis, relocs, &TECH_RESEARCH_REQ_TABLE_BEGIN[..]),
        orders: find_requirement_table_refs(analysis, relocs, &ORDER_REQ_TABLE_BEGIN[..]),
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
