use std::fmt;

use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, MemAccess, Operation, Operand};

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until, find_bytes};
use crate::util::{ExecStateExt, OperandExt, read_u32_at, bumpvec_with_capacity};

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
        let button_size = E::struct_layouts().button_set_size();
        let linked_offset = E::struct_layouts().button_linked();
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
                    .and_then(|mem| {
                        let (base, offset) = mem.address();
                        base.if_arithmetic_mul_const(word_size * 3)?;
                        Some(offset)
                    });
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
    functions: &FunctionFinder<'_, 'e, E>,
    relocs: &[RelocValues<E::VirtualAddress>],
    signature: &[u8],
) -> RequirementTable<E::VirtualAddress> {
    use std::cmp::Ordering;

    let bump = &analysis.bump;
    let data = analysis.binary_sections.data;
    let table_addresses = find_bytes(bump, &data.data, signature);
    let mut result = Vec::with_capacity(16);
    let mut value_ranges = bumpvec_with_capacity(4, bump);
    let mut address = E::VirtualAddress::from_u64(u64::MAX);
    for &table_rva in &table_addresses {
        let table_va = data.virtual_address + table_rva.0;
        let mut index = relocs.binary_search_by(|x| match x.value >= table_va {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let mut last_value = table_va;
        let start_index = index;
        while let Some(reloc) = relocs.get(index) {
            let offset = reloc.value.as_u64().wrapping_sub(table_va.as_u64());
            if offset >= 0x100 {
                // If had at least one result added, add range.
                if index != start_index {
                    // Add 4 bytes of leeway as there are arr[i + 1] accesses that
                    // scarf folds to (arr + 1)[i]
                    value_ranges.push((table_va, last_value + 5));
                }
                break;
            }
            last_value = reloc.value;
            address = table_va;
            result.push((reloc.address, offset as u32));
            index += 1;
        }
    }
    filter_requirement_results(analysis, functions, &mut result, &value_ranges);
    RequirementTable {
        references: result,
        address,
    }
}

fn filter_requirement_results<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    result: &mut Vec<(E::VirtualAddress, u32)>,
    value_ranges: &[(E::VirtualAddress, E::VirtualAddress)]
) {
    // Verify that the result address is actually instruction accessing memory.
    // Could also have the table address be passed in here, but currently it is not
    // since it isn't included in the result
    result.sort_unstable_by_key(|x| x.0);

    let binary = actx.binary;
    let ctx = actx.ctx;
    let functions = functions.functions();
    let code_section = binary.code_section();
    let code_section_start = code_section.virtual_address;
    let code_section_end = code_section_start + code_section.virtual_size;

    let mut i = 0;
    while i < result.len() {
        if result[i].0 < code_section_start || result[i].0 > code_section_end {
            // This filtering works only for code, not rdata etc refs
            i += 1;
            continue;
        }
        let mut result_pos = i;
        entry_of_until(binary, functions, result[i].0, |entry| {
            let mut analyzer = RequirementResultFilter::<E> {
                entry_of: EntryOf::Retry,
                result,
                result_pos,
                other_ok: 0,
                false_result_seen: false,
                last_result_addr: E::VirtualAddress::from_u64(0),
                value_ranges,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            result_pos = analyzer.result_pos;
            analyzer.entry_of
        });
        if result_pos == i {
            // No results found, remove current
            result.remove(i);
        } else {
            i = result_pos;
        }
    }
}

struct RequirementResultFilter<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    result: &'a mut Vec<(E::VirtualAddress, u32)>,
    result_pos: usize,
    // Bitmask if other results after result_pos are found ok before result
    other_ok: u32,
    // These two are for handling multi-operation instructions (Such as push)
    // Any operation that is before "main" operation and doesn't pass sets false_result_seen,
    // main operation will clear it on success and set last_result_addr which makes all later
    // instructions be skipped.
    false_result_seen: bool,
    last_result_addr: E::VirtualAddress,
    // Valid ranges in which a valid memory address should be
    value_ranges: &'a [(E::VirtualAddress, E::VirtualAddress)],
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    RequirementResultFilter<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        let end = ctrl.current_instruction_end();
        let mut pos = self.result_pos;
        while pos < self.result.len() {
            let result_addr = self.result[pos].0;
            if result_addr >= end {
                if self.false_result_seen {
                    // False positive result, assume no point in analyzing rest of this funcion
                    ctrl.end_analysis();
                }
                break;
            }
            if result_addr >= address {
                if address == self.last_result_addr {
                    // Was already handled in previous operation
                    return;
                }
                self.entry_of = EntryOf::Ok(());
                let ok = match *op {
                    Operation::Move(ref dest, value, None) => {
                        if self.check(ctrl, value) {
                            true
                        } else if let DestOperand::Memory(ref dest) = *dest {
                            self.check_memory(ctrl, dest)
                        } else {
                            false
                        }
                    }
                    Operation::Jump { condition, .. } => {
                        self.check(ctrl, condition)
                    }
                    Operation::SetFlags(ref arith) => {
                        self.check(ctrl, arith.left) ||
                            self.check(ctrl, arith.right)
                    }
                    _ => false,
                };
                if ok {
                    if pos == self.result_pos {
                        self.result_pos += 1;
                        while self.other_ok & 1 != 0 {
                            self.result_pos += 1;
                            self.other_ok >>= 1;
                        }
                    } else {
                        if let Some(bit) = 1u32.checked_shl((pos - self.result_pos) as u32) {
                            self.other_ok |= bit;
                        }
                    }
                    self.false_result_seen = false;
                    self.last_result_addr = address;
                } else {
                    self.false_result_seen = true;
                }
                break;
            }
            pos += 1;
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> RequirementResultFilter<'a, 'e, E> {
    fn check(&self, ctrl: &mut Control<'e, '_, '_, Self>, unresolved: Operand<'e>) -> bool {
        let resolved = ctrl.resolve(unresolved);
        self.check_resolved(resolved)
    }

    fn check_memory(
        &self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        unresolved: &MemAccess<'e>,
    ) -> bool {
        let resolved = ctrl.resolve_mem(unresolved);
        let (_, offset) = resolved.address();
        let address = E::VirtualAddress::from_u64(offset);
        self.value_ranges.iter().any(|x| x.0 <= address && address < x.1)
    }

    fn check_resolved(&self, resolved: Operand<'e>) -> bool {
        let addr = if let Some(c) = resolved.if_constant() {
            Some(E::VirtualAddress::from_u64(c))
        } else if let Some(mem) = resolved.if_memory() {
            let (_, offset) = mem.address();
            Some(E::VirtualAddress::from_u64(offset))
        } else {
            None
        };
        if let Some(address) = addr {
            return self.value_ranges.iter().any(|x| x.0 <= address && address < x.1);
        }
        if let Some(a) = resolved.if_arithmetic_any() {
            return self.check_resolved(a.left) || self.check_resolved(a.right);
        }
        false
    }
}

pub(crate) fn find_requirement_tables<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    funcs: &FunctionFinder<'_, 'e, E>,
    relocs: &[RelocValues<E::VirtualAddress>],
) -> RequirementTables<E::VirtualAddress> {
    RequirementTables {
        units: find_requirement_table_refs(actx, funcs, relocs, &UNIT_REQ_TABLE_BEGIN[..]),
        upgrades: find_requirement_table_refs(actx, funcs, relocs, &UPGRADE_REQ_TABLE_BEGIN[..]),
        tech_use: find_requirement_table_refs(actx, funcs, relocs, &TECH_USE_REQ_TABLE_BEGIN[..]),
        tech_research:
            find_requirement_table_refs(actx, funcs, relocs, &TECH_RESEARCH_REQ_TABLE_BEGIN[..]),
        orders: find_requirement_table_refs(actx, funcs, relocs, &ORDER_REQ_TABLE_BEGIN[..]),
    }
}

/// All of the addresses aren't refering to the first byte of table,
/// so there's a offset
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RequirementTables<Va: VirtualAddress> {
    pub units: RequirementTable<Va>,
    pub upgrades: RequirementTable<Va>,
    pub tech_research: RequirementTable<Va>,
    pub tech_use: RequirementTable<Va>,
    pub orders: RequirementTable<Va>,
}

#[derive(Clone, Eq, PartialEq)]
pub struct RequirementTable<Va> {
    pub references: Vec<(Va, u32)>,
    pub address: Va,
}

impl<Va: VirtualAddress> fmt::Debug for RequirementTable<Va> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}, refs [", self.address.as_u64())?;
        for (i, &(addr, offset)) in self.references.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:x} + {:x}", addr.as_u64(), offset)?;
        }
        write!(f, "]")
    }
}
