use std::rc::Rc;

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand};

use crate::{Analysis, single_result_assign, find_bytes};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SnpDefinitions {
    pub snp_definitions: Rc<Operand>,
    pub entry_size: u32,
}

pub fn snp_definitions<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<SnpDefinitions> {
    // Search for BNAU code.
    // The data is expected to be
    // SnpDefinition { u32 code, char *string_key, char *string_key, Caps *caps, Functions funcs }
    // Functions { u32 size_bytes, func *funcs[..] } (Functions are global constructor inited
    // though, so they're not in static data)
    // BNAU should be followed by UDPA
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let data = binary.section(b".data\0\0\0").unwrap();
    let results = find_bytes(&data.data, &[0x55, 0x41, 0x4e, 0x42]);
    let mut result = None;
    for rva in results {
        let address = data.virtual_address + rva.0;
        let entry_size = (0x10..0x100).find(|i| {
            match binary.read_u32(address + i * 4) {
                Ok(o) => o == 0x55445041,
                Err(_) => false,
            }
        }).map(|x| x * 4);
        if let Some(entry_size) = entry_size {
            let new = SnpDefinitions {
                snp_definitions: ctx.constant(address.as_u64()),
                entry_size,
            };
            if single_result_assign(Some(new), &mut result) {
                break;
            }
        }
    }
    result
}
