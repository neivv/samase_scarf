use bumpalo::collections::Vec as BumpVec;

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{Operand};

use crate::AnalysisCtx;

static ZERG_CAMPAIGN_SIGNATURE: &[u8] = &[
    0x20, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x21, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x22, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x2a, 0x00, 0x0f, 0x00, 0x0d, 0x00, 0x00, 0x00,
];

static TERRAN_CAMPAIGN_SIGNATURE: &[u8] = &[
    0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x02, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x03, 0x00, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x0c, 0x00, 0x04, 0x00, 0x06, 0x00, 0x01, 0x00,
];

pub(crate) fn campaigns<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<Operand<'e>> {
    // The campaign array is ordered by race, so zerg maps are in first pointer.
    // Check that second pointer is terran maps to avoid false positives.
    let rdata = analysis.binary.section(b".rdata\0\0").unwrap();
    let data = analysis.binary.section(b".data\0\0\0").unwrap();
    let bump = analysis.bump;
    let zerg_campaign_refs = crate::find_bytes(bump, &rdata.data, ZERG_CAMPAIGN_SIGNATURE);
    let va_size = <E::VirtualAddress as VirtualAddress>::SIZE;
    let candidates = zerg_campaign_refs.iter().flat_map(|&zref| {
        let address = rdata.virtual_address + zref.0;
        crate::find_address_refs(bump, &data.data, address)
    });
    let candidates = BumpVec::from_iter_in(candidates, bump);
    let result = candidates.iter()
        .map(|&rva| data.virtual_address + rva.0)
        .filter(|&address| {
            // Check that index 1 is terran campaign
            let index_1_ptr = match analysis.binary.read_address(address + va_size) {
                Ok(s) => s,
                Err(_) => return false,
            };
            let in_rdata = index_1_ptr >= rdata.virtual_address &&
                index_1_ptr < rdata.virtual_address + rdata.virtual_size;
            if !in_rdata {
                return false;
            }
            let offset = (index_1_ptr.as_u64() - rdata.virtual_address.as_u64()) as usize;
            (&rdata.data[offset..]).starts_with(TERRAN_CAMPAIGN_SIGNATURE)
        }).map(|campaigns| {
            analysis.ctx.constant(campaigns.as_u64())
        }).next();
    result
}
