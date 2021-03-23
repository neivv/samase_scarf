use byteorder::{ByteOrder, LittleEndian};
use scarf::exec_state::{ExecutionState};

use crate::{AnalysisCtx, find_bytes};

pub(crate) fn fastfail<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
) -> Vec<E::VirtualAddress> {
    let bump = &analysis.bump;

    // Find fastfail functions by looking for
    // IsProcessorFeaturePresent(0x17)
    // which is compiled as
    //   push 0x17 (0x6a, 0x17)
    //   call jmp_import (0xe8, xx, xx, xx, xx)
    // and jmp_import is
    //   jmp dword [xx] (0xff, 0x25, ..)
    // and that the jmp_import call is quickly (less than ~16 bytes) followed by
    //   int 29 (0xcd, 0x29)
    //
    // Returned addresses are at the push 0x17
    // Also some variants just do call dword [xx] instead of jump_import

    fn has_int29(data: &[u8], offset: usize) -> bool {
        Some(()).and_then(|()| {
            let following_bytes = data.get(offset..)?.get(..16)?;
            following_bytes.windows(2).find(|x| x == &[0xcd, 0x29])
        }).is_some()
    }

    let text = analysis.binary_sections.text;
    let matches = find_bytes(bump, &text.data, &[0x6a, 0x17, 0xe8]);
    let mut result = Vec::with_capacity(8);
    for pos in matches {
        let int29 = has_int29(&text.data, (pos.0 as usize).wrapping_add(7));
        if int29 {
            let call_is_to_memjmp = Some(()).and_then(|()| {
                let offset = text.data.get((pos.0 as usize).wrapping_add(3)..)?.get(..4)?;
                let offset = LittleEndian::read_u32(&offset);
                let dest = pos.0.wrapping_add(offset).wrapping_add(7);
                let callee_bytes = text.data.get(dest as usize..)?.get(..2)?;
                (callee_bytes == &[0xff, 0x25]).then(|| ())
            }).is_some();
            if call_is_to_memjmp {
                let address = text.virtual_address + pos.0;
                result.push(address);
            }
        }
    }
    let matches = find_bytes(bump, &text.data, &[0x6a, 0x17, 0xff, 0x15]);
    for pos in matches {
        let int29 = has_int29(&text.data, (pos.0 as usize).wrapping_add(8));
        if int29 {
            let address = text.virtual_address + pos.0;
            result.push(address);
        }
    }
    result
}
