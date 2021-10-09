use byteorder::{ByteOrder, LittleEndian};
use scarf::exec_state::{ExecutionState, VirtualAddress};

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
    // On 64-bit it is similar, but instead of push 17, it is mov ecx, 17
    // (0xb9, 0x17, 0x00, 0x00, 0x00)
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
    let call_bytes: &[u8] = if E::VirtualAddress::SIZE == 4 {
        &[0x6a, 0x17, 0xe8]
    } else {
        &[0xb9, 0x17, 0x00, 0x00, 0x00, 0xe8]
    };
    let matches = find_bytes(bump, &text.data, call_bytes);
    let mut result = Vec::with_capacity(8);
    for pos in matches {
        let call_end = call_bytes.len() + 4;
        let call_offset = call_bytes.len();
        let int29 = has_int29(&text.data, (pos.0 as usize).wrapping_add(call_end));
        if int29 {
            let call_is_to_memjmp = Some(()).and_then(|()| {
                let offset =
                    text.data.get((pos.0 as usize).wrapping_add(call_offset)..)?.get(..4)?;
                let offset = LittleEndian::read_u32(&offset);
                let dest = pos.0.wrapping_add(offset).wrapping_add(call_end as u32);
                let callee_bytes = text.data.get(dest as usize..)?.get(..2)?;
                (callee_bytes == &[0xff, 0x25]).then(|| ())
            }).is_some();
            if call_is_to_memjmp {
                let address = text.virtual_address + pos.0;
                result.push(address);
            }
        }
    }
    let call_bytes: &[u8] = if E::VirtualAddress::SIZE == 4 {
        &[0x6a, 0x17, 0xff, 0x15]
    } else {
        &[0xb9, 0x17, 0x00, 0x00, 0x00, 0xff, 0x15]
    };
    let matches = find_bytes(bump, &text.data, call_bytes);
    for pos in matches {
        let call_end = call_bytes.len() + 4;
        let int29 = has_int29(&text.data, (pos.0 as usize).wrapping_add(call_end));
        if int29 {
            let address = text.virtual_address + pos.0;
            result.push(address);
        }
    }
    result
}
