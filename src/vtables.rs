use bumpalo::collections::Vec as BumpVec;

use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{AnalysisCtx, FunctionFinder};

pub(crate) fn vtables<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
    name: &[u8],
) -> Vec<E::VirtualAddress> {
    // TODO x86_64 probs has Rvas instead

    // Work backwards from:
    // Mem32[vtable - 4] (RTTI info)
    // -> Mem32[addr + 0x10] (Inheritance info)
    // -> Mem32[addr + 0xc] (Inheritance list, len Mem32[addr + 0x8])
    // -> Mem32[addr + x * 4] (Base class for renderer)
    // -> Mem32[addr] (?? Indirection)
    // -> addr + 8 == b".?AVRenderer" (Base class info, in .data instead of .rdata)
    let relocs = functions.relocs_with_values();
    let data = analysis.binary_sections.data;
    let bump = &analysis.bump;
    let base_class_info = relocs.iter().filter_map(|reloc| {
        if reloc.address >= data.virtual_address {
            let offset = ((reloc.address.as_u64() - data.virtual_address.as_u64()) + 8) as usize;
            let bytes = data.data.get(offset..(offset + name.len()))?;
            if bytes == name {
                return Some(reloc.address);
            }
        }
        None
    });
    let base_class_info = BumpVec::from_iter_in(base_class_info, bump);
    let idk_indirection = base_class_info.into_iter().flat_map(|addr| {
        bsearch_equal_slice(&relocs, addr, |x| x.value).map(|x| x.address)
    });
    let idk_indirection = BumpVec::from_iter_in(idk_indirection, bump);
    let inheritance_list = idk_indirection.into_iter().flat_map(|addr| {
        bsearch_equal_slice(&relocs, addr, |x| x.value).map(|x| x.address)
    });
    let inheritance_list = BumpVec::from_iter_in(inheritance_list, bump);
    let inheritance_info = inheritance_list.into_iter().filter_map(|addr| {
        let lower_bound = upper_bound(&relocs, &addr, |x| x.value).saturating_sub(1);
        let reloc = relocs.get(lower_bound)?;
        let address = E::VirtualAddress::from_u64(reloc.address.as_u64().wrapping_sub(4));
        let base_class_count = analysis.binary.read_u32(address).ok()?;
        let is_ok =
            base_class_count as u64 >= addr.as_u64().wrapping_sub(reloc.value.as_u64()) / 4 &&
            base_class_count < 24;
        if is_ok {
            Some(E::VirtualAddress::from_u64(reloc.address.as_u64() - 0xc))
        } else {
            None
        }
    });
    let inheritance_info = BumpVec::from_iter_in(inheritance_info, bump);
    let rtti_info = inheritance_info.into_iter().flat_map(|addr| {
        bsearch_equal_slice(&relocs, addr, |x| x.value)
            .filter_map(|x| {
                // Filter some false positives out
                let address = E::VirtualAddress::from_u64(x.address.as_u64() - 0x10);
                let main_class_info = analysis.binary.read_u32(address + 0xc).ok()?;
                let main_class_info = E::VirtualAddress::from_u64(main_class_info as u64);
                relocs.binary_search_by_key(&main_class_info, |x| x.value)
                    .ok()
                    .map(|_| address)
            })
    });
    let rtti_info = BumpVec::from_iter_in(rtti_info, bump);
    let vtables = rtti_info.into_iter().flat_map(|addr| {
        bsearch_equal_slice(&relocs, addr, |x| x.value).map(|x| x.address + 0x4)
    }).collect();
    vtables
}

fn upper_bound<T, C, F>(slice: &[T], val: &C, mut map_val: F) -> usize
where C: Ord,
      F: FnMut(&T) -> C,
{
    use std::cmp::Ordering;
    slice.binary_search_by(|x| match map_val(x) <= *val {
        true => Ordering::Less,
        false => Ordering::Greater,
    }).unwrap_err()
}

fn lower_bound<T, C, F>(slice: &[T], val: &C, mut map_val: F) -> usize
where C: Ord,
      F: FnMut(&T) -> C,
{
    use std::cmp::Ordering;
    slice.binary_search_by(|x| match map_val(x) < *val {
        true => Ordering::Less,
        false => Ordering::Greater,
    }).unwrap_err()
}

fn bsearch_equal_slice<T, C, F>(slice: &[T], val: C, mut map_val: F,) -> impl Iterator<Item = &T>
where C: Ord + Eq,
      F: FnMut(&T) -> C,
{
    let lower_bound = lower_bound(slice, &val, &mut map_val);
    slice.iter().skip(lower_bound).take_while(move |x| val == map_val(x))
}
