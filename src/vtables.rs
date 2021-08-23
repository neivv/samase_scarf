use byteorder::{ByteOrder, LittleEndian};

use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile};

use crate::{AnalysisCtx};

pub struct Vtable<'e, Va: VirtualAddress> {
    /// Contains the terminating 0 of C string, in order to allow
    /// users to get exact match instead of prefix match by appending the 0.
    pub name: &'e [u8],
    pub address: Va,
}

/// Vtables of the binary.
/// Does not make distinction between the actual class and the
/// parent class that is inherited from and is included in the vtable.
/// (Though could add functions to get primary class name from the vtable if needed)
pub struct Vtables<'e, Va: VirtualAddress> {
    /// Sorted by name
    vtables: Vec<Vtable<'e, Va>>,
}

impl<'e, Va: VirtualAddress> Vtables<'e, Va> {
    pub fn vtables_starting_with<'a>(
        &'a self,
        prefix: &'a [u8],
    ) -> impl Iterator<Item=&'a Vtable<'e, Va>> {
        let start = lower_bound(&self.vtables, &prefix, |x| &x.name);
        // Alternatively could search for end with bsearch
        // end match starts_with(prefix) {
        //      true => Less,
        //      false => match x < prefix {
        //          true => Less,
        //          false => Greater,
        //      }
        //  }
        //  Which is likely bit faster if searching for a very common prefix
        self.vtables.iter()
            .skip(start)
            .take_while(move |x| x.name.starts_with(prefix))
    }

    pub fn all_vtables(&self) -> &[Vtable<'e, Va>] {
        &self.vtables
    }
}

pub(crate) fn vtables<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    relocs: &[E::VirtualAddress],
) -> Vtables<'e, E::VirtualAddress> {
    let mut vtables = Vec::with_capacity(0x2000);
    let text = analysis.binary_sections.text;
    let text_start = text.virtual_address;
    let text_end = text.virtual_address + text.virtual_size;
    let rdata = analysis.binary_sections.rdata;
    let rdata_start = rdata.virtual_address;
    let rdata_end = rdata.virtual_address + rdata.virtual_size;
    let rdata_data = &rdata.data[..];
    let start = lower_bound(relocs, &rdata_start, |&x| x);
    let end = upper_bound(relocs, &rdata_end, |&x| x);
    for window in relocs[start..end].windows(2) {
        let reloc = window[0];
        let next = window[1];
        if reloc + E::VirtualAddress::SIZE != next {
            continue;
        }
        let offset = (reloc.as_u64() as usize).wrapping_sub(rdata_start.as_u64() as usize);
        let value = match rdata_data.get(offset..).and_then(|x| x.get(..8)) {
            Some(s) => E::VirtualAddress::from_u64(LittleEndian::read_u64(s)),
            None => continue,
        };
        if value >= rdata_start && value < rdata_end {
            let next_offset = (next.as_u64() as usize).wrapping_sub(rdata_start.as_u64() as usize);
            let next_value = match rdata_data.get(next_offset..).and_then(|x| x.get(..8)) {
                Some(s) => E::VirtualAddress::from_u64(LittleEndian::read_u64(s)),
                None => continue,
            };
            if next_value >= text_start && next_value < text_end {
                let address = next;
                for name in inherited_classes_from_rtti(value, analysis) {
                    if !name.starts_with(b".?A") {
                        break;
                    }
                    vtables.push(Vtable {
                        name,
                        address,
                    });
                }
            }
        }
    }
    vtables.sort_unstable_by_key(|x| x.name);
    Vtables {
        vtables,
    }
}

fn inherited_classes_from_rtti<'e, E: ExecutionState<'e>>(
    rtti: E::VirtualAddress,
    actx: &AnalysisCtx<'e, E>,
) -> impl Iterator<Item = &'e [u8]> {
    let binary = actx.binary;
    let vtable_offset = binary.read_u32(rtti + 0x4).ok();
    let inherits = read_rtti_ptr(binary, rtti + 0x10)
        .and_then(|x| {
            let count = binary.read_u32(x + 0x8).ok()?;
            let ptr = read_rtti_ptr(binary, x + 0xc)?;
            Some((ptr, count))
        });
    let (vtable_offset, inherits_ptr, count) = match (vtable_offset, inherits) {
        (Some(a), Some((b, count))) if count < 0x40 => (a, b, count),
        _ => (0, E::VirtualAddress::from_u64(0), 0),
    };
    (0..count).filter_map(move |i| {
        let inherited_class = read_rtti_ptr(binary, inherits_ptr + 4 * i)?;
        let inherited_offset = binary.read_u32(inherited_class + 0x8).ok()?;
        if vtable_offset != inherited_offset {
            return None;
        }
        let name_offset = match E::VirtualAddress::SIZE {
            4 => 0x8,
            _ => 0x10,
        };
        let inherited_name = read_rtti_ptr(binary, inherited_class)? + name_offset;
        let name_slice = binary.slice_from_address_to_end(inherited_name).ok()?;
        let name_len = name_slice.iter().position(|&x| x == 0)?;
        Some(&name_slice[..name_len + 1])
    })
}

fn read_rtti_ptr<Va: VirtualAddress>(binary: &BinaryFile<Va>, address: Va) -> Option<Va> {
    if Va::SIZE == 4 {
        binary.read_address(address).ok()
    } else {
        binary.read_u32(address).ok().map(|x| binary.base + x)
    }
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
