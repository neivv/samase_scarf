use byteorder::{ByteOrder, LittleEndian};
use scarf::{BinaryFile, Rva};
use scarf::exec_state::VirtualAddress;

use crate::hash_map::HashMap;

pub struct UnwindFunctions {
    /// Almost always expected to be just 1..
    /// But if it isn't then dat patching changing unwind info
    /// has to handle that so that other function doesn't break.
    unwind_info_refcounts: HashMap<Rva, u32>,
    exception_table_start: Rva,
    /// Length in bytes is `entries * 0xc`
    exception_table_entries: u32,
}

impl UnwindFunctions {
    pub fn new<Va: VirtualAddress>(binary: &BinaryFile<Va>) -> UnwindFunctions {
        Self::try_new(binary).unwrap_or_else(|| UnwindFunctions {
            unwind_info_refcounts: HashMap::default(),
            exception_table_start: Rva(0),
            exception_table_entries: 0,
        })
    }

    pub fn try_new<Va: VirtualAddress>(binary: &BinaryFile<Va>) -> Option<UnwindFunctions> {
        if Va::SIZE == 4 {
            return None;
        }
        let mut read = scarf::BinaryFileWithCachedSection::try_new(binary)?;
        let base = binary.base();
        let pe_header = base + read.read_u32(base + 0x3c)?;
        let exception_offset = read.read_u32(pe_header + 0xa0)?;
        let exception_len = read.read_u32(pe_header + 0xa4)?;
        let exception_table_start = Rva(exception_offset);
        let exception_table_entries = exception_len / 0xc;
        let slice = binary.slice_from_address(base + exception_offset, exception_len).ok()?;
        let mut unwind_info_refcounts = HashMap::with_capacity_and_hasher(
            exception_table_entries as usize,
            Default::default(),
        );
        for func in slice.chunks_exact(0xc) {
            let unwind_info = LittleEndian::read_u32(&func[8..]);
            let count = unwind_info_refcounts.entry(Rva(unwind_info)).or_insert(0u32);
            *count = count.wrapping_add(1);
        }
        Some(UnwindFunctions {
            unwind_info_refcounts,
            exception_table_start,
            exception_table_entries,
        })
    }

    /// Will return None if the address is inside function and not entry.
    pub fn function_unwind_info_address<Va: VirtualAddress>(
        &self,
        binary: &BinaryFile<Va>,
        func_entry: Va,
    ) -> Option<Va> {
        let base = binary.base();
        let mut slice = binary.slice_from_address(
            base + self.exception_table_start.0,
            self.exception_table_entries * 0xc,
        ).ok()?;
        let rva = binary.try_rva_32(func_entry)?;
        // Manual binary search
        // if [T]::as_chunks is stabilized then it could be used instead
        // or bytemuck, or just mem::transmute
        let mut len = self.exception_table_entries as usize;
        while len > 1 {
            let split_index = len / 2; // On uneven length, right will have one more
            let split_byte_index = split_index.wrapping_mul(0xc);
            let (l, r) = slice.split_at(split_byte_index);
            if LittleEndian::read_u32(r) <= rva {
                slice = r;
                len = len.wrapping_add(1) / 2;
            } else {
                slice = l;
                len = split_index;
            }
        }
        let bytes = slice.get(..0xc)?;
        if LittleEndian::read_u32(bytes) == rva {
            Some(base + LittleEndian::read_u32(&bytes[8..]))
        } else {
            None
        }
    }

    pub fn unwind_info_refcount<Va: VirtualAddress>(
        &self,
        binary: &BinaryFile<Va>,
        func_entry: Va,
    ) -> u32 {
        let rva = match binary.try_rva_32(func_entry) {
            Some(s) => s,
            None => return 0,
        };
        self.unwind_info_refcounts.get(&Rva(rva)).copied().unwrap_or(0)
    }
}
