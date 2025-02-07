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

    /// Searches for the closest function in unwind info that
    /// is at address less or equal to `address`
    /// Returns None only when the address is smaller than any function in unwind info, or
    /// the address isn't convertible to Rva32.
    pub fn previous_unwind_function<Va: VirtualAddress>(
        &self,
        binary: &BinaryFile<Va>,
        address: Va,
    ) -> Option<(Va, Va)> {
        let base = binary.base();
        let mut slice = binary.slice_from_address(
            base + self.exception_table_start.0,
            self.exception_table_entries * 0xc,
        ).ok()?;
        let rva = binary.try_rva_32(address)?;
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
        // If this is chained unwind info (Unwind info for subset of a function),
        // return the parent unwind info address
        let mut bytes = slice.get(..0xc)?;
        // Using chained info end; parent end won't include this end.
        // Technically the real function end can be at greater address too,
        // would have to scan forward until non-chained unwind entry is found.
        let end = LittleEndian::read_u32(&bytes[4..]);
        loop {
            let unwind_info_rva = LittleEndian::read_u32(&bytes[8..]);
            let unwind_info = binary.slice_from_address_to_end(base + unwind_info_rva).ok()?;
            if *unwind_info.get(0)? & (0x4 << 3) != 0 {
                // Is chain
                let &code_count = unwind_info.get(2)?;
                let offset = 4 + code_count as usize * 2;
                bytes = unwind_info.get(offset..offset + 0xc)?;
            } else {
                let rva = LittleEndian::read_u32(&bytes[0..]);
                break Some((base + rva, base + end));
            }
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
