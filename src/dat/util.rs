use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use scarf::Rva;

use crate::hash_map::{HashMap};
use crate::util::bumpvec_with_capacity;

/// Queue(*), but also has hash table lookup
/// to remove things from queue.
///
/// (*) Not FIFO though, out order is sorted.
///
/// Assumes that this will be fully built first, and only read
/// from afterwards. (Single HashMap allocation)
///
/// Exists since just using HashSet isn't deterministic.
pub struct UncheckedRefs<'bump> {
    read_pos: u32,
    buf: BumpVec<'bump, Rva>,
    lookup: HashMap<Rva, u32>,
}

impl<'bump> UncheckedRefs<'bump> {
    pub fn new(bump: &'bump Bump) -> UncheckedRefs<'bump> {
        UncheckedRefs {
            read_pos: 0,
            buf: bumpvec_with_capacity(1024, bump),
            lookup: HashMap::default(),
        }
    }

    pub fn push(&mut self, rva: Rva) {
        self.buf.push(rva);
    }

    pub fn pop(&mut self) -> Option<Rva> {
        loop {
            let &rva = self.buf.get(self.read_pos as usize)?;
            self.read_pos += 1;
            // u32::MAX for ones eagerly deleted
            if rva.0 != u32::MAX {
                return Some(rva);
            }
        }
    }

    pub fn build_lookup(&mut self) {
        // Sort so that pop order is consistent.
        // (Push order is not due to code using globals_with_values)
        self.buf.sort_unstable();
        self.lookup.reserve(self.buf.len());
        for (i, &rva) in self.buf.iter().enumerate() {
            self.lookup.insert(rva, i as u32);
        }
    }

    /// Eagerly remove from queue
    pub fn remove(&mut self, rva: Rva) {
        if let Some(idx) = self.lookup.remove(&rva) {
            if let Some(val) = self.buf.get_mut(idx as usize) {
                val.0 = u32::MAX;
            }
        }
    }
}
