//! Wrap around FxHashMap to undo excessive inline hints hashbrown has

use std::collections::hash_map::Entry as StdEntry;
use std::hash::Hash;

use fxhash::{FxBuildHasher, FxHashMap, FxHashSet};

pub struct HashMap<K, V>(FxHashMap<K, V>);
pub struct HashSet<V>(FxHashSet<V>);

impl<K: Hash + Eq, V> HashMap<K, V> {
    pub fn with_capacity_and_hasher(cap: usize, hasher: FxBuildHasher) -> HashMap<K, V> {
        HashMap(FxHashMap::with_capacity_and_hasher(cap, hasher))
    }

    pub fn reserve(&mut self, size: usize) {
        self.0.reserve(size)
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where K: std::borrow::Borrow<Q>,
          Q: Hash + Eq,
    {
        self.0.get(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.0.insert(k, v)
    }

    pub fn entry(&mut self, key: K) -> StdEntry<'_, K, V> {
        self.0.entry(key)
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }

    pub fn contains_key<Q: ?Sized>(&self, value: &Q) -> bool
    where K: std::borrow::Borrow<Q>,
          Q: Hash + Eq,
    {
        self.0.contains_key(value)
    }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> Option<V>
    where K: std::borrow::Borrow<Q>,
          Q: Hash + Eq,
    {
        self.0.remove(value)
    }

    pub fn into_iter(self) -> std::collections::hash_map::IntoIter<K, V> {
        self.0.into_iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<V: Hash + Eq> HashSet<V> {
    pub fn with_capacity_and_hasher(cap: usize, hasher: FxBuildHasher) -> HashSet<V> {
        HashSet(FxHashSet::with_capacity_and_hasher(cap, hasher))
    }

    pub fn insert(&mut self, v: V) -> bool {
        self.0.insert(v)
    }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where V: std::borrow::Borrow<Q>,
          Q: Hash + Eq,
    {
        self.0.remove(value)
    }

    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where V: std::borrow::Borrow<Q>,
          Q: Hash + Eq,
    {
        self.0.contains(value)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> std::collections::hash_set::Iter<'_, V> {
        self.0.iter()
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<K: Hash + Eq, V> Default for HashMap<K, V> {
    fn default() -> HashMap<K, V> {
        HashMap(Default::default())
    }
}

impl<V: Hash + Eq> Default for HashSet<V> {
    fn default() -> HashSet<V> {
        HashSet(Default::default())
    }
}
