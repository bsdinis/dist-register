//! Monotonic map: a map that can only grow (by inserting new elements)
//!
//! ### Example
//!
//! ```
//! fn example_use() {
//!     let tracked mut mmap = GhostMonotonicMap::empty();
//!     assert(mmap@ == map![]);
//!     let map_lb_1 = mmap.insert(1, 2);
//!     assert(map_lb_1@ == map![1 => 2]);
//!     assert(mmap@ == map![1 => 2]);
//!
//!     let map_lb_2 = mmap.insert_map(map![2 => 4, 4 => 8]);
//!     assert(map_lb_2@ <= mmap@);
//! }
//!
//! proof fn when_we_have(tracked map: &GhostMonotonicMap<K, V>, tracked lb: &GhostPersistentSubmap<K, V>)
//!     requires map.id() == lb.id()
//! {
//!     lemma_monotonic_map(map, lb);
//!     // we know the lowerbound is a lowerbound
//!     assert(lb@ <= map@);
//! }
//! ```
use vstd::prelude::*;
use vstd::resource::map::GhostMapAuth;
#[cfg(verus_only)]
use vstd::resource::map::GhostPersistentPointsTo;
use vstd::resource::map::GhostPersistentSubmap;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

#[verifier::reject_recursive_types(K)]
pub tracked struct GhostMonotonicMap<K, V> {
    #[allow(dead_code)]
    auth: GhostMapAuth<K, V>,
    #[allow(dead_code)]
    sub: GhostPersistentSubmap<K, V>,
}

impl<K, V> GhostMonotonicMap<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.auth.id() == self.sub.id()
        &&& self.auth@ == self.sub@
    }

    /// Map location
    pub closed spec fn id(self) -> Loc {
        self.auth.id()
    }

    /// Logically underlying [`Map`]
    pub closed spec fn view(self) -> Map<K, V> {
        self.auth@
    }

    /// Domain of the [`GhostMonotonicMap`]
    pub closed spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    /// Indexing operation `map[key]`
    pub closed spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    /// Creating an empty [`GhostMonotonicMap`]
    pub proof fn empty() -> (tracked result: GhostMonotonicMap<K, V>)
        ensures
            result@ == Map::<K, V>::empty(),
    {
        let tracked (auth, sub) = GhostMapAuth::new(Map::empty());
        let tracked sub = sub.persist();
        GhostMonotonicMap { auth, sub }
    }

    /// Creating a [`GhostMonotonicMap`] from a particular [`Map`]
    pub proof fn new(m: Map<K, V>) -> (tracked result: GhostMonotonicMap<K, V>)
        ensures
            result@ == m,
    {
        let tracked (auth, own_sub) = GhostMapAuth::new(m);
        let tracked sub = own_sub.persist();
        GhostMonotonicMap { auth, sub }
    }

    /// Instantiate a dummy [`GhostMonotonicMap`]
    pub proof fn dummy() -> (tracked result: GhostMonotonicMap<K, V>) {
        GhostMonotonicMap::<K, V>::empty()
    }

    /// Insert a [`Map`] of values, receiving the [`GhostPersistentSubmap`] that serves as the
    /// lower bound for the monotonic map
    pub proof fn insert_map(tracked &mut self, m: Map<K, V>) -> (tracked result:
        GhostPersistentSubmap<K, V>)
        requires
            old(self)@.dom().disjoint(m.dom()),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.union_prefer_right(m),
            result.id() == final(self).id(),
            m == result@,
    {
        use_type_invariant(&*self);

        let tracked mut x = Self::dummy();
        vstd::modes::tracked_swap(&mut x, self);
        let tracked GhostMonotonicMap { mut auth, mut sub } = x;
        let tracked added = auth.insert_map(m);
        let tracked mut p_added = added.persist();
        let tracked result = p_added.duplicate();
        sub.combine(p_added);
        let tracked mut y = GhostMonotonicMap { auth, sub };
        vstd::modes::tracked_swap(&mut y, self);

        result
    }

    /// Insert a key-value pair, receiving the [`GhostPersistentSubmap`] that serves as the
    /// lower bound for the monotonic map
    pub proof fn insert(tracked &mut self, k: K, v: V) -> (tracked result: GhostPersistentPointsTo<
        K,
        V,
    >)
        requires
            !old(self)@.dom().contains(k),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(k, v),
            result.id() == final(self).id(),
            result@ == (k, v),
    {
        use_type_invariant(&*self);

        let tracked mut x = Self::dummy();
        vstd::modes::tracked_swap(&mut x, self);
        let tracked GhostMonotonicMap { mut auth, mut sub } = x;
        let tracked added = auth.insert(k, v);
        let tracked mut p_added = added.persist();
        let tracked result = p_added.duplicate();
        sub.combine_points_to(p_added);
        let tracked mut y = GhostMonotonicMap { auth, sub };
        vstd::modes::tracked_swap(&mut y, self);

        result
    }

    /// Extract a prefix of the current map
    pub proof fn lower_bound(tracked &mut self) -> (tracked result: GhostPersistentSubmap<K, V>)
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            result@ == final(self)@,
            final(self).id() == result.id(),
    {
        use_type_invariant(&*self);
        self.sub.duplicate()
    }

    /// Find if a submap is a lowerbound
    pub proof fn lemma_lb(tracked &self, tracked lb: &GhostPersistentSubmap<K, V>)
        requires
            self.id() == lb.id(),
        ensures
            lb@ <= self@,
    {
        lb.agree(&self.auth);
    }

    /// Find if a points to is a lowerbound
    pub proof fn lemma_lb_points_to(tracked &self, tracked lb: &GhostPersistentPointsTo<K, V>)
        requires
            self.id() == lb.id(),
        ensures
            self@.contains_pair(lb.key(), lb.value()),
    {
        lb.agree(&self.auth);
    }
}

} // verus!
