//! Monotonic set: a set that can only grow (by inserting new elements)
//!
//! ### Example
//!
//! ```
//! fn example_use() {
//!     let tracked mut mset = GhostMonotonicSet::empty();
//!     assert(mset@ == set![]);
//!     let set_lb_1 = mset.insert(1, 2);
//!     assert(set_lb_1@ == set![1 => 2]);
//!     assert(mset@ == set![1 => 2]);
//!
//!     let set_lb_2 = mset.insert_set(set![2 => 4, 4 => 8]);
//!     assert(set_lb_2@ <= mset@);
//! }
//! ```
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::set::GhostPersistentSingleton;
use vstd::resource::set::GhostPersistentSubset;
use vstd::resource::set::GhostSetAuth;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

#[verifier::reject_recursive_types(T)]
pub tracked struct GhostMonotonicSet<T> {
    #[allow(dead_code)]
    auth: GhostSetAuth<T>,
    #[allow(dead_code)]
    sub: GhostPersistentSubset<T>,
}

impl<T> GhostMonotonicSet<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.auth.id() == self.sub.id()
        &&& self.auth@ == self.sub@
    }

    /// Set location
    pub closed spec fn id(self) -> Loc {
        self.auth.id()
    }

    /// Logically underlying [`Set`]
    pub closed spec fn view(self) -> Set<T> {
        self.auth@
    }

    /// Creating an empty [`GhostMonotonicSet`]
    pub proof fn empty() -> (tracked result: GhostMonotonicSet<T>)
        ensures
            result@ == Set::<T>::empty(),
    {
        let tracked (auth, sub) = GhostSetAuth::new(Set::empty());
        let tracked sub = sub.persist();
        GhostMonotonicSet { auth, sub }
    }

    /// Creating a [`GhostMonotonicSet`] from a particular [`Set`]
    pub proof fn new(m: Set<T>) -> (tracked result: GhostMonotonicSet<T>)
        ensures
            result@ == m,
    {
        let tracked (auth, own_sub) = GhostSetAuth::new(m);
        let tracked sub = own_sub.persist();
        GhostMonotonicSet { auth, sub }
    }

    /// Instantiate a dummy [`GhostMonotonicSet`]
    pub proof fn dummy() -> (tracked result: GhostMonotonicSet<T>) {
        GhostMonotonicSet::<T>::empty()
    }

    /// Insert a [`Set`] of values, receiving the [`GhostPersistentSubset`] that serves as the
    /// lower bound for the monotonic set
    pub proof fn insert_set(tracked &mut self, s: Set<T>) -> (tracked result: GhostPersistentSubset<
        T,
    >)
        requires
            old(self)@.disjoint(s),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.union(s),
            result.id() == final(self).id(),
            s == result@,
    {
        use_type_invariant(&*self);

        let tracked mut x = Self::dummy();
        vstd::modes::tracked_swap(&mut x, self);
        let tracked GhostMonotonicSet { mut auth, mut sub } = x;
        let tracked added = auth.insert_set(s);
        let tracked mut p_added = added.persist();
        let tracked result = p_added.duplicate();
        sub.combine(p_added);
        let tracked mut y = GhostMonotonicSet { auth, sub };
        vstd::modes::tracked_swap(&mut y, self);

        result
    }

    /// Insert a key-value pair, receiving the [`GhostPersistentSubset`] that serves as the
    /// lower bound for the monotonic set
    pub proof fn insert(tracked &mut self, v: T) -> (tracked result: GhostPersistentSingleton<T>)
        requires
            !old(self)@.contains(v),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(v),
            result.id() == final(self).id(),
            result@ == v,
    {
        use_type_invariant(&*self);

        let tracked mut x = Self::dummy();
        vstd::modes::tracked_swap(&mut x, self);
        let tracked GhostMonotonicSet { mut auth, mut sub } = x;
        let tracked added = auth.insert(v);
        let tracked mut p_added = added.persist();
        let tracked result = p_added.duplicate();
        sub.combine_points_to(p_added);
        let tracked mut y = GhostMonotonicSet { auth, sub };
        vstd::modes::tracked_swap(&mut y, self);

        result
    }

    /// Extract a prefix of the current set
    pub proof fn lower_bound(tracked &mut self) -> (tracked result: GhostPersistentSubset<T>)
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self).id() == result.id(),
    {
        use_type_invariant(&*self);
        self.sub.duplicate()
    }
}

} // verus!
