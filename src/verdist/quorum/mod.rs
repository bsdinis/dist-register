use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(T)]
pub trait Quorum<T: SpecOrd>: Sized {
    /// A view of the quorum as a set of values
    spec fn view(self) -> Set<T>;

    /// The size of a quorum
    spec fn len(self) -> int;

    /* TODO: incompatible types with operator
    /// The maximum value of the quorum
    closed spec fn max(self) -> T {
        self@.find_unique_maximal(|a: T, b: T| a < b)
    }
    */

    /// Proof of maximum
    // TODO


    /// Invariants of a quorum
    ///     - It must be finite
    ///     - It must be non-empty
    proof fn lemma_quorum_inv(self)
        ensures
            self@.finite(),
            self.len() > 0;

}


// Alternative: specify a predicate about what is a quorum

#[verifier::reject_recursive_types(T)]
pub trait Universe<T: SpecOrd>: Sized {
    type Q: Quorum<T>;

    /// A view of the quorum is a set of values
    spec fn view(self) -> Set<T>;

    /// The size of the universe
    spec fn len(self) -> int;

    /// All quorum in the universe
    spec fn quorums(self) -> Set<Self::Q>;

    /* TODO: incompatible types with operator
    proof fn lemma_quorum_ordering(self)
        ensures
            forall |x: Self::Q|
                self.quorums().contains(x) ==> {
                    &&& self.min_quorum().max() <= x.max()
                    &&& x.max() <= self.max_quorum().max()
                };
    */

    proof fn lemma_intersection(self)
        ensures forall |x: Self::Q, y: Self::Q|
            (self.quorums().contains(x) && self.quorums().contains(y)) ==> !x@.intersect(y@).is_empty();
}



}
