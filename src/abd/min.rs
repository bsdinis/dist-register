// TODO: move this to verus/verdist/vlib

use vstd::prelude::*;

verus! {

pub trait MinOrd: Ord + Sized + SpecOrd {
    fn minimum() -> (r: Self)
        ensures r == Self::spec_minimum();

    spec fn spec_minimum() -> Self;

    proof fn minimum_is_least()
        ensures
            forall |t: Self| Self::spec_le(&Self::minimum(), &t)
    ;
}

impl MinOrd for u64 {
    fn minimum() -> Self {
        0
    }

    open spec fn spec_minimum() -> Self {
        0
    }

    proof fn minimum_is_least() {}
}

}
