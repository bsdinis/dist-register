use vstd::prelude::*;

verus! {

pub trait TaggedMessage {
    spec fn spec_tag(self) -> u64;

    fn tag(&self) -> (r: u64)
        ensures
            r == self.spec_tag(),
    ;
}

} // verus!
