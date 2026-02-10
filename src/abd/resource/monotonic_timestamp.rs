#[cfg(verus_keep_ghost)]
use crate::abd::min::MinOrd;
use crate::abd::timestamp::Timestamp;

#[allow(unused_imports)]
use vstd::pcm::Loc;
use vstd::pcm::Resource;
use vstd::pcm::PCM;

#[allow(unused_imports)]
use vstd::pcm_lib::*;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::default::DefaultSpec;

use vstd::prelude::*;

verus! {


// A monotonic timestamp permission represents a resource with one of
// the following two values:
//
// `LowerBound{ lower_bound }` -- knowledge that the monotonic timestamp
// is at least `lower_bound`
//
// `FullRightToAdvance{ value }` -- knowledge that the monotonic timestamp is
// exactly `value` and the authority to advance it past that value
#[allow(dead_code)]
pub enum MonotonicTimestampResourceValue<Id> {
    LowerBound { lower_bound: Timestamp<Id> },
    FullRightToAdvance { value: Timestamp<Id> },
    Invalid,
}

// To use `MonotonicTimestampResourceValue` as a resource, we have to implement
// `PCM`, showing how to use it in a resource algebra.
impl<Id: MinOrd> PCM for MonotonicTimestampResourceValue<Id> {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            // Two lower bounds can be combined into a lower bound
            // that's the maximum of the two lower bounds.
            (
                MonotonicTimestampResourceValue::LowerBound { lower_bound: lower_bound1 },
                MonotonicTimestampResourceValue::LowerBound { lower_bound: lower_bound2 },
            ) => {
                let max_lower_bound = if lower_bound1 > lower_bound2 {
                    lower_bound1
                } else {
                    lower_bound2
                };
                MonotonicTimestampResourceValue::LowerBound { lower_bound: max_lower_bound }
            },
            // A lower bound can be combined with a right to
            // advance as long as the lower bound doesn't exceed
            // the value in the right to advance.
            (
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
                MonotonicTimestampResourceValue::FullRightToAdvance { value },
            ) => if lower_bound <= value {
                MonotonicTimestampResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicTimestampResourceValue::Invalid {  }
            },
            (
                MonotonicTimestampResourceValue::FullRightToAdvance { value },
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                MonotonicTimestampResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicTimestampResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => MonotonicTimestampResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        MonotonicTimestampResourceValue::LowerBound { lower_bound: Timestamp::<Id>::spec_minimum() }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
        broadcast use crate::abd::timestamp::timestamp_cmp_laws;
        match (a, b) {
            (
                MonotonicTimestampResourceValue::LowerBound { lower_bound: lower_bound1 },
                MonotonicTimestampResourceValue::LowerBound { lower_bound: lower_bound2 },
            ) => {
                admit(); // TODO(id)
                assert(Self::op(a,b) == Self::op(b, a));
            },
            (
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
                MonotonicTimestampResourceValue::FullRightToAdvance { value },
            ) => if lower_bound <= value {
                assert(Self::op(a,b) == Self::op(b, a));
            } else {
                assert(Self::op(a,b) == Self::op(b, a));
            },
            (
                MonotonicTimestampResourceValue::FullRightToAdvance { value },
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                assert(Self::op(a,b) == Self::op(b, a));
            } else {
                assert(Self::op(a,b) == Self::op(b, a));
            },
            (_, _) => {
                assert(Self::op(a,b) == Self::op(b, a));
            }
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        admit(); // TODO(id)
    }

    proof fn op_unit(a: Self) {
        admit(); // TODO(id)
    }

    proof fn unit_valid() {
    }
}

impl<Id: MinOrd> MonotonicTimestampResourceValue<Id> {
    pub open spec fn timestamp(self) -> Timestamp<Id>
        recommends self.valid()
    {
        match self {
            MonotonicTimestampResourceValue::LowerBound { lower_bound } => lower_bound,
            MonotonicTimestampResourceValue::FullRightToAdvance { value } => value,
            MonotonicTimestampResourceValue::Invalid => arbitrary::<Timestamp<Id>>()
        }
    }
}

#[allow(dead_code)]
pub struct MonotonicTimestampResource<Id> {
    r: Resource<MonotonicTimestampResourceValue<Id>>,
}

impl<Id: MinOrd> MonotonicTimestampResource<Id> {
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> MonotonicTimestampResourceValue<Id> {
        self.r.value()
    }

    // This function creates a monotonic timestamp and returns a
    // resource granting full authority to advance it and giving
    // knowledge that the current value is 0.
    pub proof fn alloc() -> (tracked result: Self)
        ensures
            result@ == (MonotonicTimestampResourceValue::FullRightToAdvance {
                value: Timestamp::<Id>::spec_minimum(),
            }),
    {
        let v = MonotonicTimestampResourceValue::FullRightToAdvance {
            value: Timestamp::<Id>::spec_minimum(),
        };
        let tracked mut r = Resource::<MonotonicTimestampResourceValue<Id>>::alloc(v);
        Self { r }
    }

    // Join two resources
    pub proof fn join(tracked self: Self, tracked other: Self) -> (tracked r: Self)
        requires
            self.loc() == other.loc(),
            self@.timestamp() == other@.timestamp(),
        ensures
            r.loc() == self.loc(),
            r@.timestamp() == self@.op(other@).timestamp(),
    {
        let tracked mut r = self.r.join(other.r);
        Self { r }
    }

    // This function uses a resource granting full authority to
    // advance a monotonic timestamp to increment the timestamp.
    pub proof fn advance(tracked &mut self, new_value: Timestamp<Id>)
        requires
            old(self)@ is FullRightToAdvance,
            new_value > old(self)@.timestamp(),
        ensures
            self.loc() == old(self).loc(),
            self@ == (MonotonicTimestampResourceValue::FullRightToAdvance { value: new_value }),
    {
        let r = MonotonicTimestampResourceValue::FullRightToAdvance { value: new_value };
        assume(vstd::pcm::frame_preserving_update(self.r.value(), r)); // TODO(id)
        update_mut(&mut self.r, r);
    }

    pub proof fn extract_lower_bound(tracked &self) -> (tracked out: Self)
        ensures
            out@ is LowerBound,
            out.loc() == self.loc(),
            out@ == (MonotonicTimestampResourceValue::LowerBound {
                lower_bound: self@.timestamp(),
            }),
    {
        self.r.validate();
        let v = MonotonicTimestampResourceValue::LowerBound { lower_bound: self@.timestamp() };
        let tracked r = copy_duplicable_part(&self.r, v);
        Self { r }
    }

    pub proof fn lemma_lower_bound(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            self@ == old(self)@,
            self.loc() == old(self).loc(),
            self@ is LowerBound && other@ is FullRightToAdvance ==> self@.timestamp()
                <= other@.timestamp(),
            other@ is LowerBound && self@ is FullRightToAdvance ==> other@.timestamp()
                <= self@.timestamp(),
    {
        self.r.validate_2(&other.r)
    }
}

} // verus!
