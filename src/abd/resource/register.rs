use vstd::pcm::*;
#[allow(unused_imports)]
use vstd::pcm_lib::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::abd::proto::Timestamp;

verus! {

// A monotonic register permission represents a resource with one of
// the following two values:
//
// `LowerBound{ lower_bound }` -- knowledge that the monotonic counter
// is at least `lower_bound`
//
// `FullRightToAdvance{ value }` -- knowledge that the monotonic counter is
// exactly `value` and the authority to advance it past that value
#[allow(dead_code)]
pub enum MonotonicRegisterResourceValue {
    LowerBound { lower_bound: Timestamp },
    FullRightToAdvance { value: Timestamp },
    Invalid,
}

// To use `MonotonicRegisterResourceValue` as a resource, we have to implement
// `PCM`, showing how to use it in a resource algebra.
impl PCM for MonotonicRegisterResourceValue {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            // Two lower bounds can be combined into a lower bound
            // that's the maximum of the two lower bounds.
            (
                MonotonicRegisterResourceValue::LowerBound { lower_bound: lower_bound1 },
                MonotonicRegisterResourceValue::LowerBound { lower_bound: lower_bound2 },
            ) => {
                let max_lower_bound = if lower_bound1.gt(&lower_bound2) {
                    lower_bound1
                } else {
                    lower_bound2
                };
                MonotonicRegisterResourceValue::LowerBound { lower_bound: max_lower_bound }
            },
            // A lower bound can be combined with a right to
            // advance as long as the lower bound doesn't exceed
            // the value in the right to advance.
            (
                MonotonicRegisterResourceValue::LowerBound { lower_bound },
                MonotonicRegisterResourceValue::FullRightToAdvance { value },
            ) => if lower_bound.le(&value) {
                MonotonicRegisterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicRegisterResourceValue::Invalid {  }
            },
            (
                MonotonicRegisterResourceValue::FullRightToAdvance { value },
                MonotonicRegisterResourceValue::LowerBound { lower_bound },
            ) => if lower_bound.le(&value) {
                MonotonicRegisterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicRegisterResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => MonotonicRegisterResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        MonotonicRegisterResourceValue::LowerBound { lower_bound: Timestamp::spec_default() }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

impl MonotonicRegisterResourceValue {
    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MonotonicRegisterResourceValue::LowerBound { lower_bound } => lower_bound,
            MonotonicRegisterResourceValue::FullRightToAdvance { value } => value,
            MonotonicRegisterResourceValue::Invalid => Timestamp::spec_default(),
        }
    }
}

#[allow(dead_code)]
pub struct MonotonicRegisterResource {
    r: Resource<MonotonicRegisterResourceValue>,
}

impl MonotonicRegisterResource {
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> MonotonicRegisterResourceValue {
        self.r.value()
    }

    // This function creates a monotonic counter and returns a
    // resource granting full authority to advance it and giving
    // knowledge that the current value is 0.
    pub proof fn alloc() -> (tracked result: Self)
        ensures
            result@ == (MonotonicRegisterResourceValue::FullRightToAdvance { value: Timestamp::spec_default() }),
    {
        let v = MonotonicRegisterResourceValue::FullRightToAdvance { value: Timestamp::spec_default() };
        let tracked mut r = Resource::<MonotonicRegisterResourceValue>::alloc(v);
        Self { r }
    }


    // Join two resources
    pub proof fn join(tracked self: Self, tracked other: Self) -> (tracked r: Self)
        requires
            self.loc() == other.loc(),
            self@.timestamp() == other@.timestamp()
        ensures
            r.loc() == self.loc(),
            r@.timestamp() == self@.op(other@).timestamp(),
    {
        let tracked mut r = self.r.join(other.r);
        Self { r }
    }

    // This function uses a resource granting full authority to
    // advance a monotonic counter to increment the counter.
    pub proof fn advance(tracked &mut self, new_value: Timestamp)
        requires
            old(self)@ is FullRightToAdvance,
            new_value.gt(&old(self)@.timestamp()),
        ensures
            self.loc() == old(self).loc(),
            self@ == (MonotonicRegisterResourceValue::FullRightToAdvance {
                value: new_value
            }),
    {
        let r = MonotonicRegisterResourceValue::FullRightToAdvance { value: new_value };
        update_mut(&mut self.r, r);
    }

    pub proof fn extract_lower_bound(tracked &self) -> (tracked out: Self)
        ensures
            out@ is LowerBound,
            out.loc() == self.loc(),
            out@ == (MonotonicRegisterResourceValue::LowerBound { lower_bound: self@.timestamp() }),
    {
        self.r.validate();
        let v = MonotonicRegisterResourceValue::LowerBound { lower_bound: self@.timestamp() };
        let tracked r = copy_duplicable_part(&self.r, v);
        Self { r }
    }

    pub proof fn lemma_lower_bound(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
        ensures
            self@ == old(self)@,
            self.loc() == old(self).loc(),
            self@ is LowerBound && other@ is FullRightToAdvance ==> self@.timestamp().le(&other@.timestamp()),
            other@ is LowerBound && self@ is FullRightToAdvance ==> other@.timestamp().le(&self@.timestamp()),

    {
        self.r.validate_2(&other.r)
    }
}

}
