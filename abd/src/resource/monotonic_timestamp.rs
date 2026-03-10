use crate::timestamp::Timestamp;

use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::Resource;
use vstd::resource::pcm::PCM;
#[allow(unused_imports)]
use vstd::resource::Loc;

#[allow(unused_imports)]
use vstd::resource::*;

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
pub enum MonotonicTimestampResourceValue {
    LowerBound { lower_bound: Timestamp },
    FullRightToAdvance { value: Timestamp },
    HalfRightToAdvance { value: Timestamp },
    Invalid,
}

impl ResourceAlgebra for MonotonicTimestampResourceValue {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
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
            // full
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
            // half
            (
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
                MonotonicTimestampResourceValue::HalfRightToAdvance { value },
            ) => if lower_bound <= value {
                MonotonicTimestampResourceValue::HalfRightToAdvance { value }
            } else {
                MonotonicTimestampResourceValue::Invalid {  }
            },
            (
                MonotonicTimestampResourceValue::HalfRightToAdvance { value },
                MonotonicTimestampResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                MonotonicTimestampResourceValue::HalfRightToAdvance { value }
            } else {
                MonotonicTimestampResourceValue::Invalid {  }
            },
            // Two half rights to advance can be combined into a full right to advance
            // iff they agree on the value
            (
                MonotonicTimestampResourceValue::HalfRightToAdvance { value: lvalue },
                MonotonicTimestampResourceValue::HalfRightToAdvance { value: rvalue },
            ) => if lvalue == rvalue {
                MonotonicTimestampResourceValue::FullRightToAdvance { value: lvalue }
            } else {
                MonotonicTimestampResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => MonotonicTimestampResourceValue::Invalid {  },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl PCM for MonotonicTimestampResourceValue {
    open spec fn unit() -> Self {
        MonotonicTimestampResourceValue::LowerBound { lower_bound: Timestamp::spec_default() }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

impl MonotonicTimestampResourceValue {
    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MonotonicTimestampResourceValue::LowerBound { lower_bound } => lower_bound,
            MonotonicTimestampResourceValue::FullRightToAdvance { value } => value,
            MonotonicTimestampResourceValue::HalfRightToAdvance { value } => value,
            MonotonicTimestampResourceValue::Invalid => Timestamp::spec_default(),
        }
    }
}

#[allow(dead_code)]
pub struct MonotonicTimestampResource {
    r: Resource<MonotonicTimestampResourceValue>,
}

impl MonotonicTimestampResource {
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> MonotonicTimestampResourceValue {
        self.r.value()
    }

    // This function creates a monotonic timestamp and returns a
    // resource granting full authority to advance it and giving
    // knowledge that the current value is 0.
    pub proof fn alloc() -> (tracked result: Self)
        ensures
            result@ == (MonotonicTimestampResourceValue::FullRightToAdvance {
                value: Timestamp::spec_default(),
            }),
    {
        let v = MonotonicTimestampResourceValue::FullRightToAdvance {
            value: Timestamp::spec_default(),
        };
        let tracked r = Resource::<MonotonicTimestampResourceValue>::alloc(v);
        Self { r }
    }

    // Join two resources
    pub proof fn join(tracked self: Self, tracked other: Self) -> (tracked r: Self)
        requires
            self.loc() == other.loc(),
            self@.timestamp() == other@.timestamp(),
        ensures
            r.loc() == self.loc(),
            r@.timestamp() == MonotonicTimestampResourceValue::op(self@, other@).timestamp(),
    {
        let tracked r = self.r.join(other.r);
        Self { r }
    }

    // Split a full authority into two halves
    pub proof fn split(tracked self) -> (tracked r: (Self, Self))
        requires
            self@ is FullRightToAdvance,
        ensures
            r.0.loc() == self.loc(),
            r.1.loc() == self.loc(),
            r.0@.timestamp() == self@.timestamp(),
            r.1@.timestamp() == self@.timestamp(),
            r.0@ is HalfRightToAdvance,
            r.1@ is HalfRightToAdvance,
    {
        let half = MonotonicTimestampResourceValue::HalfRightToAdvance {
            value: self@->FullRightToAdvance_value,
        };
        let tracked (left, right) = self.r.split(half, half);
        (MonotonicTimestampResource { r: left }, MonotonicTimestampResource { r: right })
    }

    // This function uses a resource granting full authority to
    // advance a monotonic timestamp to increment the timestamp.
    pub proof fn advance(tracked &mut self, new_value: Timestamp)
        requires
            old(self)@ is FullRightToAdvance,
            new_value > old(self)@.timestamp(),
        ensures
            self.loc() == old(self).loc(),
            self@ == (MonotonicTimestampResourceValue::FullRightToAdvance { value: new_value }),
    {
        let r = MonotonicTimestampResourceValue::FullRightToAdvance { value: new_value };
        update_mut(&mut self.r, r);
    }

    // This function uses a resource granting full authority to
    // advance a monotonic timestamp to increment the timestamp.
    pub proof fn advance_halves(tracked &mut self, tracked other: &mut Self, new_value: Timestamp)
        requires
            old(self).loc() == old(other).loc(),
            old(self)@ is HalfRightToAdvance,
            old(other)@ is HalfRightToAdvance,
            new_value > old(self)@.timestamp(),
        ensures
            self.loc() == old(self).loc(),
            other.loc() == old(other).loc(),
            self@.timestamp() == new_value,
            other@.timestamp() == new_value,
            self@ is HalfRightToAdvance,
            other@ is HalfRightToAdvance,
    {
        self.r.validate_2(&other.r);
        let updated = MonotonicTimestampResourceValue::HalfRightToAdvance { value: new_value };
        update_and_redistribute(&mut self.r, &mut other.r, updated, updated);
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
            self@ is LowerBound && other@ is HalfRightToAdvance ==> self@.timestamp()
                <= other@.timestamp(),
            other@ is LowerBound && self@ is HalfRightToAdvance ==> other@.timestamp()
                <= self@.timestamp(),
    {
        self.r.validate_2(&other.r)
    }

    pub proof fn lemma_halves_agree(tracked &mut self, tracked other: &Self)
        requires
            old(self).loc() == other.loc(),
            old(self)@ is HalfRightToAdvance,
            other@ is HalfRightToAdvance,
        ensures
            self.loc() == old(self).loc(),
            self@ == old(self)@,
            self@.timestamp() == other@.timestamp(),
    {
        self.r.validate_2(&other.r)
    }
}

} // verus!
