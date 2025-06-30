use builtin::*;
use builtin_macros::*;
use vstd::pcm::*;
#[allow(unused_imports)]
use vstd::pcm_lib::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::rwlock::RwLock;

use crate::abd::proto::Timestamp;

verus! {

// A monotonic register permission represents a resource with one of
// the following three values:
//
// `LowerBound{ lower_bound }` -- knowledge that the monotonic counter
// is at least `lower_bound`
//
// `FullRightToAdvance{ value }` -- knowledge that the monotonic counter is
// exactly `value` and the authority to advance it past that value
#[allow(dead_code)]
pub enum MonotonicRegisterResourceValue {
    LowerBound { lower_bound: (nat, nat) },
    FullRightToAdvance { value: (nat, nat) },
    Invalid,
}

pub open spec fn nat_pair_gt(lhs: &(nat, nat), rhs: &(nat, nat)) -> bool
{
    (lhs.0 > rhs.0) || (lhs.0 == rhs.0 && lhs.1 > rhs.1)
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
                let max_lower_bound = if nat_pair_gt(&lower_bound1, &lower_bound2) {
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
            ) => if !nat_pair_gt(&lower_bound, &value) {
                MonotonicRegisterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicRegisterResourceValue::Invalid {  }
            },
            (
                MonotonicRegisterResourceValue::FullRightToAdvance { value },
                MonotonicRegisterResourceValue::LowerBound { lower_bound },
            ) => if !nat_pair_gt(&lower_bound, &value) {
                MonotonicRegisterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicRegisterResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => MonotonicRegisterResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        MonotonicRegisterResourceValue::LowerBound { lower_bound: (0, 0) }
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
    pub open spec fn timestamp(self) -> (nat, nat) {
        match self {
            MonotonicRegisterResourceValue::LowerBound { lower_bound } => lower_bound,
            MonotonicRegisterResourceValue::FullRightToAdvance { value } => value,
            MonotonicRegisterResourceValue::Invalid => (0, 0),
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
            result@ == (MonotonicRegisterResourceValue::FullRightToAdvance { value: (0, 0) }),
    {
        let v = MonotonicRegisterResourceValue::FullRightToAdvance { value: (0, 0) };
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
    pub proof fn advance(tracked &mut self, new_value: (nat, nat))
        requires
            old(self)@ is FullRightToAdvance,
            nat_pair_gt(&new_value, &old(self)@.timestamp()),
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
            self@ is LowerBound && other@ is FullRightToAdvance ==> !nat_pair_gt(&self@.timestamp(), &other@.timestamp()),
            other@ is LowerBound && self@ is FullRightToAdvance ==> !nat_pair_gt(&other@.timestamp(), &self@.timestamp()),

    {
        self.r.validate_2(&other.r)
    }
}

pub struct MonotonicRegisterInner {
    val: Option<u64>,
    timestamp: Timestamp,
    resource: Tracked<MonotonicRegisterResource>
}

impl MonotonicRegisterInner {
    pub fn default() -> (r: MonotonicRegisterInner)
        ensures
            r.spec_val() is None,
            r.spec_timestamp().client_id == 0,
            r.spec_timestamp().seqno == 0,
            r.spec_resource()@@ is FullRightToAdvance,
    {
        MonotonicRegisterInner {
            val: None,
            timestamp: Timestamp::default(),
            resource: Tracked(MonotonicRegisterResource::alloc())
        }
    }

    pub closed spec fn loc(&self) -> Ghost<int> {
        Ghost(self.resource@.loc())
    }

    pub fn val(&self) -> Option<u64> {
         proof {
            use_type_invariant(self);
        }
        self.val
    }

    pub closed spec fn spec_val(&self) -> Option<u64> {
        self.val
    }

    pub fn timestamp(&self) -> Timestamp {
         proof {
            use_type_invariant(self);
        }
        self.timestamp
    }

    pub closed spec fn spec_timestamp(&self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_resource(&self) -> &Tracked<MonotonicRegisterResource> {
        &self.resource
    }

    pub fn get_resource(self) -> (r: Tracked<MonotonicRegisterResource>)
        ensures
            r == self.spec_resource(),
            r@.loc() == self.loc()
    {
         proof {
            use_type_invariant(&self);
        }
        self.resource
    }

    #[verifier::type_invariant]
    pub open spec fn inv(&self) -> bool {
        self.spec_timestamp().to_nat() == self.spec_resource()@@.timestamp()
    }

    #[allow(unused_variables)]
    pub fn read(&self, lower_bound: Tracked<MonotonicRegisterResource>) -> (r: MonotonicRegisterInner)
        requires
            self.spec_resource()@@ is FullRightToAdvance,
            lower_bound@@ is LowerBound,
            lower_bound@.loc() == self.loc(),
        ensures
            lower_bound@.loc() == r.loc(),
            !nat_pair_gt(&lower_bound@@.timestamp(), &r.spec_resource()@@.timestamp()),
            r.spec_resource()@@ is LowerBound,
            r.spec_val() == self.spec_val(),
            r.spec_timestamp() == self.spec_timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        let val = self.val;
        let timestamp = self.timestamp;
        let tracked r = self.resource.borrow();
        let tracked lb = lower_bound.get();

        proof {
            lb.lemma_lower_bound(r);
        }

        let tracked lower_bound = r.extract_lower_bound();
        MonotonicRegisterInner {
            val,
            timestamp,
            resource: Tracked(lower_bound),
        }
    }

    pub fn write(self, val: Option<u64>, timestamp: Timestamp) -> (r: Self)
        requires
            self.spec_resource()@@ is FullRightToAdvance,
        ensures
            r.spec_resource()@@ is FullRightToAdvance,
            r.loc() == self.loc(),
            nat_pair_gt(&timestamp.to_nat(), &self.spec_resource()@@.timestamp()) ==> r.spec_timestamp() == timestamp && r.spec_val() == val,
            !nat_pair_gt(&timestamp.to_nat(), &self.spec_resource()@@.timestamp()) ==> self == r
    {
        proof {
            use_type_invariant(&self);
        }

        if timestamp.seqno > self.timestamp.seqno || (timestamp.seqno == self.timestamp.seqno && timestamp.client_id > self.timestamp.client_id) {
            let tracked mut r = self.resource.get();
            proof {
                r.advance(timestamp.to_nat())
            }

            MonotonicRegisterInner { val, timestamp, resource: Tracked(r) }
        } else {
            self
        }
    }
}

pub struct MonotonicRegisterInv {
    #[allow(dead_code)]
    pub resource_loc: Ghost<int>,
}

impl vstd::rwlock::RwLockPredicate<MonotonicRegisterInner> for MonotonicRegisterInv {
    open spec fn inv(self, v: MonotonicRegisterInner) -> bool {
        &&& v.inv()
        &&& v.loc() == self.resource_loc
        &&& v.spec_resource()@@ is FullRightToAdvance
    }
}

pub struct MonotonicRegister {
    inner: RwLock<MonotonicRegisterInner, MonotonicRegisterInv>,
    #[allow(dead_code)]
    resource_loc: Ghost<int>,
}

impl MonotonicRegister {
    // return the register and the lower bound
    pub fn default() -> (r: (Self, Tracked<MonotonicRegisterResource>))
        ensures
            r.1@@ is LowerBound,
            r.0.loc() == r.1@.loc(),
            r.0.inv()
    {
        let inner_reg = MonotonicRegisterInner::default();
        let tracked r = inner_reg.resource.borrow();
        let resource_loc = Ghost(r.loc());

        let tracked lower_bound = r.extract_lower_bound();

        proof  {
            use_type_invariant(&inner_reg);
        }

        let inner = RwLock::new(inner_reg, Ghost(MonotonicRegisterInv { resource_loc }));

        let r = (MonotonicRegister {
            inner,
            resource_loc
        }, Tracked(lower_bound));

        r
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.inner.pred() == MonotonicRegisterInv { resource_loc: self.resource_loc }
    }

    pub closed spec fn loc(&self) -> Ghost<int> {
        self.resource_loc
    }

    pub fn read(&self, lower_bound: Tracked<MonotonicRegisterResource>) -> (r: MonotonicRegisterInner)
        requires
            lower_bound@@ is LowerBound,
            lower_bound@.loc() == self.loc(),
        ensures
            r.spec_resource()@@ is LowerBound,
            r.loc() == self.loc(),
            !nat_pair_gt(&lower_bound@@.timestamp(), &r.spec_resource()@@.timestamp()),
    {
        proof {
            use_type_invariant(self);
        }
        let handle = self.inner.acquire_read();
        let val = handle.borrow();
        let res = val.read(lower_bound);
        handle.release_read();

        res
    }

    pub fn write(&self, val: Option<u64>, timestamp: Timestamp) -> (r: Tracked<MonotonicRegisterResource>)
        ensures
            r@@ is LowerBound,
            r@.loc() == self.loc(),
            !nat_pair_gt(&timestamp.to_nat(), &r@@.timestamp()),
    {
        proof {
            use_type_invariant(self);
        }
        let (guard, handle) = self.inner.acquire_write();

        let new_value = guard.write(val, timestamp);
        proof  {
            use_type_invariant(&new_value);
        }

        let tracked r = new_value.resource.borrow();
        let tracked lower_bound = r.extract_lower_bound();

        proof {
            lower_bound.lemma_lower_bound(r);
        }

        handle.release_write(new_value);

        Tracked(lower_bound)
    }
}

}
