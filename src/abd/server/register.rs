use vstd::prelude::*;
use vstd::rwlock::RwLock;

use crate::abd::proto::{GetResponse, GetTimestampResponse};
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

verus! {

pub struct MonotonicRegisterInner {
    pub val: Option<u64>,
    pub timestamp: Timestamp,
    pub resource: Tracked<MonotonicTimestampResource>,
}

impl MonotonicRegisterInner {
    pub fn default() -> (r: MonotonicRegisterInner)
        ensures
            r.val is None,
            r.timestamp == Timestamp::spec_default(),
            r.resource@@ is HalfRightToAdvance,
            r.inv(),
    {
        let tracked r = MonotonicTimestampResource::alloc();
        let tracked (my_split, inv_split) = r.split();
        MonotonicRegisterInner {
            val: None,
            timestamp: Timestamp::default(),
            resource: Tracked(my_split),
        }
    }

    pub closed spec fn loc(&self) -> int {
        self.resource@.loc()
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.timestamp == self.resource@@.timestamp()
    }

    #[allow(unused_variables)]
    pub fn read(&self) -> (r: GetResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
        ensures
            r.spec_value() == self.val,
            r.spec_timestamp() == self.timestamp,
            r.loc() == self.loc(),
    {
        let val = self.val.clone();
        let timestamp = self.timestamp;
        let tracked r = self.resource.borrow();
        let tracked lb = r.extract_lower_bound();

        proof {
            lb.lemma_lower_bound(r);
        }

        GetResponse::new(self.val.clone(), self.timestamp.clone(), Tracked(lb))
    }

    #[allow(unused_variables)]
    pub fn read_timestamp(&self) -> (r: GetTimestampResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
        ensures
            r.spec_timestamp() == self.timestamp,
            r.loc() == self.loc(),
    {
        let timestamp = self.timestamp;
        let tracked r = self.resource.borrow();
        let tracked lb = r.extract_lower_bound();

        proof {
            lb.lemma_lower_bound(r);
        }

        GetTimestampResponse::new(self.timestamp.clone(), Tracked(lb))
    }

    // TODO: add invariant here to advance
    pub fn write(self, val: Option<u64>, timestamp: Timestamp) -> (r: Self)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
        ensures
            r.inv(),
            r.loc() == self.loc(),
            r.resource@@ is HalfRightToAdvance,
            timestamp > self.timestamp ==> r.timestamp == timestamp && r.val == val,
            timestamp <= self.timestamp ==> self == r,
    {
        if timestamp > self.timestamp {
            let tracked mut r = self.resource.get();
            proof { admit(); /* r.advance_halves(inv.r, timestamp) */ }

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
        &&& v.resource@@ is HalfRightToAdvance
    }
}

pub struct MonotonicRegister {
    inner: RwLock<MonotonicRegisterInner, MonotonicRegisterInv>,
}

impl MonotonicRegister {
    pub fn default() -> (r: Self)
        ensures
            r.inv(),
    {
        let inner_reg = MonotonicRegisterInner::default();
        let tracked r = inner_reg.resource.borrow();
        let resource_loc = Ghost(r.loc());

        let pred = Ghost(MonotonicRegisterInv { resource_loc });
        assert(<MonotonicRegisterInv as vstd::rwlock::RwLockPredicate<_>>::inv(pred@, inner_reg));
        let inner = RwLock::new(inner_reg, pred);

        MonotonicRegister { inner }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        true
    }

    pub closed spec fn loc(&self) -> Ghost<int> {
        self.inner.pred().resource_loc
    }

    pub fn read(&self) -> (r: GetResponse)
        ensures
            r.loc() == self.loc(),
    {
        proof {
            use_type_invariant(self);
        }
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read();
        handle.release_read();

        res
    }

    pub fn read_timestamp(&self) -> (r: GetTimestampResponse)
        ensures
            r.loc() == self.loc(),
    {
        proof {
            use_type_invariant(self);
        }
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read_timestamp();
        handle.release_read();

        res
    }

    pub fn write(&self, val: Option<u64>, timestamp: Timestamp) -> (r: Tracked<
        MonotonicTimestampResource,
    >)
        ensures
            r@@ is LowerBound,
            r@.loc() == self.loc(),
            timestamp <= r@@.timestamp(),
    {
        proof {
            use_type_invariant(self);
        }
        let (guard, handle) = self.inner.acquire_write();

        let new_value = guard.write(val, timestamp);
        let tracked r = new_value.resource.borrow();
        let tracked lower_bound = r.extract_lower_bound();

        proof {
            lower_bound.lemma_lower_bound(r);
        }

        handle.release_write(new_value);

        Tracked(lower_bound)
    }
}

} // verus!
