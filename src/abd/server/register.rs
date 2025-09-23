#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::rwlock::RwLock;

use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

verus! {

pub struct MonotonicRegisterInner {
    pub val: Option<u64>,
    pub timestamp: Timestamp,
    pub resource: Tracked<MonotonicTimestampResource>
}

impl MonotonicRegisterInner {
    pub fn default() -> (r: MonotonicRegisterInner)
        ensures
            r.val is None,
            r.timestamp.client_id == 0,
            r.timestamp.seqno == 0,
            r.resource@@ is FullRightToAdvance,
            r.inv(),
    {
        MonotonicRegisterInner {
            val: None,
            timestamp: Timestamp::default(),
            resource: Tracked(MonotonicTimestampResource::alloc())
        }
    }

    pub closed spec fn loc(&self) -> Ghost<int> {
        Ghost(self.resource@.loc())
    }

    pub fn lower_bound(&self) -> (r: Tracked<MonotonicTimestampResource>)
        requires
            self.inv()
        ensures
            r@.loc() == self.loc(),
            r@@ is LowerBound,
            r@@.timestamp() == self.resource@@.timestamp()
    {
        Tracked(self.resource.borrow().extract_lower_bound())
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.timestamp == self.resource@@.timestamp()
    }

    #[allow(unused_variables)]
    pub fn read(&self) -> (r: MonotonicRegisterInner)
        requires
            self.resource@@ is FullRightToAdvance,
            self.inv(),
        ensures
            r.inv(),
            r.resource@@ is LowerBound,
            r.val == self.val,
            r.timestamp == self.timestamp,
            r.loc() == self.loc(),
    {
        let val = self.val;
        let timestamp = self.timestamp;
        let tracked r = self.resource.borrow();
        let tracked lb = r.extract_lower_bound();

        proof {
            lb.lemma_lower_bound(r);
        }

        MonotonicRegisterInner {
            val,
            timestamp,
            resource: Tracked(lb),
        }
    }

    pub fn write(self, val: Option<u64>, timestamp: Timestamp) -> (r: Self)
        requires
            self.resource@@ is FullRightToAdvance,
            self.inv(),
        ensures
            r.inv(),
            r.loc() == self.loc(),
            r.resource@@ is FullRightToAdvance,
            timestamp > self.timestamp ==> r.timestamp == timestamp && r.val == val,
            timestamp <= self.timestamp ==> self == r
    {
        if timestamp > self.timestamp {
            let tracked mut r = self.resource.get();
            proof {
                r.advance(timestamp)
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
        &&& v.resource@@ is FullRightToAdvance
    }
}

pub struct MonotonicRegister {
    inner: RwLock<MonotonicRegisterInner, MonotonicRegisterInv>,

    #[allow(dead_code)]
    resource_loc: Ghost<int>,
}

impl MonotonicRegister {
    // return the register and the lower bound
    pub fn default() -> (r: Self)
        ensures
            r.inv()
    {
        let inner_reg = MonotonicRegisterInner::default();
        let tracked r = inner_reg.resource.borrow();
        let resource_loc = Ghost(r.loc());

        let pred = Ghost(MonotonicRegisterInv { resource_loc });
        assert(<MonotonicRegisterInv as vstd::rwlock::RwLockPredicate<_>>::inv(pred@, inner_reg));
        let inner = RwLock::new(inner_reg, pred);

        MonotonicRegister {
            inner,
            resource_loc,
        }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(&self) -> bool {
        self.inner.pred() == MonotonicRegisterInv { resource_loc: self.resource_loc }
    }

    pub closed spec fn loc(&self) -> Ghost<int> {
        self.resource_loc
    }

    pub fn read(&self) -> (r: MonotonicRegisterInner)
        ensures
            r.resource@@ is LowerBound,
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

    pub fn write(&self, val: Option<u64>, timestamp: Timestamp) -> (r: Tracked<MonotonicTimestampResource>)
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

}
