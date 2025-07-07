use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::rwlock::RwLock;

use crate::abd::proto::Timestamp;
use crate::abd::resource::register::MonotonicRegisterResource;

verus! {

#[cfg(verus_keep_ghost)]
use crate::abd::resource::register::nat_pair_gt;

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

    pub fn lower_bound(&self) -> (r: Tracked<MonotonicRegisterResource>)
        ensures
            r@.loc() == self.loc(),
            r@@ is LowerBound,
            r@@.timestamp() == self.spec_resource()@@.timestamp()
    {
        proof {
            use_type_invariant(&self);
        }
        let tracked resource = self.resource.borrow();
        let tracked lower_bound = resource.extract_lower_bound();

        Tracked(lower_bound)
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
