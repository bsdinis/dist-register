use crate::abd::min::MinOrd;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::OrdSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialOrdSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::default::DefaultSpec;

use vstd::prelude::*;

verus! {

#[derive(Structural, PartialEq)]
pub struct Timestamp<Id> {
    pub seqno: u64,
    pub client_id: Id,
    pub client_ctr: u64,
}

impl<Id: Default> Default for Timestamp<Id> {
    fn default() -> Self {
        Timestamp { seqno: 0, client_id: Id::default(), client_ctr: 0 }
    }
}
impl<Id: Clone> Clone for Timestamp<Id> {
    fn clone(&self) -> Self {
        Timestamp { seqno: self.seqno, client_id: self.client_id.clone(), client_ctr: self.client_ctr }
    }
}
impl<Id: Copy> Copy for Timestamp<Id> {}
impl<Id: Eq> Eq for Timestamp<Id> {}
impl<Id: PartialOrd> PartialOrd for Timestamp<Id> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        proof { admit(); } // TODO(id)
        if self.seqno.partial_cmp(&other.seqno) != Some(std::cmp::Ordering::Equal) {
            self.seqno.partial_cmp(&other.seqno)
        } else if self.client_id.partial_cmp(&other.client_id) != Some(std::cmp::Ordering::Equal) {
            self.client_id.partial_cmp(&other.client_id)
        } else {
            self.client_ctr.partial_cmp(&other.client_ctr)
        }
    }
}
impl<Id: Ord> Ord for Timestamp<Id> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        proof { admit(); } // TODO(id)
        if self.seqno.cmp(&other.seqno) != std::cmp::Ordering::Equal {
            self.seqno.cmp(&other.seqno)
        } else if self.client_id.cmp(&other.client_id) != std::cmp::Ordering::Equal {
            self.client_id.cmp(&other.client_id)
        } else {
            self.client_ctr.cmp(&other.client_ctr)
        }
    }
}

#[cfg(verus_keep_ghost)]
impl<Id: PartialOrdSpec> vstd::std_specs::cmp::PartialOrdSpecImpl for Timestamp<Id>
{
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if PartialOrdSpec::partial_cmp_spec(&self.seqno, &other.seqno) != Some(std::cmp::Ordering::Equal) {
            PartialOrdSpec::partial_cmp_spec(&self.seqno, &other.seqno)
        } else if PartialOrdSpec::partial_cmp_spec(&self.client_id, &other.client_id) != Some(std::cmp::Ordering::Equal) {
            PartialOrdSpec::partial_cmp_spec(&self.client_id, &other.client_id)
        } else {
            PartialOrdSpec::partial_cmp_spec(&self.client_ctr, &other.client_ctr)
        }
    }
}

#[cfg(verus_keep_ghost)]
impl<Id: OrdSpec> vstd::std_specs::cmp::OrdSpecImpl for Timestamp<Id> {
    open spec fn obeys_cmp_spec() -> bool {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> std::cmp::Ordering {
        if OrdSpec::cmp_spec(&self.seqno, &other.seqno) != std::cmp::Ordering::Equal {
            OrdSpec::cmp_spec(&self.seqno, &other.seqno)
        } else if OrdSpec::cmp_spec(&self.client_id, &other.client_id) != std::cmp::Ordering::Equal {
            OrdSpec::cmp_spec(&self.client_id, &other.client_id)
        } else {
            OrdSpec::cmp_spec(&self.client_ctr, &other.client_ctr)
        }
    }
}

#[cfg(verus_keep_ghost)]
impl<Id: DefaultSpec> vstd::std_specs::default::DefaultSpecImpl for Timestamp<Id> {
    open spec fn obeys_default_spec() -> bool {
        true
    }

    open spec fn default_spec() -> Self {
        Timestamp {
            seqno: 0,
            client_id: Id::default_spec(),
            client_ctr: 0,
        }
    }
}

impl<Id: MinOrd> Timestamp<Id> {
    pub open spec fn spec_lt(self, other: Self) -> bool {
        ||| self.seqno < other.seqno
        ||| (self.seqno == other.seqno && Id::lt(&self.client_id, &other.client_id))
        ||| (self.seqno == other.seqno && Id::eq(&self.client_id, &other.client_id) && self.client_ctr < other.client_ctr)
    }

    pub open spec fn spec_le(self, other: Self) -> bool {
        self < other || self == other
    }

    pub open spec fn spec_gt(self, other: Self) -> bool {
        !(self <= other)
    }

    pub open spec fn spec_ge(self, other: Self) -> bool {
        !(self < other)
    }
}

impl<Id> Timestamp<Id>
    where Id: Eq
{
    spec fn spec_eq(self, other: Self) -> bool {
        &&& self.seqno == other.seqno
        &&& self.client_id == other.client_id
        &&& self.client_ctr == other.client_ctr
    }
}

impl<Id: MinOrd> MinOrd for Timestamp<Id> {
    fn minimum() -> Self {
        Timestamp { seqno: 0, client_id: Id::minimum(), client_ctr: 0 }
    }

    open spec fn spec_minimum() -> Self {
        Timestamp { seqno: 0, client_id: Id::spec_minimum(), client_ctr: 0 }
    }

    proof fn minimum_is_least() {}
}

mod laws {

#[cfg(verus_keep_ghost)]
use super::*;

#[cfg(verus_keep_ghost)]
use vstd::laws_cmp::*;
#[cfg(verus_keep_ghost)]
use vstd::laws_eq::*;

pub broadcast proof fn lemma_timestamp_obeys_eq_spec<Id: Ord>()
    // requires
        // obeys_eq_spec::<Id>(),
    ensures
        #[trigger] obeys_eq_spec::<Timestamp<Id>>(),
{
    reveal(obeys_eq_spec_properties);
    admit(); // TODO(id)
}

pub broadcast proof fn lemma_timestamp_obeys_concrete_eq<Id: Ord>()
    // requires
        // obeys_concrete_eq::<Id>(),
    ensures
        #[trigger] obeys_concrete_eq::<Timestamp<Id>>(),
{
    reveal(obeys_concrete_eq);
    admit(); // TODO(id)
}


pub broadcast proof fn lemma_timestamp_obeys_cmp_spec<Id: Ord>()
    // requires
        // obeys_cmp_spec::<Id>()
    ensures
        #[trigger] obeys_cmp_spec::<Timestamp<Id>>()
{
    broadcast use lemma_timestamp_obeys_eq_spec;
    broadcast use lemma_timestamp_obeys_concrete_eq;
    reveal(obeys_eq_spec_properties);
    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    admit(); // TODO(id)
    assert(obeys_eq_spec::<Timestamp<Id>>());
}

pub broadcast group timestamp_cmp_laws {
    lemma_timestamp_obeys_eq_spec,
    lemma_timestamp_obeys_concrete_eq,
    lemma_timestamp_obeys_cmp_spec
}

}

#[cfg(verus_keep_ghost)]
pub use laws::*;

} // verus!

impl<Id: std::fmt::Debug> std::fmt::Debug for Timestamp<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.seqno.fmt(f)?;
        f.write_str(".")?;
        self.client_id.fmt(f)
    }
}

impl<Id: std::hash::Hash> std::hash::Hash for Timestamp<Id> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.seqno.hash(state);
        self.client_id.hash(state);
        self.client_ctr.hash(state);
    }
}
