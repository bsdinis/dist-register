use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::prelude::*;

verus! {

#[derive(Structural, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp {
    pub seqno: u64,
    pub client_id: u64,
    pub client_ctr: u64,
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialOrdSpecImpl for Timestamp {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.seqno == other.seqno && self.client_id == other.client_id && self.client_ctr
            == other.client_ctr {
            Some(std::cmp::Ordering::Equal)
        } else if self.seqno < other.seqno || (self.seqno == other.seqno && self.client_id
            < other.client_id) || (self.seqno == other.seqno && self.client_id == other.client_id
            && self.client_ctr < other.client_ctr) {
            Some(std::cmp::Ordering::Less)
        } else {
            Some(std::cmp::Ordering::Greater)
        }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::OrdSpecImpl for Timestamp {
    open spec fn obeys_cmp_spec() -> bool {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> std::cmp::Ordering {
        if self.seqno == other.seqno && self.client_id == other.client_id {
            std::cmp::Ordering::Equal
        } else if self.seqno < other.seqno || (self.seqno == other.seqno && self.client_id
            < other.client_id) || (self.seqno == other.seqno && self.client_id == other.client_id
            && self.client_ctr < other.client_ctr) {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Greater
        }
    }
}

impl Timestamp {
    pub fn default() -> (r: Self)
        ensures
            r.seqno == 0,
            r.client_id == 0,
            r.client_ctr == 0,
    {
        Timestamp { seqno: 0, client_id: 0, client_ctr: 0 }
    }

    pub open spec fn spec_default() -> (r: Self) {
        Timestamp { seqno: 0, client_id: 0, client_ctr: 0 }
    }

    pub open spec fn spec_lt(self, other: Self) -> bool {
        ||| self.seqno < other.seqno
        ||| (self.seqno == other.seqno && self.client_id < other.client_id)
        ||| (self.seqno == other.seqno && self.client_id == other.client_id && self.client_ctr
            < other.client_ctr)
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

    pub open spec fn spec_eq(self, other: Self) -> bool {
        &&& self.seqno == other.seqno
        &&& self.client_id == other.client_id
        &&& self.client_ctr == other.client_ctr
    }
}

#[allow(unused)]
#[derive(Debug, Clone, Copy)]
pub enum Request {
    Get,
    GetTimestamp,
    Write { val: Option<u64>, timestamp: Timestamp },
}

pub enum Response {
    Get { val: Option<u64>, timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource> },
    GetTimestamp { timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource> },
    Write { lb: Tracked<MonotonicTimestampResource> },
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Response::Get { val, timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Get { val: *val, timestamp: *timestamp, lb: Tracked(new_lb) }
            },
            Response::GetTimestamp { timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::GetTimestamp { timestamp: *timestamp, lb: Tracked(new_lb) }
            },
            Response::Write { lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Write { lb: Tracked(new_lb) }
            },
        }
    }
}

} // verus!
impl std::fmt::Debug for Response {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Response::Get { val, timestamp, .. } => f
                .debug_struct("Response::Get")
                .field("value", &val)
                .field("timestamp", &timestamp)
                .finish(),
            Response::GetTimestamp { timestamp, .. } => f
                .debug_struct("Response::GetTimestamp")
                .field("timestamp", &timestamp)
                .finish(),
            Response::Write { .. } => f.debug_struct("Response::Write").finish(),
        }
    }
}

impl std::fmt::Debug for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.seqno.fmt(f)?;
        f.write_str(".")?;
        self.client_id.fmt(f)
    }
}
