use crate::abd::resource::register::MonotonicRegisterResource;

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp {
    pub seqno: u64,
    pub client_id: u64,
}

impl Timestamp {
    pub fn default() -> (r: Self)
        ensures
            r.seqno == 0,
            r.client_id == 0
    {
        Timestamp { seqno: 0, client_id: 0 }
    }

    pub open spec fn to_nat(&self) -> (nat, nat) {
        (self.seqno as nat, self.client_id as nat)
    }

    pub open spec fn lt(&self, other: &Self) -> bool  {
        self.seqno < other.seqno || (self.seqno == other.seqno && self.client_id < other.client_id)
    }

    pub open spec fn le(&self, other: &Self) -> bool  {
        self.lt(other) || self == other
    }

    pub open spec fn gt(&self, other: &Self) -> bool  {
        !self.le(other)
    }

    pub open spec fn ge(&self, other: &Self) -> bool  {
        !self.lt(other)
    }
}

// TODO: add type invariant
#[derive(Debug, Clone, Copy)]
pub enum Request {
    Get,
    GetTimestamp,
    Write {
        val: Option<u64>,
        timestamp: Timestamp,
    },
}

// TODO: add type invariant
pub enum Response {
    Get {
        val: Option<u64>,
        timestamp: Timestamp,
        lb: Tracked<MonotonicRegisterResource>
    },
    GetTimestamp {
        timestamp: Timestamp,
        lb: Tracked<MonotonicRegisterResource>,
    },
    Write {
        lb: Tracked<MonotonicRegisterResource>,
    },
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Response::Get { val, timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Get {
                    val: val.clone(),
                    timestamp: timestamp.clone(),
                    lb: Tracked(new_lb),
                }
            },
            Response::GetTimestamp { timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::GetTimestamp {
                    timestamp: timestamp.clone(),
                    lb: Tracked(new_lb),
                }
            },
            Response::Write { lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Write {
                    lb: Tracked(new_lb),
                }
            },
        }
    }
}

}

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
