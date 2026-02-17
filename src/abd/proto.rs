use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

use vstd::prelude::*;

verus! {

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
