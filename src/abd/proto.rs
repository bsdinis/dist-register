#[cfg(verus_keep_ghost)]
use crate::abd::min::MinOrd;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

use vstd::prelude::*;

verus! {

pub enum Request<Id> {
    Get,
    GetTimestamp,
    Write { val: Option<u64>, timestamp: Timestamp<Id> },
}

impl<Id: Clone> Clone for Request<Id> {
    fn clone(&self) -> Self {
        match self {
            Request::Get => Request::Get,
            Request::GetTimestamp => Request::GetTimestamp,
            Request::Write { val, timestamp } => {
                Request::Write { val: val.clone(), timestamp: timestamp.clone() }
            },
        }
    }
}
impl<Id: Copy> Copy for Request<Id> {}

pub enum Response<Id>
{
    Get { val: Option<u64>, timestamp: Timestamp<Id>, lb: Tracked<MonotonicTimestampResource<Id>> },
    GetTimestamp { timestamp: Timestamp<Id>, lb: Tracked<MonotonicTimestampResource<Id>> },
    Write { lb: Tracked<MonotonicTimestampResource<Id>> },
}

#[cfg(verus_keep_ghost)]
impl<Id: Clone + MinOrd> Clone for Response<Id> {
    #[allow(unused)]
    fn clone(&self) -> Self {
        match self {
            Response::Get { val, timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Get { val: *val, timestamp: timestamp.clone(), lb: Tracked(new_lb) }
            },
            Response::GetTimestamp { timestamp, lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::GetTimestamp { timestamp: timestamp.clone(), lb: Tracked(new_lb) }
            },
            Response::Write { lb } => {
                let tracked new_lb = lb.borrow().extract_lower_bound();
                Response::Write { lb: Tracked(new_lb) }
            },
        }
    }
}

} // verus!

impl<Id: std::fmt::Debug> std::fmt::Debug for Request<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Request::Get => f.debug_struct("Request::Get").finish(),
            Request::GetTimestamp => f.debug_struct("Request::GetTimestamp").finish(),
            Request::Write { val, timestamp } => f
                .debug_struct("Request::Write")
                .field("value", &val)
                .field("timestamp", &timestamp)
                .finish(),
        }
    }
}
impl<Id: std::fmt::Debug> std::fmt::Debug for Response<Id> {
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
