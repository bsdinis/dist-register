use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

use vstd::prelude::*;

verus! {

#[allow(unused)]
#[derive(Debug)]
pub enum Request {
    Get(GetRequest),
    GetTimestamp,
    Write { val: Option<u64>, timestamp: Timestamp },
}

#[allow(unused)]
pub struct GetRequest {
    servers: Tracked<ServerUniverse>,
}

pub enum Response {
    Get { val: Option<u64>, timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource> },
    GetTimestamp { timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource> },
    Write { lb: Tracked<MonotonicTimestampResource> },
}

#[allow(unused)]
impl GetRequest {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.servers@.inv()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub fn new(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
        ensures
            r.servers() == servers@,
    {
        GetRequest { servers }
    }
}

impl Clone for GetRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
        }
        GetRequest::new(Tracked(new_servers))
    }
}

impl Clone for Request {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Request::Get(get) => { Request::Get(get.clone()) },
            Request::GetTimestamp => { Request::GetTimestamp },
            Request::Write { val, timestamp } => {
                Request::Write { val: val.clone(), timestamp: timestamp.clone() }
            },
        }
    }
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
impl std::fmt::Debug for GetRequest {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
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
