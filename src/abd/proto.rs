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
    Get(GetResponse),
    GetTimestamp { timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource> },
    Write { lb: Tracked<MonotonicTimestampResource> },
}

#[allow(unused)]
pub struct GetResponse {
    val: Option<u64>,
    timestamp: Timestamp,
    lb: Tracked<MonotonicTimestampResource>,
    // TODO: commitment
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

#[allow(unused)]
impl GetResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@@.timestamp() == self.timestamp
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.val
    }

    pub open spec fn loc(self) -> int {
        self.lb().loc()
    }

    pub fn new(val: Option<u64>, timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource>) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@@.timestamp() == timestamp,
        ensures
            r.lb() == lb@,
            r.spec_timestamp() == timestamp,
            r.spec_value() == val,
    {
        GetResponse { val, timestamp, lb }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp()
    {
        self.timestamp.clone()
    }

    pub fn value(&self) -> (value: &Option<u64>)
        ensures
            *value == self.spec_value()
    {
        &self.val
    }

    pub fn into_inner(self) -> (r: (Option<u64>, Timestamp))
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
    {
        (self.val, self.timestamp)
    }
}

impl Clone for GetResponse {
    fn clone(&self) -> (r: Self) {
        let tracked new_lb;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
        }
        GetResponse::new(self.val.clone(), self.timestamp.clone(), Tracked(new_lb))
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
            Response::Get(get) => {
                Response::Get(get.clone())
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

impl std::fmt::Debug for GetResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetResponse")
            .field("value", &self.val)
            .field("timestamp", &self.timestamp)
            .finish()
    }
}

impl std::fmt::Debug for Response {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Response::Get(get) => f.debug_tuple("Response::Get").field(&get).finish(),
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
