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

pub enum Response {
    Get(GetResponse),
    GetTimestamp(GetTimestampResponse),
    Write(WriteResponse),
}

#[allow(unused)]
pub struct GetResponse {
    val: Option<u64>,
    timestamp: Timestamp,
    lb: Tracked<MonotonicTimestampResource>,
    // TODO: commitment
}

#[allow(unused)]
pub struct GetTimestampResponse {
    timestamp: Timestamp,
    lb: Tracked<MonotonicTimestampResource>,
}

    // TODO: what do we actually send?
#[allow(unused)]
pub struct WriteResponse;


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
#[allow(unused)]
impl GetTimestampResponse {
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

    pub open spec fn loc(self) -> int {
        self.lb().loc()
    }

    pub fn new(timestamp: Timestamp, lb: Tracked<MonotonicTimestampResource>) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@@.timestamp() == timestamp,
        ensures
            r.lb() == lb@,
            r.spec_timestamp() == timestamp,
    {
        GetTimestampResponse { timestamp, lb }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp()
    {
        self.timestamp.clone()
    }
}

impl Clone for GetTimestampResponse {
    fn clone(&self) -> (r: Self) {
        let tracked new_lb;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
        }
        GetTimestampResponse::new(self.timestamp.clone(), Tracked(new_lb))
    }
}


#[allow(unused)]
impl WriteResponse {
    // #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        true
    }


    pub fn new() -> (r: Self)
    {
        WriteResponse
    }
}

impl Clone for WriteResponse {
    fn clone(&self) -> (r: Self) {
        WriteResponse
    }
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Response::Get(get) => {
                Response::Get(get.clone())
            },
            Response::GetTimestamp(get_ts) => {
                Response::GetTimestamp(get_ts.clone())
            },
            Response::Write(write) => {
                Response::Write(write.clone())
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

impl std::fmt::Debug for GetTimestampResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampResponse")
            .field("timestamp", &self.timestamp)
            .finish()
    }
}

impl std::fmt::Debug for WriteResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteResponse").finish()
    }
}

impl std::fmt::Debug for Response {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Response::Get(get) => f.debug_tuple("Response::Get").field(&get).finish(),
            Response::GetTimestamp(get_ts) => f
                .debug_tuple("Response::GetTimestamp")
                .field(&get_ts)
                .finish(),
            Response::Write(write) => f.debug_tuple("Response::Write").field(&write).finish(),
        }
    }
}
