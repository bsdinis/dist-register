use crate::abd::invariants::committed_to::WriteCommitment;
use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

#[allow(unused)]
#[derive(Debug)]
pub enum Request {
    Get(GetRequest),
    GetTimestamp(GetTimestampRequest),
    Write(WriteRequest),
}

#[allow(unused)]
pub struct GetRequest {
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct GetTimestampRequest {
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct WriteRequest {
    value: Option<u64>,
    timestamp: Timestamp,
    commitment: Tracked<WriteCommitment>,
    // TODO: add lower bound
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
impl GetTimestampRequest {
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
        GetTimestampRequest { servers }
    }
}

impl Clone for GetTimestampRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
        }
        GetTimestampRequest::new(Tracked(new_servers))
    }
}

#[allow(unused)]
impl WriteRequest {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value() == self.value
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.value
    }

    pub fn new(
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
    ) -> (r: Self)
        requires
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.spec_timestamp() == timestamp,
            r.spec_value() == value,
    {
        WriteRequest { value, timestamp, commitment }
    }

    pub fn destruct(self) -> (r: (Option<u64>, Timestamp, Tracked<WriteCommitment>))
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
            r.2@.key() == self.spec_timestamp(),
            r.2@.value() == self.spec_value(),
    {
        proof {
            use_type_invariant(&self);
        }

        (self.value, self.timestamp, self.commitment)
    }
}

impl Clone for WriteRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_commitment;
        proof {
            use_type_invariant(self);
            new_commitment = self.commitment.borrow().duplicate()
        }
        WriteRequest::new(self.value.clone(), self.timestamp.clone(), Tracked(new_commitment))
    }
}

impl Clone for Request {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Request::Get(get) => { Request::Get(get.clone()) },
            Request::GetTimestamp(get_ts) => { Request::GetTimestamp(get_ts.clone()) },
            Request::Write(write) => { Request::Write(write.clone()) },
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

#[allow(unused)]
pub struct WriteResponse {
    // TODO: there is no exec state that ties this together
    lb: Tracked<MonotonicTimestampResource>,
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

    pub open spec fn loc(self) -> Loc {
        self.lb().loc()
    }

    pub fn new(
        val: Option<u64>,
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
    ) -> (r: Self)
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
            ts == self.spec_timestamp(),
    {
        self.timestamp.clone()
    }

    pub fn value(&self) -> (value: &Option<u64>)
        ensures
            *value == self.spec_value(),
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

    pub open spec fn loc(self) -> Loc {
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
            ts == self.spec_timestamp(),
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
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.lb@@.timestamp()
    }

    pub open spec fn loc(self) -> Loc {
        self.lb().loc()
    }

    pub fn new(lb: Tracked<MonotonicTimestampResource>) -> (r: Self)
        requires
            lb@@ is LowerBound,
        ensures
            r.lb() == lb@,
            r.spec_timestamp() == lb@@.timestamp(),
    {
        WriteResponse { lb  }
    }
}

impl Clone for WriteResponse {
    fn clone(&self) -> (r: Self) {
        let tracked new_lb;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
        }
        WriteResponse::new(Tracked(new_lb))
    }
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> Self {
        match self {
            Response::Get(get) => { Response::Get(get.clone()) },
            Response::GetTimestamp(get_ts) => { Response::GetTimestamp(get_ts.clone()) },
            Response::Write(write) => { Response::Write(write.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for GetRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetRequest").finish()
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

impl std::fmt::Debug for GetTimestampRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampRequest").finish()
    }
}

impl std::fmt::Debug for GetTimestampResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampResponse")
            .field("timestamp", &self.timestamp)
            .finish()
    }
}

impl std::fmt::Debug for WriteRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteRequest")
            .field("value", &self.value)
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
