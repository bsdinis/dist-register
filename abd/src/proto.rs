use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;
use verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

// TODO(qed/proto_lb):
// - add the *sent* lowerbound / token to the request to the *response*
// - add type invariant that orders the lowerbounds on the response

use std::sync::atomic::AtomicU64;

verus! {

exec static REQUEST_TAG: AtomicU64 = AtomicU64::new(0);

#[allow(unused)]
#[derive(Debug)]
pub enum Request {
    Get(GetRequest),
    GetTimestamp(GetTimestampRequest),
    Write(WriteRequest),
}

impl TaggedMessage for Request {
    fn tag(&self) -> u64 {
        match self {
            Request::Get(req) => req.tag(),
            Request::GetTimestamp(req) => req.tag(),
            Request::Write(req) => req.tag(),
        }
    }

    open spec fn spec_tag(self) -> u64 {
        match self {
            Request::Get(req) => req.spec_tag(),
            Request::GetTimestamp(req) => req.spec_tag(),
            Request::Write(req) => req.spec_tag(),
        }
    }
}

#[allow(unused)]
pub struct GetRequest {
    request_id: u64,
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct GetTimestampRequest {
    request_id: u64,
    servers: Tracked<ServerUniverse>,
}

#[allow(unused)]
pub struct WriteRequest {
    request_id: u64,
    value: Option<u64>,
    timestamp: Timestamp,
    commitment: Tracked<
        WriteCommitment,
    >,
    // TODO(qed/read/proto): add lower bound to write request
}

#[allow(unused)]
impl GetRequest {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub fn new(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.servers() == servers@,
    {
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        GetRequest { request_id, servers }
    }

    pub fn server_lower_bound(&mut self, server_id: Ghost<u64>) -> (r: Tracked<
        MonotonicTimestampResource,
    >)
        requires
            old(self).servers().contains_key(server_id@),
        ensures
            old(self).spec_tag() == self.spec_tag(),
            self.servers().locs() == old(self).servers().locs(),
            forall|id| #[trigger]
                self.servers().contains_key(id) ==> {
                    &&& self.servers()[id]@.loc() == old(self).servers()[id]@.loc()
                    &&& self.servers()[id]@@.timestamp() == old(self).servers()[id]@@.timestamp()
                },
            r@.loc() == self.servers()[server_id@]@.loc(),
            r@@.timestamp() == self.servers()[server_id@]@@.timestamp(),
            r@@ is LowerBound,
    {
        let tracked new_lb;
        proof {
            use_type_invariant(&*self);

            let ghost old_servers = self.servers@;

            let tracked lb = self.servers.borrow_mut().tracked_remove_lb(server_id@);
            let ghost unchanged_servers = self.servers@;

            new_lb = lb.extract_lower_bound();
            self.servers.borrow_mut().tracked_insert_lb(server_id@, lb);

            assert forall|id| #[trigger] self.servers@.contains_key(id) implies {
                &&& self.servers@[id]@.loc() == old_servers[id]@.loc()
                &&& self.servers@[id]@@.timestamp() == old_servers[id]@@.timestamp()
            } by {
                if id != server_id@ {
                    assert(unchanged_servers.contains_key(id));  // TRIGGER
                }
            }
        }

        Tracked(new_lb)
    }
}

impl TaggedMessage for GetRequest {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for GetRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
        }
        GetRequest { request_id: self.request_id, servers: Tracked(new_servers) }
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
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        GetTimestampRequest { request_id, servers }
    }
}

impl TaggedMessage for GetTimestampRequest {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for GetTimestampRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
        }
        GetTimestampRequest { request_id: self.request_id, servers: Tracked(new_servers) }
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
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        WriteRequest { request_id, value, timestamp, commitment }
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

impl TaggedMessage for WriteRequest {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for WriteRequest {
    fn clone(&self) -> (r: Self) {
        let tracked new_commitment;
        proof {
            use_type_invariant(self);
            new_commitment = self.commitment.borrow().duplicate()
        }
        WriteRequest {
            request_id: self.request_id,
            value: self.value.clone(),
            timestamp: self.timestamp.clone(),
            commitment: Tracked(new_commitment),
        }
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

impl TaggedMessage for Response {
    fn tag(&self) -> u64 {
        match self {
            Response::Get(resp) => resp.tag(),
            Response::GetTimestamp(resp) => resp.tag(),
            Response::Write(resp) => resp.tag(),
        }
    }

    open spec fn spec_tag(self) -> u64 {
        match self {
            Response::Get(resp) => resp.spec_tag(),
            Response::GetTimestamp(resp) => resp.spec_tag(),
            Response::Write(resp) => resp.spec_tag(),
        }
    }
}

#[allow(unused)]
pub struct GetResponse {
    request_id: u64,
    value: Option<u64>,
    timestamp: Timestamp,
    lb: Tracked<MonotonicTimestampResource>,
    commitment: Tracked<WriteCommitment>,
    server_token: Tracked<
        ServerToken,
    >,
    // TODO(qed/read/phase_1): return the lower bound that originated from it
}

#[allow(unused)]
pub struct GetTimestampResponse {
    request_id: u64,
    timestamp: Timestamp,
    lb: Tracked<MonotonicTimestampResource>,
}

#[allow(unused)]
pub struct WriteResponse {
    request_id: u64,
    lb: Tracked<MonotonicTimestampResource>,
    // TODO(qed/read/phase_2):
    //  - return the ghost request that was sent in the request to tie down the lb here
}

#[allow(unused)]
impl GetResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@.loc() == self.server_token@.value()
        &&& self.lb@@.timestamp() == self.timestamp
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value()
            == self.value
        // Q: need to tie the server_token to the global invariant (by the id)
        // Q: need to tie the server_token.key() to the server this came from

    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.value
    }

    pub closed spec fn spec_commitment(self) -> WriteCommitment {
        self.commitment@
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.server_token@.id()
    }

    pub closed spec fn server_id(self) -> u64 {
        self.server_token@.key()
    }

    pub open spec fn loc(self) -> Loc {
        self.lb().loc()
    }

    pub fn new(
        request_id: u64,
        value: Option<u64>,
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
        commitment: Tracked<WriteCommitment>,
        server_token: Tracked<ServerToken>,
    ) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@.loc() == server_token@.value(),
            lb@@.timestamp() == timestamp,
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.spec_tag() == request_id,
            r.lb().loc() == lb@.loc(),
            r.lb()@.timestamp() == lb@@.timestamp(),
            r.spec_timestamp() == timestamp,
            r.spec_value() == value,
            r.spec_commitment() == commitment@,
            r.server_id() == server_token@.key(),
            r.loc() == server_token@.value(),
    {
        GetResponse { request_id, value, timestamp, lb, commitment, server_token }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp(),
        no_unwind
    {
        self.timestamp
    }

    pub fn value(&self) -> (value: &Option<u64>)
        ensures
            *value == self.spec_value(),
        no_unwind
    {
        &self.value
    }

    pub fn into_inner(self) -> (r: (Option<u64>, Timestamp))
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
    {
        (self.value, self.timestamp)
    }

    pub fn duplicate_lb(&self) -> (r: Tracked<MonotonicTimestampResource>)
        ensures
            r@.loc() == self.lb().loc(),
            r@@.timestamp() == self.lb()@.timestamp(),
            r@@ is LowerBound,
        no_unwind
    {
        let tracked lb;
        proof {
            use_type_invariant(self);
            lb = self.lb.borrow().extract_lower_bound();
        }
        Tracked(lb)
    }

    pub fn commitment(&self) -> (r: Tracked<WriteCommitment>)
        ensures
            r@.id() == self.spec_commitment().id(),
            r@.key() == self.spec_timestamp(),
            r@.value() == self.spec_value(),
        no_unwind
    {
        let tracked commitment;
        proof {
            use_type_invariant(self);
            commitment = self.commitment.borrow().duplicate();
        }
        Tracked(commitment)
    }

    pub fn lemma_get_response(&self)
        ensures
            self.lb()@ is LowerBound,
            self.spec_timestamp() == self.lb()@.timestamp(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
        }
    }

    pub fn lemma_token_agree(&self, server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>)
        requires
            self.server_token_id() == old(server_tokens)@.id(),
        ensures
            server_tokens@.id() == old(server_tokens)@.id(),
            server_tokens@@ == old(server_tokens)@@,
            server_tokens@@.contains_key(self.server_id()) ==> server_tokens@@[self.server_id()]
                == self.loc(),
        no_unwind
    {
        proof {
            use_type_invariant(self);
            server_tokens.borrow_mut().intersection_agrees_points_to(self.server_token.borrow());
        }
    }
}

impl TaggedMessage for GetResponse {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for GetResponse {
    fn clone(&self) -> (r: Self) {
        let tracked lb;
        let tracked commitment;
        let tracked server_token;
        proof {
            use_type_invariant(self);
            lb = self.lb.borrow().extract_lower_bound();
            commitment = self.commitment.borrow().duplicate();
            server_token = self.server_token.borrow().duplicate();
        }
        GetResponse::new(
            self.request_id,
            self.value.clone(),
            self.timestamp.clone(),
            Tracked(lb),
            Tracked(commitment),
            Tracked(server_token),
        )
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

    pub fn new(
        request_id: u64,
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
    ) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@@.timestamp() == timestamp,
        ensures
            r.spec_tag() == request_id,
            r.lb() == lb@,
            r.spec_timestamp() == timestamp,
    {
        GetTimestampResponse { request_id, timestamp, lb }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp(),
    {
        self.timestamp.clone()
    }
}

impl TaggedMessage for GetTimestampResponse {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for GetTimestampResponse {
    fn clone(&self) -> (r: Self) {
        let tracked new_lb;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
        }
        GetTimestampResponse::new(self.request_id, self.timestamp.clone(), Tracked(new_lb))
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

    pub fn new(request_id: u64, lb: Tracked<MonotonicTimestampResource>) -> (r: Self)
        requires
            lb@@ is LowerBound,
        ensures
            r.spec_tag() == request_id,
            r.lb() == lb@,
            r.spec_timestamp() == lb@@.timestamp(),
    {
        WriteResponse { request_id, lb }
    }
}

impl TaggedMessage for WriteResponse {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Clone for WriteResponse {
    fn clone(&self) -> (r: Self) {
        let tracked new_lb;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
        }
        WriteResponse::new(self.request_id, Tracked(new_lb))
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
            .field("value", &self.value)
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
