use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
#[cfg(verus_only)]
use crate::proto::fake_request_proof;
use crate::proto::get::GetRequest;
use crate::proto::get_timestamp::GetTimestampRequest;
use crate::proto::write::WriteRequest;
use crate::proto::ReqType;
use crate::proto::RequestProof;
use crate::timestamp::Timestamp;

use verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

use std::sync::atomic::AtomicU64;

verus! {

exec static REQUEST_TAG: AtomicU64 = AtomicU64::new(0);

pub struct Request {
    request_id: u64,
    inner: RequestInner,
    request: Tracked<RequestProof>,
}

pub enum RequestInner {
    Get(GetRequest),
    GetTimestamp(GetTimestampRequest),
    Write(WriteRequest),
}

impl TaggedMessage for Request {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Request {
    pub closed spec fn request_id(self) -> Loc {
        self.request.id()
    }

    pub closed spec fn request_key(self) -> (u64, u64) {
        self.request@.key()
    }

    pub closed spec fn request(self) -> RequestInner {
        self.request@.value()
    }

    pub closed spec fn req_type(self) -> ReqType {
        match self.inner {
            RequestInner::Get(_) => ReqType::Get,
            RequestInner::GetTimestamp(_) => ReqType::GetTimestamp,
            RequestInner::Write(_) => ReqType::Write,
        }
    }

    pub closed spec fn get(self) -> GetRequest
        recommends
            self.req_type() is Get,
    {
        self.inner->Get_0
    }

    pub closed spec fn get_timestamp(self) -> GetTimestampRequest
        recommends
            self.req_type() is GetTimestamp,
    {
        self.inner->GetTimestamp_0
    }

    pub closed spec fn write(self) -> WriteRequest
        recommends
            self.req_type() is Write,
    {
        self.inner->Write_0
    }

    pub closed spec fn client_id(self) -> u64 {
        self.request@.key().0
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request@.key().1 == self.request_id
        &&& self.request@.value().spec_eq(self.inner)
    }

    // TODO: require submaps
    pub fn new_get(client_id: u64, servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.req_type() is Get,
            r.request_key() == (client_id, r.spec_tag()),
            r.client_id() == client_id,
            ({
                let req = r.get();
                req.servers() == servers@
            }),
    {
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let inner = RequestInner::Get(GetRequest::new(servers));
        let request = Tracked(fake_request_proof((client_id, request_id), inner));
        Request { request_id, inner, request }
    }

    pub fn new_get_timestamp(client_id: u64, servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.req_type() is GetTimestamp,
            r.request_key() == (client_id, r.spec_tag()),
            r.client_id() == client_id,
            ({
                let req = r.get_timestamp();
                req.servers() == servers@
            }),
    {
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let inner = RequestInner::GetTimestamp(GetTimestampRequest::new(servers));
        let request = Tracked(fake_request_proof((client_id, request_id), inner));
        Request { request_id, inner, request }
    }

    pub fn new_write(
        client_id: u64,
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
    ) -> (r: Self)
        requires
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.req_type() is Write,
            r.request_key() == (client_id, r.spec_tag()),
            r.client_id() == client_id,
            ({
                let req = r.write();
                &&& req.spec_timestamp() == timestamp
                &&& req.spec_value() == value
            }),
    {
        let request_id = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let inner = RequestInner::Write(WriteRequest::new(value, timestamp, commitment));
        let request = Tracked(fake_request_proof((client_id, request_id), inner));
        Request { request_id, inner, request }
    }

    pub fn destruct(self) -> (r: (u64, RequestInner, Tracked<RequestProof>))
        ensures
            r.0 == self.spec_tag(),
            r.2@.value().spec_eq(r.1),
            r.2@.id() == self.request_id(),
            r.2@.value() == self.request(),
            r.2@.key() == self.request_key(),
            r.2@.key() == (self.client_id(), self.spec_tag()),
            r.1 is Get <==> self.req_type() is Get,
            r.1 is GetTimestamp <==> self.req_type() is GetTimestamp,
            r.1 is Write <==> self.req_type() is Write,
        no_unwind
    {
        proof {
            use_type_invariant(&self);
        }
        (self.request_id, self.inner, self.request)
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.request_id == other.request_id
        &&& self.inner.spec_eq(other.inner)
        &&& self.request@.id() == other.request@.id()
        &&& self.request@@ == other.request@@
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        RequestInner::spec_eq_refl(a.inner);
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        RequestInner::spec_eq_symm(a.inner, b.inner);
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        RequestInner::spec_eq_trans(a.inner, b.inner, c.inner);
    }
}

impl RequestInner {
    pub open spec fn spec_eq(self, other: Self) -> bool {
        match (self, other) {
            (RequestInner::Get(a), RequestInner::Get(b)) => a.spec_eq(b),
            (RequestInner::GetTimestamp(a), RequestInner::GetTimestamp(b)) => a.spec_eq(b),
            (RequestInner::Write(a), RequestInner::Write(b)) => a.spec_eq(b),
            (_, _) => false,
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            RequestInner::Get(a) => {
                assume(a.inv());  // TODO(verus): limitation around spec values and type invariants
                GetRequest::spec_eq_refl(a)
            },
            RequestInner::GetTimestamp(a) => {
                assume(a.inv());  // TODO(verus): limitation around spec values and type invariants
                GetTimestampRequest::spec_eq_refl(a)
            },
            RequestInner::Write(a) => WriteRequest::spec_eq_refl(a),
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (RequestInner::Get(a), RequestInner::Get(b)) => GetRequest::spec_eq_symm(a, b),
            (
                RequestInner::GetTimestamp(a),
                RequestInner::GetTimestamp(b),
            ) => GetTimestampRequest::spec_eq_symm(a, b),
            (RequestInner::Write(a), RequestInner::Write(b)) => WriteRequest::spec_eq_symm(a, b),
            (_, _) => {},
        }
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        match (a, b, c) {
            (
                RequestInner::Get(a),
                RequestInner::Get(b),
                RequestInner::Get(c),
            ) => GetRequest::spec_eq_trans(a, b, c),
            (
                RequestInner::GetTimestamp(a),
                RequestInner::GetTimestamp(b),
                RequestInner::GetTimestamp(c),
            ) => GetTimestampRequest::spec_eq_trans(a, b, c),
            (
                RequestInner::Write(a),
                RequestInner::Write(b),
                RequestInner::Write(c),
            ) => WriteRequest::spec_eq_trans(a, b, c),
            (_, _, _) => {},
        }
    }
}

impl Clone for Request {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        broadcast use RequestInner::spec_eq_trans;
        broadcast use RequestInner::spec_eq_symm;

        proof {
            use_type_invariant(self);
        }
        let inner = self.inner.clone();
        assert(inner.spec_eq(self.inner));
        assert(self.request@.value().spec_eq(self.inner));
        assert(self.request@.value().spec_eq(inner));
        let request = Tracked(self.request.borrow().duplicate());
        Request { request_id: self.request_id, inner, request }
    }
}

impl Clone for RequestInner {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        match self {
            RequestInner::Get(get) => { RequestInner::Get(get.clone()) },
            RequestInner::GetTimestamp(get_ts) => { RequestInner::GetTimestamp(get_ts.clone()) },
            RequestInner::Write(write) => { RequestInner::Write(write.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for RequestInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RequestInner::Get(get) => f.debug_tuple("Get").field(&get).finish(),
            RequestInner::GetTimestamp(get_ts) => {
                f.debug_tuple("GetTimestamp").field(&get_ts).finish()
            }
            RequestInner::Write(write) => f.debug_tuple("Write").field(&write).finish(),
        }
    }
}

impl std::fmt::Debug for Request {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Request")
            .field("request_id", &self.request_id)
            .field("request", &self.inner)
            .finish()
    }
}
