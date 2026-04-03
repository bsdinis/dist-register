use crate::invariants::requests::RequestProof;
use crate::proto::get::GetResponse;
use crate::proto::get_timestamp::GetTimestampResponse;
#[cfg(verus_only)]
use crate::proto::request::RequestInner;
use crate::proto::write::WriteResponse;
#[cfg(verus_only)]
use crate::proto::ReqType;

use verdist::rpc::proto::TaggedMessage;

use vstd::pervasive::unreached;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct Response {
    request_id: u64,
    inner: ResponseInner,
    request: Tracked<RequestProof>,
}

pub enum ResponseInner {
    Get(GetResponse),
    GetTimestamp(GetTimestampResponse),
    Write(WriteResponse),
}

impl TaggedMessage for Response {
    fn tag(&self) -> u64 {
        self.request_id
    }

    closed spec fn spec_tag(self) -> u64 {
        self.request_id
    }
}

impl Response {
    pub fn new(request_id: u64, inner: ResponseInner, request: Tracked<RequestProof>) -> (r: Self)
        requires
            request@.key().1 == request_id,
            request@.value() is Get <==> inner is Get,
            request@.value() is GetTimestamp <==> inner is GetTimestamp,
            request@.value() is Write <==> inner is Write,
        ensures
            r.spec_tag() == request_id,
            r.request_id() == request.id(),
            r.request_key() == request@.key(),
            r.request() == request@.value(),
            inner is Get ==> r.req_type() is Get && inner->Get_0 == r.get(),
            inner is GetTimestamp ==> r.req_type() is GetTimestamp && inner->GetTimestamp_0
                == r.get_timestamp(),
            inner is Write ==> r.req_type() is Write && inner->Write_0 == r.write(),
    {
        Response { request_id, inner, request }
    }

    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.request@.key().1 == self.spec_tag()
        &&& self.request@.value() is Get <==> self.req_type() is Get
        &&& self.request@.value() is GetTimestamp <==> self.req_type() is GetTimestamp
        &&& self.request@.value() is Write <==> self.req_type() is Write
    }

    pub closed spec fn server_id(self) -> u64 {
        match self.inner {
            ResponseInner::Get(req) => req.server_id(),
            ResponseInner::GetTimestamp(req) => req.server_id(),
            ResponseInner::Write(req) => req.server_id(),
        }
    }

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
            ResponseInner::Get(_) => ReqType::Get,
            ResponseInner::GetTimestamp(_) => ReqType::GetTimestamp,
            ResponseInner::Write(_) => ReqType::Write,
        }
    }

    pub closed spec fn get(self) -> GetResponse
        recommends
            self.req_type() is Get,
    {
        self.inner->Get_0
    }

    pub closed spec fn get_timestamp(self) -> GetTimestampResponse
        recommends
            self.req_type() is GetTimestamp,
    {
        self.inner->GetTimestamp_0
    }

    pub closed spec fn write(self) -> WriteResponse
        recommends
            self.req_type() is Write,
    {
        self.inner->Write_0
    }

    pub fn destruct_get(self) -> GetResponse
        requires
            self.req_type() is Get,
        returns
            self.get(),
        no_unwind
    {
        match self.inner {
            ResponseInner::Get(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    pub fn destruct_get_timestamp(self) -> GetTimestampResponse
        requires
            self.req_type() is GetTimestamp,
        returns
            self.get_timestamp(),
        no_unwind
    {
        match self.inner {
            ResponseInner::GetTimestamp(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
    }

    pub fn destruct_write(self) -> WriteResponse
        requires
            self.req_type() is Write,
        returns
            self.write(),
        no_unwind
    {
        match self.inner {
            ResponseInner::Write(g) => g,
            _ => {
                assert(false);
                unreached()
            },
        }
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
        ResponseInner::spec_eq_refl(a.inner);
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        ResponseInner::spec_eq_symm(a.inner, b.inner);
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
        ResponseInner::spec_eq_trans(a.inner, b.inner, c.inner);
    }
}

impl ResponseInner {
    pub open spec fn spec_eq(self, other: Self) -> bool {
        match (self, other) {
            (ResponseInner::Get(a), ResponseInner::Get(b)) => a.spec_eq(b),
            (ResponseInner::GetTimestamp(a), ResponseInner::GetTimestamp(b)) => a.spec_eq(b),
            (ResponseInner::Write(a), ResponseInner::Write(b)) => a.spec_eq(b),
            (_, _) => false,
        }
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        match a {
            ResponseInner::Get(a) => GetResponse::spec_eq_refl(a),
            ResponseInner::GetTimestamp(a) => GetTimestampResponse::spec_eq_refl(a),
            ResponseInner::Write(a) => WriteResponse::spec_eq_refl(a),
        }
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
        match (a, b) {
            (ResponseInner::Get(a), ResponseInner::Get(b)) => GetResponse::spec_eq_symm(a, b),
            (
                ResponseInner::GetTimestamp(a),
                ResponseInner::GetTimestamp(b),
            ) => GetTimestampResponse::spec_eq_symm(a, b),
            (ResponseInner::Write(a), ResponseInner::Write(b)) => WriteResponse::spec_eq_symm(a, b),
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
                ResponseInner::Get(a),
                ResponseInner::Get(b),
                ResponseInner::Get(c),
            ) => GetResponse::spec_eq_trans(a, b, c),
            (
                ResponseInner::GetTimestamp(a),
                ResponseInner::GetTimestamp(b),
                ResponseInner::GetTimestamp(c),
            ) => GetTimestampResponse::spec_eq_trans(a, b, c),
            (
                ResponseInner::Write(a),
                ResponseInner::Write(b),
                ResponseInner::Write(c),
            ) => WriteResponse::spec_eq_trans(a, b, c),
            (_, _, _) => {},
        }
    }
}

impl Clone for Response {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
    {
        proof {
            use_type_invariant(self);
        }
        let inner = self.inner.clone();
        let request = Tracked(self.request.borrow().duplicate());
        Response { request_id: self.request_id, inner, request }
    }
}

impl Clone for ResponseInner {
    #[allow(unused_variables)]
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
    {
        match self {
            ResponseInner::Get(get) => { ResponseInner::Get(get.clone()) },
            ResponseInner::GetTimestamp(get_ts) => { ResponseInner::GetTimestamp(get_ts.clone()) },
            ResponseInner::Write(write) => { ResponseInner::Write(write.clone()) },
        }
    }
}

} // verus!
impl std::fmt::Debug for ResponseInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResponseInner::Get(get) => f.debug_tuple("Get").field(&get).finish(),
            ResponseInner::GetTimestamp(get_ts) => {
                f.debug_tuple("GetTimestamp").field(&get_ts).finish()
            }
            ResponseInner::Write(write) => f.debug_tuple("Write").field(&write).finish(),
        }
    }
}

impl std::fmt::Debug for Response {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Response")
            .field("request_id", &self.request_id)
            .field("response", &self.inner)
            .finish()
    }
}
