use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;
use verdist::rpc::proto::TaggedMessage;

use vstd::pervasive::unreached;
use vstd::prelude::*;
use vstd::resource::map::{GhostPersistentPointsTo, GhostPersistentSubmap};
use vstd::resource::Loc;

mod get;
mod get_timestamp;
mod request;
mod response;
mod write;

pub use get::*;
pub use get_timestamp::*;
pub use request::*;
pub use response::*;
pub use write::*;

// TODO(qed/proto_lb):
// - add the *sent* lowerbound / token to the request to the *response*
// - add type invariant that orders the lowerbounds on the response

verus! {

type RequestProof = GhostPersistentPointsTo<(u64, u64), RequestInner>;

pub enum ReqType {
    Get,
    GetTimestamp,
    Write,
}

pub axiom fn fake_request_proof(id: (u64, u64), inner: RequestInner) -> (tracked r: RequestProof)
    ensures
        r.key() == id,
        r.value().spec_eq(inner),
;

} // verus!
