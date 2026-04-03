use vstd::prelude::*;

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

pub enum ReqType {
    Get,
    GetTimestamp,
    Write,
}

} // verus!
