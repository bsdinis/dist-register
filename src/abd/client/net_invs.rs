use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::proto::{GetResponse, Response};
use crate::verdist::rpc::proto::Tagged;
use crate::verdist::rpc::replies::RepliesView;

verus! {

#[allow(dead_code)]
pub struct GetInv {
    pub old_servers: ServerUniverse,
}

#[allow(dead_code)]
pub struct WritebackInv {}

#[allow(dead_code)]
pub struct GetTimestampInv {}

#[allow(dead_code)]
pub struct WriteInv {}

impl InvariantPredicate<GetInv, RepliesView<(u64, u64), GetResponse, Tagged<Response>>> for GetInv {
    open spec fn inv(
        pred: GetInv,
        v: RepliesView<(u64, u64), GetResponse, Tagged<Response>>,
    ) -> bool {
        &&& v.replies.dom().map(|x: (u64, u64)| x.1) <= pred.old_servers.dom()
        &&& v.invalid_replies.dom().map(|x: (u64, u64)| x.1) <= pred.old_servers.dom()
        &&& v.errors.dom().map(|x: (u64, u64)| x.1) <= pred.old_servers.dom()
        &&& forall|chan_id: (u64, u64)| #[trigger]
            v.replies.contains_key(chan_id) ==> pred.old_servers[chan_id.1]@@.timestamp()
                <= v.replies[chan_id].spec_timestamp()
    }
}

impl<ChanId, T, R> InvariantPredicate<WritebackInv, RepliesView<ChanId, T, R>> for WritebackInv {
    open spec fn inv(pred: WritebackInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}

impl<ChanId, T, R> InvariantPredicate<
    GetTimestampInv,
    RepliesView<ChanId, T, R>,
> for GetTimestampInv {
    open spec fn inv(pred: GetTimestampInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}

impl<ChanId, T, R> InvariantPredicate<WriteInv, RepliesView<ChanId, T, R>> for WriteInv {
    open spec fn inv(pred: WriteInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}

} // verus!
