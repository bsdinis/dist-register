use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

use crate::verdist::rpc::replies::RepliesView;

verus! {

#[allow(dead_code)]
pub struct GetInv {}

#[allow(dead_code)]
pub struct WritebackInv {}

#[allow(dead_code)]
pub struct GetTimestampInv {}

#[allow(dead_code)]
pub struct WriteInv {}

impl<ChanId, T, R> InvariantPredicate<GetInv, RepliesView<ChanId, T, R>> for GetInv {
    open spec fn inv(pred: GetInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}
impl<ChanId, T, R> InvariantPredicate<WritebackInv, RepliesView<ChanId, T, R>> for WritebackInv {
    open spec fn inv(pred: WritebackInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}
impl<ChanId, T, R> InvariantPredicate<GetTimestampInv, RepliesView<ChanId, T, R>> for GetTimestampInv {
    open spec fn inv(pred: GetTimestampInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}
impl<ChanId, T, R> InvariantPredicate<WriteInv, RepliesView<ChanId, T, R>> for WriteInv {
    open spec fn inv(pred: WriteInv, v: RepliesView<ChanId, T, R>) -> bool {
        true
    }
}

}
