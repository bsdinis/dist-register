#![allow(unused)]

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::proto::Tagged;
use crate::verdist::rpc::proto::TaggedMessage;
use crate::verdist::rpc::replies::RepliesView;
use crate::verdist::rpc::Replies;
use crate::verdist::rpc::RequestContext;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct BroadcastPool<'a, Pool> {
    pub pool: &'a Pool,
}

impl<'a, Pool, Request> BroadcastPool<'a, Pool> where
    Pool: ConnectionPool,
    Pool::C: Channel<S = Tagged<Request>>,
    <Pool::C as Channel>::R: TaggedMessage + std::fmt::Debug,
    Request: Clone + std::fmt::Debug,
 {
    pub fn new(pool: &'a Pool) -> BroadcastPool<'a, Pool> {
        BroadcastPool { pool }
    }

    pub fn broadcast_filter<F: Fn(<Pool::C as Channel>::Id) -> bool, T, Pred>(
        self,
        request: Request,
        pred: Ghost<Pred>,
        filter_fn: F,
    ) -> RequestContext<'a, Pool, T, Pred> where
        Pred: InvariantPredicate<
            Pred,
            RepliesView<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R>,
        >,

        requires
            forall|id| filter_fn.requires((id,)),
            Pred::inv(pred@, RepliesView::empty()),
            vstd::std_specs::btree::obeys_key_model::<<Pool::C as Channel>::Id>(),
    {
        let tagged = Tagged::tag(request);
        let conns = self.pool.conns();
        for idx in 0..conns.len()
            invariant
                forall|id| filter_fn.requires((id,)),
        {
            let channel = &conns[idx];
            if filter_fn(channel.id()) {
                let _res = channel.send(&tagged);
            }
        }
        RequestContext::new(self.pool, tagged.tag(), pred)
    }

    pub fn broadcast<T, Pred>(
        self,
        request: <<Pool::C as Channel>::S as TaggedMessage>::Inner,
        pred: Ghost<Pred>,
    ) -> RequestContext<'a, Pool, T, Pred> where
        Pred: InvariantPredicate<
            Pred,
            RepliesView<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R>,
        >,

        requires
            Pred::inv(pred@, RepliesView::empty()),
            vstd::std_specs::btree::obeys_key_model::<<Pool::C as Channel>::Id>(),
    {
        self.broadcast_filter(request, pred, |_s| true)
    }
}

} // verus!
