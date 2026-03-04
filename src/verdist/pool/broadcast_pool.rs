#![allow(unused)]

use crate::verdist::network::channel::Channel;
use crate::verdist::network::channel::ChannelInvariant;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::proto::Tagged;
use crate::verdist::rpc::proto::TaggedMessage;
use crate::verdist::rpc::replies::ReplyAccumulator;
use crate::verdist::rpc::Replies;
use crate::verdist::rpc::RequestContext;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct BroadcastPool<'a, Pool> {
    pub pool: &'a Pool,
}

// TODO: remove request generic
impl<'a, Pool, Request> BroadcastPool<'a, Pool> where
    Pool: ConnectionPool,
    Pool::C: Channel<S = Request>,
    <Pool::C as Channel>::R: TaggedMessage + std::fmt::Debug,
    Request: TaggedMessage + Clone + std::fmt::Debug,
 {
    pub fn new(pool: &'a Pool) -> BroadcastPool<'a, Pool> {
        BroadcastPool { pool }
    }

    pub fn broadcast_filter<Pred, A, F>(
        self,
        request: Request,
        pred: Ghost<Pred>,
        accum: A,
        filter_fn: F,
    ) -> (r: RequestContext<'a, Pool, Pred, A>)
        where
            Pred: InvariantPredicate<Pred, A>,
            A: ReplyAccumulator<<Pool::C as Channel>::Id, Pred>,
            F: Fn(<Pool::C as Channel>::Id) -> bool,
        requires
            // TODO: forall |chan| #[trigger] Chann::K::send_inv(chan.constant(), chan.id(), request)
            Pred::inv(pred@, accum),
            forall|id| filter_fn.requires((id,)),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<<Pool::C as Channel>::Id>(),
        ensures
            r.pred() == pred@,
    {
        let conns = self.pool.conns();
        for idx in 0..conns.len()
            invariant
                forall|id| filter_fn.requires((id,)),
        {
            let channel = &conns[idx];
            if filter_fn(channel.id()) {
                assume(<Pool::C as Channel>::K::send_inv(channel.constant(), channel.spec_id(), request));
                let _res = channel.send(&request);
            }
        }
        RequestContext::new(self.pool, request.tag(), pred, accum)
    }

    pub fn broadcast<Pred, A>(self,
        request: Request,
        pred: Ghost<Pred>,
        accum: A
    ) -> (r: RequestContext<'a, Pool, Pred, A>)
    where
        Pred: InvariantPredicate<Pred, A>,
        A: ReplyAccumulator<<Pool::C as Channel>::Id, Pred>,
        requires
            Pred::inv(pred@, accum),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<<Pool::C as Channel>::Id>(),
        ensures
            r.pred() == pred@,
    {
        self.broadcast_filter(request, pred, accum, |_s| true)
    }
}

} // verus!
