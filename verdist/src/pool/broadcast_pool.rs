#![allow(unused)]

use crate::network::channel::Channel;
use crate::network::channel::ChannelInvariant;
use crate::pool::ChannelId;
use crate::pool::ChannelResp;
use crate::pool::ConnectionPool;
use crate::pool::PoolChannel;
use crate::rpc::proto::Tagged;
use crate::rpc::proto::TaggedMessage;
use crate::rpc::replies::ReplyAccumulator;
use crate::rpc::Replies;
use crate::rpc::RequestContext;

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
    ChannelResp<Pool>: TaggedMessage + std::fmt::Debug,
    Request: TaggedMessage + Clone + std::fmt::Debug,
 {
    pub fn new(pool: &'a Pool) -> (r: BroadcastPool<'a, Pool>)
        ensures
            r.spec_channels() == pool.spec_channels(),
    {
        BroadcastPool { pool }
    }

    pub open spec fn spec_channels(self) -> Map<ChannelId<Pool>, PoolChannel<Pool>> {
        self.pool.spec_channels()
    }

    pub fn broadcast_filter<Pred, A, F>(
        self,
        request: Request,
        pred: Ghost<Pred>,
        accum: A,
        filter_fn: F,
    ) -> (r: RequestContext<'a, Pool, Pred, A>) where
        Pred: InvariantPredicate<Pred, A>,
        A: ReplyAccumulator<ChannelId<Pool>, Pred, T = ChannelResp<Pool>>,
        F: Fn(ChannelId<Pool>) -> bool,

        requires
    // TODO: forall |chan| #[trigger] Chann::K::send_inv(chan.constant(), chan.id(), request)

            Pred::inv(pred@, accum),
            forall|id| filter_fn.requires((id,)),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<ChannelId<Pool>>(),
        ensures
            r.pred() == pred@,
    {
        let channels = self.pool.channels();
        for idx in 0..channels.len()
            invariant
                forall|id| filter_fn.requires((id,)),
        {
            let channel = &channels[idx];
            if filter_fn(channel.id()) {
                assume(<Pool::C as Channel>::K::send_inv(
                    channel.constant(),
                    channel.spec_id(),
                    request,
                ));
                let _res = channel.send(&request);
            }
        }
        RequestContext::new(self.pool, request.tag(), pred, accum)
    }

    pub fn broadcast<Pred, A>(self, request: Request, pred: Ghost<Pred>, accum: A) -> (r:
        RequestContext<'a, Pool, Pred, A>) where
        Pred: InvariantPredicate<Pred, A>,
        A: ReplyAccumulator<ChannelId<Pool>, Pred, T = ChannelResp<Pool>>,

        requires
            Pred::inv(pred@, accum),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<ChannelId<Pool>>(),
        ensures
            r.pred() == pred@,
    {
        self.broadcast_filter(request, pred, accum, |_s| true)
    }
}

} // verus!
