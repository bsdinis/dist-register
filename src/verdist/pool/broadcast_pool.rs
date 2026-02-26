#![allow(unused)]

use crate::verdist::network::channel::Channel;
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

impl<'a, Pool, Request> BroadcastPool<'a, Pool> where
    Pool: ConnectionPool,
    Pool::C: Channel<S = Tagged<Request>>,
    <Pool::C as Channel>::R: TaggedMessage + std::fmt::Debug,
    Request: Clone + std::fmt::Debug,
 {
    pub fn new(pool: &'a Pool) -> BroadcastPool<'a, Pool> {
        BroadcastPool { pool }
    }

    pub fn broadcast_filter<A, F: Fn(<Pool::C as Channel>::Id) -> bool>(
        self,
        request: Request,
        accum: A,
        filter_fn: F,
    ) -> RequestContext<'a, Pool, A> where A: ReplyAccumulator<<Pool::C as Channel>::Id>
        requires
            forall|id| filter_fn.requires((id,)),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<<Pool::C as Channel>::Id>(),
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
        RequestContext::new(self.pool, tagged.tag(), accum)
    }

    pub fn broadcast<A>(
        self,
        request: <<Pool::C as Channel>::S as TaggedMessage>::Inner,
        accum: A,
    ) -> RequestContext<'a, Pool, A> where A: ReplyAccumulator<<Pool::C as Channel>::Id>
        requires
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<<Pool::C as Channel>::Id>(),
    {
        self.broadcast_filter(request, accum, |_s| true)
    }
}

} // verus!
