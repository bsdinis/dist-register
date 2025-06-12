use crate::verdist::network::channel::Channel;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::proto::Tagged;
use crate::verdist::proto::TaggedMessage;
use crate::verdist::request::RequestContext;

use vstd::prelude::*;

verus! {

pub struct BroadcastPool<'a, Pool> {
    pub pool: &'a Pool,
}

impl<'a, Pool, Request> BroadcastPool<'a, Pool>
where
    Pool: ConnectionPool,
    Pool::C: Channel<S = Tagged<Request>>,
    <Pool::C as Channel>::R: TaggedMessage + std::fmt::Debug,
    Request: Clone + std::fmt::Debug,
{
    pub fn new(pool: &'a Pool) -> BroadcastPool<'a, Pool> {
        BroadcastPool { pool }
    }

    pub fn broadcast_filter<F: Fn(usize) -> bool, T>(
        self,
        request: Request,
        filter_fn: F,
    ) -> RequestContext<'a, Pool, T>
    {
        let tagged = Tagged::tag(request);
        let conns = self.pool.conns();
        for idx in 0..conns.len() {
            assume(filter_fn.requires((idx,)));
            if filter_fn(idx) {
                let channel = &conns[idx];
                let _res = channel.send(tagged.clone());
            }
        }
        RequestContext::new(self.pool, tagged.tag())
    }

    pub fn broadcast<T>(
        self,
        request: <<Pool::C as Channel>::S as TaggedMessage>::Inner,
    ) -> RequestContext<'a, Pool, T> {
        self.broadcast_filter(request, |_s| true)
    }
}

}
