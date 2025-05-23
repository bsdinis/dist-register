use crate::network::connection_pool::ConnectionPool;
use crate::network::request_context::RequestContext;
use crate::network::Channel;
use crate::proto::Tagged;

use super::TaggedMessage;

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
        // tracing::info!(?request, "broadcast");
        let tagged = Tagged::tag(request);
        let conns = self.pool.conns();
        for idx in 0..conns.len() {
            assume(filter_fn.requires((idx,)));
            if filter_fn(idx) {
                let channel = &conns[idx];
                let _res = channel.send(tagged.clone());
                // if res.is_err() { tracing::error!("failed to send request to a replica {idx}: {e:?}") };
            }
        }
        // tracing::debug!(?tagged, client_id = self.pool.id(), "broadcast complete");
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
