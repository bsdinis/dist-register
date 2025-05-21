use crate::network::connection_pool::ConnectionPool;
use crate::network::request_context::RequestContext;
use crate::network::Channel;
use crate::proto::Tagged;

use super::TaggedMessage;

pub struct BroadcastPool<'a, Pool> {
    pool: &'a Pool,
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
    ) -> RequestContext<'a, Pool, T> {
        tracing::info!(?request, "broadcast");
        let tagged = Tagged::tag(request);
        self.pool
            .iter()
            .enumerate()
            .filter(|(idx, _channel)| filter_fn(*idx))
            .map(|(idx, channel)| (idx, channel.send(tagged.clone())))
            .for_each(|(idx, result)| {
                if let Err(e) = result {
                    tracing::error!("failed to send request to a replica {idx}: {e:?}");
                }
            });
        tracing::debug!(?tagged, client_id = self.pool.id(), "broadcast complete");
        RequestContext::new(self.pool, tagged.tag())
    }

    pub fn broadcast<T>(
        self,
        request: <<Pool::C as Channel>::S as TaggedMessage>::Inner,
    ) -> RequestContext<'a, Pool, T> {
        self.broadcast_filter(request, |_| true)
    }
}
