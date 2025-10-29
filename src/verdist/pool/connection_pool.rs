use crate::verdist::network::channel::BufChannel;
use crate::verdist::network::channel::Channel;
use crate::verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;

verus! {

type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;
pub trait ConnectionPool {
    type C: Channel;

    fn n_nodes(&self) -> usize;

    fn quorum_size(&self) -> usize {
        self.n_nodes() / 2 + 1
    }

    fn poll(
        &self,
        request_id: u64,
    ) -> Vec<(
            usize,
            Result<Option<Resp<Self>>, crate::verdist::network::error::TryRecvError>,
        )>;

    fn id(&self) -> (r: u64)
        ensures r == self.pool_id();

    spec fn pool_id(self) -> u64;

    fn conns(&self) -> &[Self::C];
}

pub struct FlawlessPool<C> {
    pool: Vec<C>,
    id: u64,
}

impl<C> FlawlessPool<C>
where
    C: Channel,
    C::S: TaggedMessage,
{
    pub fn new(pool: Vec<C>, id: u64) -> Self {
        FlawlessPool { pool, id }
    }
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>>
where
    C: Channel,
    C::R: TaggedMessage,
{
    type C = BufChannel<C>;

    fn conns(&self) -> &[Self::C] {
        self.pool.as_slice()
    }

    fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    fn poll(
        &self,
        request_tag: u64,
    ) -> Vec<(
            usize,
            Result<Option<C::R>, crate::verdist::network::error::TryRecvError>,
        )>
    {
        let conns = self.conns();

        let mut v = Vec::new();

        for idx in 0..conns.len() {
            let channel = &conns[idx];
            let res = channel.try_recv_tag(request_tag);
            v.push((idx, res));
        }

        v
    }

    fn id(&self) -> u64 {
        self.id
    }

    closed spec fn pool_id(self) -> u64 {
        self.id
    }
}

}
