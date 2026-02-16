use crate::verdist::network::channel::BufChannel;
use crate::verdist::network::channel::Channel;
use crate::verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;

verus! {

#[allow(dead_code)]
type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

pub trait ConnectionPool {
    type C: Channel;

    fn n_nodes(&self) -> (r: usize)
        ensures
            r == self.n(),
    ;

    spec fn n(self) -> nat;

    fn quorum_size(&self) -> (r: usize)
        ensures
            r == self.qsize(),
    ;

    spec fn qsize(self) -> nat;

    #[allow(dead_code)]
    fn poll(&self, request_id: u64) -> Vec<
        (
            <Self::C as Channel>::Id,
            Result<Option<Resp<Self>>, crate::verdist::network::error::TryRecvError>,
        ),
    >;

    #[allow(unused)]
    fn id(&self) -> (r: u64)
        ensures
            r == self.pool_id(),
    ;

    spec fn pool_id(self) -> u64;

    fn conns(&self) -> &[Self::C];

    proof fn lemma_quorum_nonzero(self)
        requires
            self.n() > 0,
        ensures
            self.qsize() > 0,
    ;
}

#[allow(unused)]
pub struct FlawlessPool<C> {
    pool: Vec<C>,
    id: u64,
}

impl<C> FlawlessPool<C> where C: Channel, C::S: TaggedMessage {
    pub fn new(pool: Vec<C>, id: u64) -> (r: Self)
        ensures
            r._n() == pool.len(),
    {
        FlawlessPool { pool, id }
    }

    pub closed spec fn _n(self) -> nat {
        self.pool@.len()
    }
}

pub proof fn lemma_pool_len<C: Channel>(pool: FlawlessPool<BufChannel<C>>) where
    C::S: TaggedMessage,
    C::R: TaggedMessage,

    ensures
        pool._n() == pool.n(),
{
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>> where C: Channel, C::R: TaggedMessage {
    type C = BufChannel<C>;

    fn conns(&self) -> &[Self::C] {
        self.pool.as_slice()
    }

    fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    closed spec fn n(self) -> nat {
        self.pool@.len()
    }

    fn quorum_size(&self) -> usize {
        self.n_nodes() / 2 + 1
    }

    closed spec fn qsize(self) -> nat {
        self.n() / 2 + 1
    }

    fn poll(&self, request_tag: u64) -> Vec<
        (C::Id, Result<Option<C::R>, crate::verdist::network::error::TryRecvError>),
    > {
        let conns = self.conns();

        let mut v = Vec::new();

        for idx in 0..conns.len() {
            let channel = &conns[idx];
            let res = channel.try_recv_tag(request_tag);
            v.push((channel.id(), res));
        }

        v
    }

    fn id(&self) -> u64 {
        self.id
    }

    closed spec fn pool_id(self) -> u64 {
        self.id
    }

    proof fn lemma_quorum_nonzero(self) {
    }
}

} // verus!
