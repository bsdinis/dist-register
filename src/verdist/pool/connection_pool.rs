use crate::verdist::network::channel::BufChannel;
use crate::verdist::network::channel::Channel;
use crate::verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;

verus! {

#[allow(dead_code)]
type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

pub trait ConnectionPool {
    type C: Channel;

    fn len(&self) -> (r: usize)
        ensures
            r == self.spec_len(),
    ;

    spec fn spec_len(self) -> nat;

    // TODO: wrong abstraction layer
    fn quorum_size(&self) -> (r: usize)
        ensures
            r == self.spec_quorum_size(),
    ;

    spec fn spec_quorum_size(self) -> nat;

    #[allow(dead_code)]
    fn poll(&self, request_id: u64) -> Vec<
        (
            <Self::C as Channel>::Id,
            Result<Option<Resp<Self>>, crate::verdist::network::error::TryRecvError>,
        ),
    >;

    // TODO: don't like this
    // Assuming the symmetric ids, we would like to say something
    // about all the sources in the flow are the same
    #[allow(unused)]
    fn id(&self) -> (r: u64)
        ensures
            r == self.spec_id(),
    ;

    spec fn spec_id(self) -> u64;

    fn conns(&self) -> &[Self::C];

    proof fn lemma_quorum_nonzero(self)
        requires
            self.spec_len() > 0,
        ensures
            self.spec_quorum_size() > 0,
    ;
}

#[allow(unused)]
pub struct FlawlessPool<C> {
    pool: Vec<C>,
    id: u64,
}

impl<C> FlawlessPool<BufChannel<C>> where C: Channel, C::S: TaggedMessage, C::R: TaggedMessage {
    pub fn new(pool: Vec<BufChannel<C>>, id: u64) -> (r: Self)
        ensures
            r.spec_len() == pool.len(),
    {
        FlawlessPool { pool, id }
    }
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>> where
    C: Channel,
    C::S: TaggedMessage,
    C::R: TaggedMessage,
 {
    type C = BufChannel<C>;

    fn conns(&self) -> &[Self::C] {
        self.pool.as_slice()
    }

    fn len(&self) -> usize {
        self.pool.len()
    }

    closed spec fn spec_len(self) -> nat {
        self.pool@.len()
    }

    // TODO: remove
    fn quorum_size(&self) -> usize {
        self.len() / 2 + 1
    }

    closed spec fn spec_quorum_size(self) -> nat {
        self.spec_len() / 2 + 1
    }

    fn id(&self) -> u64 {
        self.id
    }

    closed spec fn spec_id(self) -> u64 {
        self.id
    }

    proof fn lemma_quorum_nonzero(self) {
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
}

} // verus!
