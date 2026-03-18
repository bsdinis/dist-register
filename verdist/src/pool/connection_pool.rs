use crate::network::channel::BufChannel;
use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::rpc::proto::TaggedMessage;

use vstd::prelude::*;

use super::ChannelResp;

verus! {

pub trait ConnectionPool {
    type C: Channel;

    fn len(&self) -> (r: usize)
        ensures
            r == self.spec_len(),
    ;

    spec fn spec_len(self) -> nat;

    #[allow(dead_code)]
    fn poll(&self, request_id: u64) -> (r: Vec<
        (
            <Self::C as Channel>::Id,
            Result<Option<ChannelResp<Self>>, crate::network::error::TryRecvError>,
        ),
    >)
        ensures
            forall|idx|
                0 <= idx < r@.len() ==> {
                    let (id, resp) = #[trigger] r@[idx];
                    &&& self.spec_conns().contains_key(id)
                    &&& resp is Ok && resp->Ok_0 is Some ==> {
                        let x = resp->Ok_0->Some_0;
                        <Self::C as Channel>::K::recv_inv(self.spec_conns()[id].constant(), id, x)
                    }
                },
    ;

    fn conns(&self) -> (r: &[Self::C])
        ensures
            r@.to_set() == self.spec_conns().values(),
    ;

    spec fn spec_conns(&self) -> Map<<Self::C as Channel>::Id, Self::C>;

    proof fn lemma_len(tracked &self)
        ensures
            self.spec_len() == self.spec_conns().len(),
    ;
}

#[allow(unused)]
pub struct FlawlessPool<C> where C: Channel {
    pool: Vec<C>,
}

impl<C: Channel> FlawlessPool<C> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        forall|i, j|
            0 <= i < j < self.pool@.len() ==> #[trigger] self.pool@[i].spec_id()
                != #[trigger] self.pool@[j].spec_id()
    }
}

impl<C> FlawlessPool<BufChannel<C>> where C: Channel, C::S: TaggedMessage, C::R: TaggedMessage {
    pub fn new(pool: Vec<BufChannel<C>>) -> (r: Self)
        requires
            forall|i, j|
                0 <= i < j < pool@.len() ==> #[trigger] pool@[i].spec_id()
                    != #[trigger] pool@[j].spec_id(),
        ensures
            r.spec_len() == pool.len(),
            r.spec_conns().dom() == pool@.to_set().map(|c: BufChannel<C>| c.spec_id()),
            r.spec_conns().values() == pool@.to_set(),
            forall|cid| #[trigger]
                r.spec_conns().contains_key(cid) ==> r.spec_conns()[cid].spec_id() == cid,
    {
        proof {
            admit();  // TODO
        }
        FlawlessPool { pool }
    }
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>> where
    C: Channel,
    C::S: TaggedMessage,
    C::R: TaggedMessage,
 {
    type C = BufChannel<C>;

    fn conns(&self) -> &[Self::C] {
        proof {
            use_type_invariant(self);
            admit();  // TODO
        }
        assert(self.pool@.to_set() == self.spec_conns().values());
        self.pool.as_slice()
    }

    closed spec fn spec_conns(&self) -> Map<<Self::C as Channel>::Id, Self::C> {
        Map::new(
            |id|
                exists|idx|
                    0 <= idx < self.pool@.len() ==> #[trigger] self.pool@[idx].spec_id() == id,
            |id|
                {
                    let idx = choose|idx|
                        0 <= idx < self.pool@.len() ==> #[trigger] self.pool@[idx].spec_id() == id;
                    self.pool@[idx]
                },
        )
    }

    fn len(&self) -> usize {
        self.pool.len()
    }

    closed spec fn spec_len(self) -> nat {
        self.pool@.len()
    }

    proof fn lemma_len(tracked &self) {
        use_type_invariant(self);
        // TODO(connection): lemma len
        admit();
    }

    fn poll(&self, request_tag: u64) -> Vec<
        (C::Id, Result<Option<C::R>, crate::network::error::TryRecvError>),
    > {
        proof {
            use_type_invariant(self);
        }
        let conns = self.conns();

        let mut v = Vec::new();

        for idx in 0..conns.len()
            invariant
                forall|idx|
                    0 <= idx < v@.len() ==> {
                        let (id, resp): (C::Id, Result<Option<C::R>, _>) = #[trigger] v@[idx];
                        &&& self.spec_conns().contains_key(id)
                        &&& resp is Ok && resp->Ok_0 is Some ==> {
                            let x = resp->Ok_0->Some_0;
                            <Self::C as Channel>::K::recv_inv(
                                self.spec_conns()[id].constant(),
                                id,
                                x,
                            )
                        }
                    },
        {
            let channel = &conns[idx];
            let res = channel.try_recv_tag(request_tag);
            proof {
                assume(self.spec_conns().contains_key(channel.spec_id()));  // TODO
                admit();  // TODO
            }
            v.push((channel.id(), res));
        }

        v
    }
}

} // verus!
