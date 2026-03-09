use crate::verdist::network::channel::Channel;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::replies::ReplyAccumulator;
use crate::verdist::rpc::Replies;

#[allow(dead_code)]
type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct RequestContext<'a, Pool, Pred, A> where
    Pool: ConnectionPool,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<<Pool::C as Channel>::Id, Pred>,
 {
    pub pool: &'a Pool,
    pub request_tag: u64,
    #[allow(dead_code)]
    pub replies: Replies<<Pool::C as Channel>::Id, Pred, <Pool::C as Channel>::R, A>,
}

impl<'a, Pool, Pred, A> RequestContext<'a, Pool, Pred, A> where
    Pool: ConnectionPool,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<<Pool::C as Channel>::Id, Pred>,
 {
    pub fn new(pool: &'a Pool, request_tag: u64, pred: Ghost<Pred>, accum: A) -> (r: Self)
        requires
            Pred::inv(pred@, accum),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<<Pool::C as Channel>::Id>(),
        ensures
            r.pred() == pred@,
    {
        RequestContext { pool, request_tag, replies: Replies::new(pred, accum) }
    }

    #[allow(dead_code)]
    pub fn tag(&self) -> u64 {
        self.request_tag
    }

    #[allow(dead_code)]
    pub fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    // TODO: remove!
    #[allow(dead_code)]
    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }

    pub closed spec fn pred(self) -> Pred {
        self.replies.pred()
    }

    #[allow(dead_code)]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait_for<F, V>(self, termination_cond: F, extractor_fn: V) -> (r: Result<
        Replies<<Pool::C as Channel>::Id, Pred, Resp<Pool>, A>,
        Replies<<Pool::C as Channel>::Id, Pred, Resp<Pool>, A>,
    >) where
        F: Fn(&Replies<<Pool::C as Channel>::Id, Pred, <Pool::C as Channel>::R, A>) -> bool,
        V: Fn(<Pool::C as Channel>::R) -> Result<A::T, <Pool::C as Channel>::R>,

        requires
            forall|replies| termination_cond.requires((&replies,)),
            forall|r| extractor_fn.requires((r,)),
        ensures
            r is Ok ==> {
                &&& call_ensures(termination_cond, (&r->Ok_0,), true)
                &&& Pred::inv(self.pred(), r->Ok_0.accumulator())
            },
            r is Err ==> {
                &&& Pred::inv(self.pred(), r->Err_0.accumulator())
            },
    {
        let ghost pred = self.pred();
        let mut self_mut = self;
        loop
            invariant
                forall|replies| termination_cond.requires((&replies,)),
                forall|r| extractor_fn.requires((r,)),
                pred == self_mut.pred(),
                pred == self.pred(),
        {
            if termination_cond(&self_mut.replies) {
                self_mut.replies.lemma_pred();
                assert(Pred::inv(self_mut.replies.pred(), self_mut.replies.accumulator()));
                assert(self_mut.replies.pred() == pred);
                return Ok(self_mut.replies);
            }
            if self_mut.replies.len() >= self_mut.pool.quorum_size()
                || self_mut.replies.n_received() >= self_mut.n_nodes() {
                let replies = self_mut.replies;
                replies.lemma_pred();

                assert(Pred::inv(replies.pred(), replies.accumulator()));
                assert(replies.pred() == pred);
                assert(Pred::inv(pred, replies.accumulator()));
                assert(Pred::inv(self.pred(), replies.accumulator()));
                return Err(replies);
            }
            let it = self_mut.pool.poll(self_mut.request_tag);
            for (idx, response) in it
                invariant
                    forall|r| extractor_fn.requires((r,)),
                    pred == self_mut.pred(),
            {
                match response {
                    Ok(Some(r)) => {
                        match extractor_fn(r) {
                            Ok(v) => self_mut.replies.insert_reply(idx, v),
                            Err(resp) => self_mut.replies.insert_invalid_reply(idx, resp),
                        }
                    },
                    Ok(None) => {},
                    Err(e) => {
                        self_mut.replies.insert_error(idx, e);
                    },
                }
            }
        }
    }
}

} // verus!
