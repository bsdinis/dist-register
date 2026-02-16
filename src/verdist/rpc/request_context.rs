use crate::verdist::network::channel::Channel;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::replies::RepliesView;
use crate::verdist::rpc::Replies;

#[allow(dead_code)]
type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct RequestContext<'a, Pool: ConnectionPool, T, Pred> where
    Pred: InvariantPredicate<
        Pred,
        RepliesView<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R>,
    >,
 {
    pub pool: &'a Pool,
    pub request_tag: u64,
    #[allow(dead_code)]
    pub replies: Replies<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R, Pred>,
}

impl<'a, Pool: ConnectionPool, T, Pred> RequestContext<'a, Pool, T, Pred> where
    Pred: InvariantPredicate<
        Pred,
        RepliesView<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R>,
    >,
 {
    pub fn new(pool: &'a Pool, request_tag: u64, pred: Ghost<Pred>) -> Self
        requires
            Pred::inv(pred@, RepliesView::empty()),
            vstd::std_specs::btree::obeys_key_model::<<Pool::C as Channel>::Id>(),
    {
        RequestContext { pool, request_tag, replies: Replies::new(pred) }
    }

    #[allow(dead_code)]
    pub fn tag(&self) -> u64 {
        self.request_tag
    }

    #[allow(dead_code)]
    pub fn n_nodes(&self) -> usize {
        self.pool.n_nodes()
    }

    #[allow(dead_code)]
    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }

    #[allow(dead_code)]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait_for<F, V>(self, termination_cond: F, extractor_fn: V) -> (r: Result<
        Replies<<Pool::C as Channel>::Id, T, Resp<Pool>, Pred>,
        Replies<<Pool::C as Channel>::Id, T, Resp<Pool>, Pred>,
    >) where
        F: Fn(&Replies<<Pool::C as Channel>::Id, T, <Pool::C as Channel>::R, Pred>) -> bool,
        V: Fn(<Pool::C as Channel>::R) -> Result<T, <Pool::C as Channel>::R>,

        requires
            forall|replies| termination_cond.requires((&replies,)),
            forall|r|
                extractor_fn.requires(
                    (r,),
                ),
    // vstd::std_specs::btree::obeys_key_model::<<Pool::C as Channel>::Id>(),

        ensures
            r is Ok ==> call_ensures(termination_cond, (&r->Ok_0,), true),
    {
        let mut self_mut = self;
        loop
            invariant
                forall|replies| termination_cond.requires((&replies,)),
                forall|r| extractor_fn.requires((r,)),
        {
            if termination_cond(&self_mut.replies) {
                return Ok(self_mut.replies);
            }
            if self_mut.replies.len() >= self_mut.pool.quorum_size()
                || self_mut.replies.n_received() >= self_mut.pool.n_nodes() {
                return Err(self_mut.replies);
            }
            let it = self_mut.pool.poll(self_mut.request_tag);
            for (idx, response) in it
                invariant
                    forall|r| extractor_fn.requires((r,)),
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
