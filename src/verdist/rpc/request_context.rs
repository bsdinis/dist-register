use crate::verdist::network::channel::Channel;
use crate::verdist::network::error::TryRecvError;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::Replies;

type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

use vstd::prelude::*;

verus! {

pub struct RequestContext<'a, Pool: ConnectionPool, T> {
    pub pool: &'a Pool,
    pub request_tag: u64,
    pub replies: Replies<T, <Pool::C as Channel>::R>,
}

impl<'a, Pool: ConnectionPool, T> RequestContext<'a, Pool, T> {
    pub fn new(pool: &'a Pool, request_tag: u64) -> Self {
        RequestContext {
            pool,
            request_tag,
            replies: Replies::with_capacity(pool.quorum_size()),
        }
    }

    pub fn replies(&self) -> &[(usize, T)] {
        self.replies.replies()
    }

    pub fn invalid_replies(&self) -> &[(usize, <Pool::C as Channel>::R)] {
        self.replies.invalid_replies()
    }

    pub fn errors(&self) -> &[(usize, TryRecvError)] {
        self.replies.errors()
    }

    pub fn tag(&self) -> u64 {
        self.request_tag
    }

    pub fn n_nodes(&self) -> usize {
        self.pool.n_nodes()
    }

    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn wait_for<F, V>(self, termination_cond: F, extractor_fn: V) -> (r: Result<
        Replies<T, Resp<Pool>>,
        Replies<T, Resp<Pool>>,
    >) where
        F: Fn(&Replies<T, <Pool::C as Channel>::R>) -> bool,
        V: Fn(<Pool::C as Channel>::R) -> Result<T, <Pool::C as Channel>::R>,
        requires
            forall |replies: Replies<T, <Pool::C as Channel>::R>| termination_cond.requires((&replies,)),
            forall |r: <Pool::C as Channel>::R| extractor_fn.requires((r,)),
        ensures
            r is Ok ==> call_ensures(termination_cond, (&r->Ok_0,), true)
     {
        let mut self_mut = self;
        loop
            invariant
                forall |replies: Replies<T, <Pool::C as Channel>::R>| termination_cond.requires((&replies,)),
                forall |r: <Pool::C as Channel>::R| extractor_fn.requires((r,)),
        {
            if termination_cond(&self_mut.replies) {
                return Ok(
                    self_mut.replies
                );
            }
            if self_mut.replies.len() >= self_mut.pool.quorum_size() || self_mut.replies.n_received() >= self_mut.pool.n_nodes() {
                return Err(
                    self_mut.replies
                );
            }

            let it = self_mut.pool.poll(self_mut.request_tag);
            for (idx, response) in it
                invariant
                    forall |r: <Pool::C as Channel>::R| extractor_fn.requires((r,)),
            {
                match response {
                    Ok(Some(r)) => {
                        match extractor_fn(r) {
                            Ok(v) => self_mut.replies.push_reply(idx, v),
                            Err(resp) => self_mut.replies.push_invalid_reply(idx, resp),
                        }
                    },
                    Ok(None) => {},
                    Err(e) => {
                        self_mut.replies.push_error(idx, e);
                    },
                }
            }
        }
    }
}

} // verus!
