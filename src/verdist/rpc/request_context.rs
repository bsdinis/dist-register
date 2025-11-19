#![allow(dead_code)]
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
    pub replies: Vec<(usize, T)>,
    pub invalid_replies: Vec<(usize, <Pool::C as Channel>::R)>,
    pub errors: Vec<(usize, TryRecvError)>,
}

impl<'a, Pool: ConnectionPool, T> RequestContext<'a, Pool, T> {
    pub fn new(pool: &'a Pool, request_tag: u64) -> Self {
        RequestContext {
            pool,
            request_tag,
            replies: Vec::with_capacity(pool.quorum_size()),
            invalid_replies: Vec::new(),
            errors: Vec::new(),
        }
    }

    pub fn replies(&self) -> &[(usize, T)] {
        self.replies.as_slice()
    }

    pub fn invalid_replies(&self) -> &[(usize, <Pool::C as Channel>::R)] {
        self.invalid_replies.as_slice()
    }

    pub fn errors(&self) -> &[(usize, TryRecvError)] {
        self.errors.as_slice()
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
    pub fn wait_for<F, V>(self, termination_cond: F, extractor_fn: V) -> Result<
        Replies<T, Resp<Pool>>,
        Replies<T, Resp<Pool>>,
    > where
        F: Fn(&Self) -> bool,
        V: Fn(<Pool::C as Channel>::R) -> Result<T, <Pool::C as Channel>::R>,
     {
        let mut self_mut = self;
        assume(self_mut.replies.len() + self_mut.errors.len() + self_mut.invalid_replies.len()
            < usize::MAX);
        loop
            invariant
                self_mut.replies.len() + self_mut.errors.len() + self_mut.invalid_replies.len()
                    < usize::MAX,
        {
            assume(termination_cond.requires((&self_mut,)));
            if termination_cond(&self_mut) {
                return Ok(
                    Replies::new(self_mut.replies, self_mut.invalid_replies, self_mut.errors),
                );
            }
            if self_mut.replies().len() >= self_mut.pool.quorum_size() || self_mut.replies.len()
                + self_mut.errors.len() + self_mut.invalid_replies.len()
                >= self_mut.pool.n_nodes() {
                return Err(
                    Replies::new(self_mut.replies, self_mut.invalid_replies, self_mut.errors),
                );
            }
            let mut replies = vec![];
            let mut invalid_replies = vec![];
            let mut errors = vec![];
            let it = self_mut.pool.poll(self_mut.request_tag);
            for (idx, response) in it {
                match response {
                    Ok(Some(r)) => {
                        assume(extractor_fn.requires((r,)));
                        match extractor_fn(r) {
                            Ok(v) => replies.push((idx, v)),
                            Err(resp) => invalid_replies.push((idx, resp)),
                        }
                    },
                    Ok(None) => {},
                    Err(e) => {
                        errors.push((idx, e));
                    },
                }
            }

            self_mut.replies.append(&mut replies);
            self_mut.invalid_replies.append(&mut invalid_replies);
            self_mut.errors.append(&mut errors);
            assume(self_mut.replies.len() + self_mut.errors.len() + self_mut.invalid_replies.len()
                < usize::MAX);
        }
    }
}

} // verus!
