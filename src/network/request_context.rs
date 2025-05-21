#![allow(dead_code)]
use crate::network::connection_pool::ConnectionPool;
use crate::network::replies::Replies;
use crate::network::Channel;

use super::error::TryRecvError;

type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;

pub struct RequestContext<'a, Pool: ConnectionPool, T> {
    pool: &'a Pool,
    request_tag: u64,
    replies: Vec<(usize, T)>,
    invalid_replies: Vec<(usize, <Pool::C as Channel>::R)>,
    errors: Vec<(usize, TryRecvError)>,
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
        &self.replies
    }

    pub fn invalid_replies(&self) -> &[(usize, <Pool::C as Channel>::R)] {
        &self.invalid_replies
    }

    pub fn errors(&self) -> &[(usize, TryRecvError)] {
        &self.errors
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

    pub fn wait_for<F, V>(
        mut self,
        termination_cond: F,
        extractor_fn: V,
    ) -> Result<Replies<T, Resp<Pool>>, Replies<T, Resp<Pool>>>
    where
        F: Fn(&Self) -> bool,
        V: Fn(<Pool::C as Channel>::R) -> Result<T, <Pool::C as Channel>::R>,
    {
        loop {
            if termination_cond(&self) {
                break Ok(Replies::new(
                    self.replies,
                    self.invalid_replies,
                    self.errors,
                ));
            }

            if self.replies().len() >= self.pool.quorum_size()
                || self.replies.len() + self.errors.len() + self.invalid_replies.len()
                    >= self.pool.n_nodes()
            {
                break Err(Replies::new(
                    self.replies,
                    self.invalid_replies,
                    self.errors,
                ));
            }

            let mut replies = vec![];
            let mut invalid_replies = vec![];
            let mut errors = vec![];
            for (idx, response) in self.pool.poll(self.request_tag) {
                match response {
                    Ok(Some(r)) => match extractor_fn(r) {
                        Ok(v) => replies.push((idx, v)),
                        Err(resp) => invalid_replies.push((idx, resp)),
                    },
                    Ok(None) => {}
                    Err(e) => {
                        tracing::error!(
                            failing_node = idx,
                            request_tag = self.request_tag,
                            error = ?e,
                            "failed to get response"
                        );
                        errors.push((idx, e));
                    }
                }
            }

            self.replies.append(&mut replies);
            self.invalid_replies.append(&mut invalid_replies);
            self.errors.append(&mut errors);
        }
    }
}
