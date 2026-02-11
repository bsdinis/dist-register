#![allow(dead_code)]
use crate::verdist::network::error::TryRecvError;

use vstd::prelude::*;

verus! {

pub struct Replies<T, R> {
    replies: Vec<(usize, T)>,
    invalid_replies: Vec<(usize, R)>,
    errors: Vec<(usize, TryRecvError)>,
}

impl<T, R> Replies<T, R> {
    pub fn new() -> Self {
        Replies { replies: Vec::new(), invalid_replies: Vec::new(), errors: Vec::new() }
    }

    pub fn with_capacity(n: usize) -> Self {
        Replies { replies: Vec::with_capacity(n), invalid_replies: Vec::new(), errors: Vec::new() }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.replies.len() + self.invalid_replies.len() + self.errors.len() <= usize::MAX
    }

    pub fn len(&self) -> (r: usize)
        ensures r == self.spec_len()
    {
        self.replies.len()
    }

    pub closed spec fn spec_len(self) -> (r: usize) {
        self.replies.len()
    }

    pub fn n_received(&self) -> usize {
        proof {
            use_type_invariant(self);
        }
        self.replies.len() + self.invalid_replies.len() + self.errors.len()
    }

    pub fn replies(&self) -> (r: &[(usize, T)])
        ensures r.len() == self.spec_len()
    {
        self.replies.as_slice()
    }

    pub fn into_replies(self) -> (r: Vec<(usize, T)>)
        ensures r.len() == self.spec_len()
    {
        self.replies
    }

    pub fn invalid_replies(&self) -> &[(usize, R)] {
        self.invalid_replies.as_slice()
    }

    pub fn into_invalid_replies(self) -> Vec<(usize, R)> {
        self.invalid_replies
    }

    pub fn errors(&self) -> &[(usize, TryRecvError)] {
        self.errors.as_slice()
    }

    pub fn into_errors(self) -> Vec<(usize, TryRecvError)> {
        self.errors
    }

    pub fn push_reply(&mut self, idx: usize, v: T)
        ensures
            self.spec_len() == old(self).spec_len() + 1
    {
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        self.replies.push((idx, v))
    }

    pub fn push_invalid_reply(&mut self, idx: usize, resp: R)
    {
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        self.invalid_replies.push((idx, resp))
    }

    pub fn push_error(&mut self, idx: usize, resp: TryRecvError)
    {
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        self.errors.push((idx, resp))
    }
}

} // verus!
