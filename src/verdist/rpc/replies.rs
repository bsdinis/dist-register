#![allow(dead_code)]
use crate::verdist::network::error::TryRecvError;

use vstd::prelude::*;

verus! {

pub struct Replies<T, R> {
    pub replies: Vec<(usize, T)>,
    pub invalid_replies: Vec<(usize, R)>,
    pub errors: Vec<(usize, TryRecvError)>,
}

impl<T, R> Replies<T, R> {
    pub fn new(
        replies: Vec<(usize, T)>,
        invalid_replies: Vec<(usize, R)>,
        errors: Vec<(usize, TryRecvError)>,
    ) -> Self {
        Replies { replies, invalid_replies, errors }
    }

    pub fn replies(&self) -> &[(usize, T)] {
        self.replies.as_slice()
    }

    pub fn into_replies(self) -> Vec<(usize, T)> {
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
}

} // verus!
