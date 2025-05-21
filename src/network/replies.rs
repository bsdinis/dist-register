#![allow(dead_code)]
use super::error::TryRecvError;

pub struct Replies<T, R> {
    replies: Vec<(usize, T)>,
    invalid_replies: Vec<(usize, R)>,
    errors: Vec<(usize, TryRecvError)>,
}

impl<T, R> Replies<T, R> {
    pub fn new(
        replies: Vec<(usize, T)>,
        invalid_replies: Vec<(usize, R)>,
        errors: Vec<(usize, TryRecvError)>,
    ) -> Self {
        Replies {
            replies,
            invalid_replies,
            errors,
        }
    }

    pub fn replies(&self) -> &[(usize, T)] {
        &self.replies
    }

    pub fn into_replies(self) -> impl Iterator<Item = (usize, T)> {
        self.replies.into_iter()
    }

    pub fn invalid_replies(&self) -> &[(usize, R)] {
        &self.invalid_replies
    }

    pub fn into_invalid_replies(self) -> impl Iterator<Item = (usize, R)> {
        self.invalid_replies.into_iter()
    }

    pub fn errors(&self) -> &[(usize, TryRecvError)] {
        &self.errors
    }

    pub fn into_errors(self) -> impl Iterator<Item = (usize, TryRecvError)> {
        self.errors.into_iter()
    }
}
