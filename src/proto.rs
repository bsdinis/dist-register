use crate::network::TaggedMessage;
use std::sync::atomic::AtomicU64;

use vstd::prelude::*;

verus! {
exec static REQUEST_TAG: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Copy)]
pub struct Tagged<R> {
    pub(crate) tag: u64,
    pub(crate) inner: R,
}

impl<R: Clone> Clone for Tagged<R> {
    fn clone(&self) -> Self {
        Tagged {
            tag: self.tag,
            inner: self.inner.clone()
        }
    }
}

impl<R> Tagged<R> {
    pub fn tag(inner: R) -> Self {
        let tag = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        Tagged { tag, inner }
    }

    pub fn into_inner(self) -> R {
        self.inner
    }

    pub fn deref(&self) -> &R {
        &self.inner
    }
}

impl<R> TaggedMessage for Tagged<R> {
    type Inner = R;

    fn tag(&self) -> u64 {
        self.tag
    }
}

}
