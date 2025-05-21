use crate::network::TaggedMessage;
use std::sync::atomic::AtomicU64;

#[derive(Debug, Clone, Copy)]
pub struct Tagged<R> {
    pub(crate) tag: u64,
    pub(crate) inner: R,
}

impl<R> Tagged<R> {
    pub fn tag(inner: R) -> Self {
        static REQUEST_TAG: AtomicU64 = AtomicU64::new(0);
        let tag = REQUEST_TAG.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        Tagged { tag, inner }
    }

    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R> std::ops::Deref for Tagged<R> {
    type Target = R;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<R> TaggedMessage for Tagged<R> {
    type Inner = R;

    fn tag(&self) -> u64 {
        self.tag
    }
}
