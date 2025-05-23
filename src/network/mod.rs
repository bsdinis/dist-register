pub mod broadcast_pool;
pub mod connection_pool;
pub mod error;
pub mod modelled;
pub mod replies;
pub mod request_context;

use std::collections::HashMap;
use std::time::Duration;

use crate::network::error::ConnectError;
use crate::network::error::SendError;
use crate::network::error::TryListenError;
use crate::network::error::TryRecvError;

use rand_distr::{Distribution, Normal};

use vstd::prelude::*;
use vstd::rwlock::RwLock;

fn park_thread(mean: Duration, std_dev: Duration) {
    let normal = Normal::new(mean.as_secs_f64(), std_dev.as_secs_f64())
        .expect("should be able to construct normal distribution");
    let wait = normal.sample(&mut rand::rng());
    if wait.is_sign_positive() {
        std::thread::sleep(Duration::from_secs_f64(wait));
    }
}

fn default_delay() -> (Duration, Duration) {
    Default::default()
}

verus! {

struct EmptyCond;

impl<V> vstd::rwlock::RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

pub assume_specification[park_thread](mean: Duration, std_dev: Duration);
pub assume_specification[default_delay]() -> (a: (Duration, Duration));

pub trait Channel {
    type R;
    type S;

    fn try_recv(&self) -> Result<Self::R, TryRecvError>;
    fn send(&self, v: Self::S) -> Result<(), SendError<Self::S>>;
    fn id(&self) -> u64;

    fn add_latency(&mut self, _avg: Duration, _stddev: Duration) {}
    fn delay(&self) -> (Duration, Duration) {
        default_delay()
    }

    fn wait(&self) {
        let (mean, std_dev) = self.delay();
        park_thread(mean, std_dev);
    }
}

pub trait ChannelExt {
    fn induce_fault(&self) -> bool;
    fn clear_fault(&self) -> bool;
}

pub trait TaggedMessage {
    type Inner;

    fn tag(&self) -> u64;
}

pub trait Listener<C>
where
    C: Channel,
{
    fn try_accept(&self) -> Result<C, TryListenError>;
}

pub trait Connector<C>
where
    C: Channel,
{
    fn connect(&self, id: u64) -> Result<C, ConnectError>;
}

pub struct BufChannel<C: Channel> {
    channel: C,
    buffered: RwLock<HashMap<u64, C::R>, EmptyCond>,
}

impl<C: Channel> BufChannel<C> {
    pub fn new(channel: C) -> Self {
        BufChannel {
            channel,
            buffered: RwLock::new(HashMap::new(), Ghost(EmptyCond)),
        }
    }
}

impl<C> BufChannel<C>
where
    C: Channel,
    C::R: TaggedMessage,
{
    pub fn try_recv_tag(&self, tag: u64) -> Result<Option<C::R>, TryRecvError> {
        let (mut guard, handle) = self.buffered.acquire_write();
        if let Some(r) = guard.remove(&tag) {
            handle.release_write(guard);
            return Ok(Some(r));
        }
        handle.release_write(guard);

        match self.channel.try_recv() {
            Ok(r) if r.tag() == tag => Ok(Some(r)),
            Ok(r) => {
                let (mut guard, handle) = self.buffered.acquire_write();
                guard.insert(r.tag(), r);
                handle.release_write(guard);
                Ok(None)
            }
            Err(crate::network::TryRecvError::Disconnected) => Err(TryRecvError::Disconnected),
            Err(crate::network::TryRecvError::Empty) => Ok(None),
        }
    }
}

impl<C: Channel> Channel for BufChannel<C> {
    type R = C::R;
    type S = C::S;

    fn id(&self) -> u64 {
        self.channel.id()
    }
    fn try_recv(&self) -> Result<Self::R, TryRecvError> {
        self.channel.try_recv()
    }
    fn send(&self, v: Self::S) -> Result<(), SendError<Self::S>> {
        self.channel.send(v)
    }
    fn wait(&self) {
        self.channel.wait();
    }
    fn delay(&self) -> (Duration, Duration) {
        self.channel.delay()
    }
    fn add_latency(&mut self, avg: Duration, stddev: Duration) {
        self.channel.add_latency(avg, stddev);
    }
}

impl<C: ChannelExt + Channel> ChannelExt for BufChannel<C> {
    fn clear_fault(&self) -> bool {
        self.channel.clear_fault()
    }
    fn induce_fault(&self) -> bool {
        self.channel.induce_fault()
    }
}

}
