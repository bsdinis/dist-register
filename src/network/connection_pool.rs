use rand::seq::SliceRandom;
use rand::Rng;

use crate::network::BufChannel;
use crate::network::Channel;

use super::ChannelExt;
use super::TaggedMessage;

type Resp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;
pub trait ConnectionPool {
    type C: Channel;

    fn n_nodes(&self) -> usize;

    fn quorum_size(&self) -> usize {
        self.n_nodes() / 2 + 1
    }

    fn poll(
        &self,
        request_id: u64,
    ) -> impl Iterator<
        Item = (
            usize,
            Result<Option<Resp<Self>>, crate::network::error::TryRecvError>,
        ),
    >;

    fn shuffle_faults(&self) {}

    fn id(&self) -> u64;

    fn iter(&self) -> impl Iterator<Item = &Self::C>;
}

pub struct FlawlessPool<C> {
    pool: Vec<C>,
    id: u64,
}

pub struct LossyPool<C> {
    pool: Vec<C>,
    faults: usize,
    id: u64,
}

impl<C> FlawlessPool<C>
where
    C: Channel,
    C::S: TaggedMessage,
{
    pub fn new(pool: Vec<C>, id: u64) -> Self {
        FlawlessPool { pool, id }
    }
}

impl<C> LossyPool<C>
where
    C: Channel,
    C::S: TaggedMessage,
{
    pub fn new(pool: Vec<C>, faults: usize, id: u64) -> Self {
        if 2 * faults + 1 > pool.len() {
            tracing::warn!(
                "Constructing a lossy pool for {faults} faults with too few nodes (have {}, required {})",
                pool.len(),
                2 * faults + 1
            );
        }

        LossyPool { pool, faults, id }
    }
}

impl<C> ConnectionPool for FlawlessPool<BufChannel<C>>
where
    C: Channel,
    C::R: TaggedMessage,
{
    type C = BufChannel<C>;

    fn iter(&self) -> impl Iterator<Item = &Self::C> {
        self.pool.iter()
    }

    fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    fn poll(
        &self,
        request_tag: u64,
    ) -> impl Iterator<
        Item = (
            usize,
            Result<Option<C::R>, crate::network::error::TryRecvError>,
        ),
    > {
        self.pool
            .iter()
            .map(move |channel| channel.try_recv_tag(request_tag))
            .enumerate()
    }

    fn id(&self) -> u64 {
        self.id
    }
}

impl<C> ConnectionPool for LossyPool<BufChannel<C>>
where
    C: Channel,
    C: ChannelExt,
    C::R: TaggedMessage,
{
    type C = BufChannel<C>;

    fn iter(&self) -> impl Iterator<Item = &Self::C> {
        self.pool.iter()
    }

    fn n_nodes(&self) -> usize {
        self.pool.len()
    }

    fn poll(
        &self,
        request_id: u64,
    ) -> impl Iterator<
        Item = (
            usize,
            Result<Option<C::R>, crate::network::error::TryRecvError>,
        ),
    > {
        self.pool
            .iter()
            .map(move |channel| channel.try_recv_tag(request_id))
            .enumerate()
    }

    fn shuffle_faults(&self) {
        let mut rng = rand::rng();
        let f = rng.random_range(0..=self.faults);
        let mut faults: Vec<bool> = (0..self.pool.len()).map(|i| i < f).collect();
        faults.shuffle(&mut rng);

        for (idx, (channel, fault)) in self.pool.iter().zip(faults.into_iter()).enumerate() {
            if fault {
                let was_faulty = channel.induce_fault();
                if !was_faulty {
                    tracing::warn!("induced a fault on connection {idx}");
                }
            } else {
                let was_faulty = channel.clear_fault();
                if was_faulty {
                    tracing::warn!("restored connection {idx}");
                }
            }
        }
    }

    fn id(&self) -> u64 {
        self.id
    }
}
