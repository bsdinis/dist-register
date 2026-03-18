pub mod broadcast_pool;
pub mod connection_pool;

pub use broadcast_pool::BroadcastPool;
pub use connection_pool::ConnectionPool;
pub use connection_pool::FlawlessPool;

use crate::network::channel::Channel;

pub type PoolChannel<Pool> = <Pool as ConnectionPool>::C;
pub type ChannelReq<Pool> = <<Pool as ConnectionPool>::C as Channel>::S;
pub type ChannelResp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;
pub type ChannelId<Pool> = <<Pool as ConnectionPool>::C as Channel>::Id;
pub type ChannelK<Pool> = <<Pool as ConnectionPool>::C as Channel>::K;
