pub mod broadcast_pool;
pub mod connection_pool;

pub use broadcast_pool::BroadcastPool;
pub use connection_pool::ConnectionPool;
pub use connection_pool::FlawlessPool;

use crate::network::channel::Channel;

pub(crate) type ChannelReq<Pool> = <<Pool as ConnectionPool>::C as Channel>::S;
pub(crate) type ChannelResp<Pool> = <<Pool as ConnectionPool>::C as Channel>::R;
pub(crate) type ChannelId<Pool> = <<Pool as ConnectionPool>::C as Channel>::Id;
pub(crate) type ChannelK<Pool> = <<Pool as ConnectionPool>::C as Channel>::K;
