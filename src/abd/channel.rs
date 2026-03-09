use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::verdist::network::channel::Channel;
use crate::verdist::network::channel::ChannelInvariant;
use std::collections::HashMap;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct ChannelInv {
    // TODO: this is a particular loc, to some ghost map from request_id to some X
    // loc: Loc,
}

impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        true  // TODO: r should have the gname that is in Request

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        true  // TODO: s should have the gname that is in Response

    }
}

impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        true  // TODO: r should have the gname that is in Request

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        true  // TODO: s should have the gname that is in Response

    }
}

impl<C> vstd::rwlock::RwLockPredicate<HashMap<u64, C>> for ChannelInv where
    C: Channel<Id = (u64, u64), R = Request, S = Response, K = ChannelInv>,
 {
    open spec fn inv(self, v: HashMap<u64, C>) -> bool {
        forall|client_id: u64| #[trigger]
            v@.contains_key(client_id) ==> { self == v@[client_id].constant() }
    }
}

} // verus!
