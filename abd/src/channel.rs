use crate::proto::Request;
use crate::proto::Response;
use std::collections::HashMap;
use verdist::network::channel::Channel;
use verdist::network::channel::ChannelInvariant;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct ChannelInv {
    // TODO: this is a particular loc, to some ghost map from request_id to some X
    // loc: Loc,
}

// Invariant on server
impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        // r.server_id() == id.1
        true  // TODO: r should have the gname that is in Request

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        s is Get ==> {
            &&& s.server_id() == id.0
        }
        // TODO: s should have the gname that is in Response

    }
}

// Invariant on client
impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        // r.server_id() == id.1
        true
        // TODO: r should have the gname that is in Response

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        true
    }
}

} // verus!
