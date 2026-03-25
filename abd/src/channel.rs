use crate::proto::Request;
use crate::proto::Response;
use verdist::network::channel::ChannelInvariant;

use vstd::prelude::*;

verus! {

pub struct ChannelInv {
    // TODO: this is a particular loc, to some ghost map from request_id to some X
    // loc: Loc,
}

// Invariant on server
impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        true
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        s is Get ==> {
            let sent = s->Get_0;
            &&& s.server_id() == id.0
        }
        // TODO: s should have the gname that is in Response

    }
}

// Invariant on client
impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        r is Get ==> {
            let recv = r->Get_0;
            recv.server_id() == id.1
        }
        // TODO: r should have the gname that is in Response

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        true
    }
}

} // verus!
