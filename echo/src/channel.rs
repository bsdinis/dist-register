#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::Request;
use crate::proto::Response;

use verdist::network::channel::ChannelInvariant;
#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;

use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

#[allow(dead_code)]
pub struct ChannelInv {
    pub request_map_id: Loc,
}

impl ChannelInv {
    pub open spec fn from_state_pred(s_inv: StatePredicate) -> Self {
        ChannelInv { request_map_id: s_inv.request_map_ids.request_auth_id }
    }
}

pub open spec fn chan_request_inv(
    k: ChannelInv,
    client_id: u64,
    server_id: u64,
    r: Request,
) -> bool {
    &&& r.request_key() == (client_id, r.spec_tag())
    &&& r.request_id() == k.request_map_id
}

pub open spec fn chan_response_inv(
    k: ChannelInv,
    client_id: u64,
    server_id: u64,
    r: Response,
) -> bool {
    &&& r.request_id() == k.request_map_id
    &&& r.request_key().0 == client_id
}

// Invariant on server
impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        chan_request_inv(k, id.1, id.0, r)
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        chan_response_inv(k, id.1, id.0, s)
    }
}

// Invariant on client
impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        chan_response_inv(k, id.0, id.1, r)
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        chan_request_inv(k, id.0, id.1, s)
    }
}

} // verus!
