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
    pub commitment_id: Loc,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub server_locs: Map<u64, Loc>,
}

impl ChannelInv {
    pub open spec fn from_state_pred(s_inv: StatePredicate) -> Self {
        ChannelInv {
            commitment_id: s_inv.commitments_ids.commitment_id,
            request_map_id: s_inv.request_map_ids.request_auth_id,
            server_tokens_id: s_inv.server_tokens_id,
            server_locs: s_inv.server_locs,
        }
    }
}

// Invariant on server
impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        &&& r.request_key() == (id.1, r.spec_tag())
        &&& r.request_id() == k.request_map_id
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        s.req_type() is Get ==> {
            let sent = s.get();
            &&& s.request_id() == k.request_map_id
            &&& sent.server_id() == id.0  // TODO -- move this to s itself
            &&& sent.spec_commitment().id() == k.commitment_id
            &&& sent.server_token_id() == k.server_tokens_id
            &&& k.server_locs.contains_key(sent.server_id())
            &&& k.server_locs[sent.server_id()] == sent.loc()
        }
    }
}

// Invariant on client
impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        r.req_type() is Get ==> {
            let recv = r.get();
            &&& r.request_id() == k.request_map_id
            &&& recv.server_id() == id.1  // TODO -- move this to r itself
            &&& recv.spec_commitment().id() == k.commitment_id
            &&& recv.server_token_id() == k.server_tokens_id
            &&& k.server_locs.contains_key(recv.server_id())
            &&& k.server_locs[recv.server_id()] == recv.loc()
        }
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        &&& s.request_key() == (id.0, s.spec_tag())
        &&& s.request_id() == k.request_map_id
    }
}

} // verus!
