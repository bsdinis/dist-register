#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::Request;
use crate::proto::Response;
use verdist::network::channel::ChannelInvariant;

use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

#[allow(dead_code)]
pub struct ChannelInv {
    // TODO: add a loc, to some ghost map from request_id to some X
    pub commitment_id: Loc,
    pub server_tokens_id: Loc,
}

impl ChannelInv {
    pub open spec fn from_state_pred(s_inv: StatePredicate) -> Self {
        ChannelInv {
            commitment_id: s_inv.commitments_ids.commitment_id,
            server_tokens_id: s_inv.server_tokens_id,
        }
    }
}

// Invariant on server
impl ChannelInvariant<ChannelInv, (u64, u64), Request, Response> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Request) -> bool {
        true
    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Response) -> bool {
        s is Get ==> {
            let sent = s->Get_0;
            &&& sent.server_id() == id.0
            &&& sent.spec_commitment().id() == k.commitment_id
            &&& sent.server_token_id() == k.server_tokens_id
        }
        // TODO: s should have the gname that is in Response

    }
}

// Invariant on client
impl ChannelInvariant<ChannelInv, (u64, u64), Response, Request> for ChannelInv {
    open spec fn recv_inv(k: ChannelInv, id: (u64, u64), r: Response) -> bool {
        r is Get ==> {
            let recv = r->Get_0;
            &&& recv.server_id() == id.1
            &&& recv.spec_commitment().id() == k.commitment_id
            &&& recv.server_token_id() == k.server_tokens_id
        }
        // TODO: r should have the gname that is in Response

    }

    open spec fn send_inv(k: ChannelInv, id: (u64, u64), s: Request) -> bool {
        true
    }
}

} // verus!
