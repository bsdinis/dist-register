use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
use crate::invariants::requests::RequestCtrToken;
use crate::invariants::StateInvariant;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;

#[cfg(verus_only)]
use specs::echo::EchoError as _;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;

pub mod error;

use verdist::rpc::rpc_channel::RpcChannel;
use vstd::atomic::PAtomicU64;
#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

use std::hash::Hash;
use std::sync::Arc;

verus! {

#[allow(dead_code)]
pub struct EchoClient<C> where
    C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv>,
 {
    channel: RpcChannel<C>,
    id: u64,
    state_inv: Tracked<Arc<StateInvariant>>,
    request_ctr_token: Tracked<RequestCtrToken>,
    request_ctr: PAtomicU64,
}

impl<C> EchoClient<C> where C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv> {
    pub fn new(
        channel: BufChannel<C>,
        id: u64,
        request_ctr: PAtomicU64,
        request_ctr_token: Tracked<RequestCtrToken>,
        state_inv: Tracked<Arc<StateInvariant>>,
    ) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().request_map_ids.request_ctr_id == request_ctr_token@.id(),
            state_inv@.constant().request_map_ids.request_auth_id
                == channel.constant().request_map_id,
            channel.spec_id().0 == id,
            request_ctr_token@.key() == id,
            request_ctr_token@.value().0 == 0,
            request_ctr_token@.value().1 == request_ctr.id(),
    {
        EchoClient {
            channel: RpcChannel::new(channel),
            id,
            state_inv,
            request_ctr_token,
            request_ctr,
        }
    }

    closed spec fn id(self) -> u64 {
        self.id
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.state_inv@.constant().request_map_ids.request_ctr_id
            == self.request_ctr_token@.id()
        &&& self.request_ctr_token@.key() == self.id()
        &&& self.request_ctr_token@.value().1 == self.request_ctr.id()
        &&& {
            let c_id = self.channel.spec_id();
            &&& c_id.0 == self.id
            &&& self.state_inv@.constant().request_map_ids.request_auth_id
                == self.channel.constant().request_map_id
        }
    }
}

impl<C> specs::echo::EchoClient<C> for EchoClient<C> where
    C: Channel<R = Response, S = Request, Id = (u64, u64), K = ChannelInv>,
    C::Id: Eq + Hash,
 {
    type Error = error::EchoError;

    type Val = String;

    fn echo(&mut self, message: String) -> (r: Result<String, error::EchoError>) {
        proof {
            use_type_invariant(&*self);
        }
        let req_inner = RequestInner::new_echo(message);
        let tracked mut request_proof;
        let request_id;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let ghost old_dom = state.request_map.request_ctr_map().dom();
            let tracked mut perm;
            proof {
                perm = state.request_map.take_permission(self.request_ctr_token.borrow());
            }
            assume(perm.value() < u64::MAX); // XXX: integer overflow
            request_id = self.request_ctr.fetch_add(Tracked(&mut perm), 1);
            proof {
                request_proof = state.request_map.issue_request_proof(
                    self.request_ctr_token.borrow_mut(),
                    request_id,
                    req_inner, perm
                );
                assert(state.request_map.request_ctr_map().dom() == old_dom);
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req = Request::new(self.id, request_id, req_inner, Tracked(request_proof.duplicate()));

        let reply = match self.channel.invoke(&req) {
            Ok(reply) => reply,
            Err(e) => {
                vlib::veprintln!("[client|{:>3}]: failed to invoke echo: {:?}", self.id, e);
                return Err(error::EchoError)
            },
        };

        reply.lemma_inv();
        proof {
            reply.agree_request(&mut request_proof);
        }

        let reply_message = reply.destruct_echo().message();

        Ok(reply_message)
    }
}

} // verus!
