use std::sync::Arc;

use echo::invariants::requests::RequestCtrToken;
use echo::invariants::StateInvariant;

use vstd::atomic::PermissionU64;
use vstd::prelude::*;

verus! {

#[allow(unused)]
pub(crate) fn get_invariant_state(client_id: u64, request_perm: Tracked<PermissionU64>) -> (r: (
    Tracked<RequestCtrToken>,
    Tracked<Arc<StateInvariant>>,
))
    requires
        request_perm@.value() == 0,
    ensures
        r.0@.key() == client_id,
        r.0@.value().0 == 0,
        r.0@.value().1 == request_perm@.id(),
        r.0@.id() == r.1@.constant().request_map_ids.request_ctr_id,
        r.1@.namespace() == echo::invariants::state_inv_id(),
{
    let tracked state_inv;
    proof {
        state_inv = echo::invariants::get_system_state();
    }

    let tracked mut request_ctr_token;
    vstd::open_atomic_invariant!(&state_inv => state => {
        proof {
            // XXX(assume/client_disjoint): client_id uniqueness: could be resolved by a client id service
            assume(!state.request_map.request_ctr_map().contains_key(client_id));

            let tracked Tracked(request_p) = request_perm;
            request_ctr_token = state.request_map.login(client_id, request_p);
            state.request_map.agree_client_token(&request_ctr_token);
        }

        // XXX: not load bearing but good for debugging
        assert(<echo::invariants::StatePredicate as vstd::invariant::InvariantPredicate<_, _>>::inv(state_inv.constant(), state));
    });

    (Tracked(request_ctr_token), Tracked(state_inv))
}

} // verus!
