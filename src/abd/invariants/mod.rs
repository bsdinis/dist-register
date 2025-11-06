#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::set::GhostSetAuth;
use vstd::tokens::set::GhostSingleton;

pub mod lin_queue;
pub mod logatom;
pub mod quorum;

use lin_queue::*;
use logatom::*;
use quorum::*;

use vstd::prelude::*;

verus! {

// XXX: how to number invariants
//
// Right now we are giving them sequential numbers. This is very error prone.
//
// Alternative:
//  - define a pub uninterp spec fn invariant_X_id()
//
// spec fns are deterministic so the value would be the same
//
// Question: how to handle collisions?
pub open spec fn state_inv_id() -> int { 1int }

pub type ClientTokenAuth = GhostSetAuth<u64>;
pub type ClientToken = GhostSingleton<u64>;

pub struct StatePredicate {
    pub lin_queue_ids: LinQueueIds,
    pub register_id: int,
    pub server_locs: Map<nat, int>,
    pub client_token_auth_id: int,
}

pub struct State<ML: MutLinearizer<RegisterWrite>> {
    pub tracked register: GhostVarAuth<Option<u64>>,
    pub tracked linearization_queue: LinearizationQueue<ML>,
    pub tracked servers: ServerUniverse,
    pub tracked client_token_auth: ClientTokenAuth,
}

impl<ML> InvariantPredicate<StatePredicate, State<ML>> for StatePredicate
    where ML: MutLinearizer<RegisterWrite>
{
    open spec fn inv(p: StatePredicate, state: State<ML>) -> bool {
        &&& p.lin_queue_ids == state.linearization_queue.ids()
        &&& p.register_id == state.register.id()
        &&& p.client_token_auth_id == state.client_token_auth.id()
        &&& p.server_locs == state.servers.locs()
        &&& state.linearization_queue.register_id == state.register.id()
        &&& state.linearization_queue.client_token_auth_id == state.client_token_auth.id()
        &&& state.linearization_queue.inv()
        &&& state.servers.inv()
        &&& forall |q: Quorum| state.servers.valid_quorum(q) ==> {
            state.linearization_queue.watermark@.timestamp() <= state.servers.quorum_timestamp(q)
        }
    }
}

pub type StateInvariant<ML> = AtomicInvariant<StatePredicate, State<ML>, StatePredicate>;
pub type RegisterView = GhostVar<Option<u64>>;

pub proof fn initialize_system_state<ML>() -> (tracked r: (StateInvariant<ML>, RegisterView))
    where ML: MutLinearizer<RegisterWrite>
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
{
    let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
    let tracked servers = ServerUniverse::dummy();
    let tracked client_token_auth = GhostSetAuth::dummy();
    let tracked linearization_queue = LinearizationQueue::dummy(register.id(), client_token_auth.id());

    let pred = StatePredicate {
        lin_queue_ids: linearization_queue.ids(),
        register_id: register.id(),
        client_token_auth_id: client_token_auth.id(),
        server_locs: servers.locs(),
    };


    let tracked state = State { register, linearization_queue, client_token_auth, servers };
    assert(<StatePredicate as InvariantPredicate<_, _>>::inv(pred, state));
    let tracked state_inv = AtomicInvariant::new(pred, state, state_inv_id());

    (state_inv, view)
}

pub axiom fn get_system_state<ML>() -> (tracked r: (StateInvariant<ML>, RegisterView))
    where ML: MutLinearizer<RegisterWrite>
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
;

}
