use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;

#[allow(unused_imports)]
use std::sync::Arc;

pub mod requests;

use requests::*;

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
pub open spec fn state_inv_id() -> int {
    1int
}

pub struct StatePredicate {
    pub request_map_ids: RequestMapIds,
}

pub struct State {
    pub tracked request_map: RequestMap,
}

impl State {
    pub open spec fn inv(self) -> bool {
        // member invariants
        &&& self.request_map.is_full()
    }
}

impl InvariantPredicate<StatePredicate, State> for StatePredicate {
    open spec fn inv(p: StatePredicate, state: State) -> bool {
        &&& p.request_map_ids == state.request_map.ids()
        &&& state.inv()
    }
}

pub type StateInvariant = AtomicInvariant<StatePredicate, State, StatePredicate>;

pub proof fn initialize_system_state() -> (tracked r: Arc<StateInvariant>)
    ensures
        r.namespace() == state_inv_id(),
{
    let tracked request_map = RequestMap::new();

    let pred = StatePredicate { request_map_ids: request_map.ids() };

    let tracked state = State { request_map };

    let tracked state_inv = AtomicInvariant::new(pred, state, state_inv_id());

    Arc::new(state_inv)
}

pub axiom fn get_system_state() -> (tracked r: Arc<StateInvariant>)
    ensures
        r.namespace() == state_inv_id(),
;

} // verus!
