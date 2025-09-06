#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::invariant::*;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::map::GhostMapAuth;

use crate::abd::client::client_id_map::*;
use crate::abd::client::linearization::*;
use crate::abd::client::logatom::*;

verus! {

pub struct StatePredicate {
    pub token_map_id: int,
    pub watermark_loc: int,
    pub register_id: int,
}

pub struct State<ML: MutLinearizer<RegisterWrite>> {
    pub tracked linearization_queue: LinearizationQueue<ML>,
    pub tracked register: GhostVarAuth<Option<u64>>,
}

impl<ML> InvariantPredicate<StatePredicate, State<ML>> for StatePredicate
    where ML: MutLinearizer<RegisterWrite>
{
    open spec fn inv(p: StatePredicate, state: State<ML>) -> bool {
        &&& p.token_map_id == state.linearization_queue.token_map.id()
        &&& p.watermark_loc == state.linearization_queue.watermark.loc()
        &&& p.register_id == state.register.id()
    }
}

pub type StateInvariant<ML> = AtomicInvariant<StatePredicate, State<ML>, StatePredicate>;
pub type RegisterView = Tracked<GhostVar<Option<u64>>>;

pub proof fn initialize_system_state<ML>() -> (r: (StateInvariant<ML>, RegisterView))
    where ML: MutLinearizer<RegisterWrite>
    ensures
        r.0.namespace() == 1int,
        r.0.constant().register_id == r.1@.id(),
{
    let tracked queue = LinearizationQueue::<ML>::dummy();
    let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
    let tracked linearization_queue = LinearizationQueue::dummy();
    let pred = StatePredicate {
        token_map_id: queue.token_map.id(),
        watermark_loc: queue.watermark.loc(),
        register_id: register.id(),
    };


    let tracked state_inv = AtomicInvariant::new(pred, State { linearization_queue, register }, 1int);

    (state_inv, Tracked(view))
}

pub axiom fn get_system_state<ML>() -> (r: (StateInvariant<ML>, RegisterView))
    where ML: MutLinearizer<RegisterWrite>
    ensures
        r.0.namespace() == 1int,
        r.0.constant().register_id == r.1@.id(),
;

pub struct ClientMapPredicate {
    pub map_id: int
}


impl InvariantPredicate<ClientMapPredicate, ClientMap> for ClientMapPredicate {
    open spec fn inv(p: ClientMapPredicate, map: ClientMap) -> bool {
        p.map_id == map.map.id()
    }
}

pub type ClientIdInvariant = AtomicInvariant<ClientMapPredicate, ClientMap, ClientMapPredicate>;

pub proof fn initialize_client_map() -> (r: ClientIdInvariant)
    ensures r.namespace() == 2int
{
    let tracked map = ClientMap::dummy();
    let pred = ClientMapPredicate { map_id: map.id() };

    let tracked inv = AtomicInvariant::new(pred, map, 2int);

    inv
}

pub axiom fn get_client_map() -> (r: ClientIdInvariant)
    ensures r.namespace() == 2int
;

}
