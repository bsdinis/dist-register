#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::invariant::*;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;

pub mod client_id_map;
pub mod lin_queue;
pub mod logatom;
pub mod server_map;

use client_id_map::*;
use lin_queue::*;
use logatom::*;
use server_map::*;

verus! {

pub struct StatePredicate {
    pub lin_queue_namespace: Map<&'static str, int>,
    pub register_id: int,
    pub server_map_locs: Map<u64, int>,
}

pub struct State<ML: MutLinearizer<RegisterWrite>> {
    pub tracked register: GhostVarAuth<Option<u64>>,
    pub tracked linearization_queue: LinearizationQueue<ML>,
    pub tracked server_map: ServerMap,
}

impl<ML> InvariantPredicate<StatePredicate, State<ML>> for StatePredicate
    where ML: MutLinearizer<RegisterWrite>
{
    open spec fn inv(p: StatePredicate, state: State<ML>) -> bool {
        &&& p.lin_queue_namespace == state.linearization_queue.namespace()
        &&& p.register_id == state.register.id()
        &&& p.server_map_locs == state.server_map.locs()
        &&& state.linearization_queue.inv()
        &&& state.linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts()
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
    let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
    let tracked linearization_queue = LinearizationQueue::dummy();
    let tracked server_map = ServerMap::dummy();
    let pred = StatePredicate {
        lin_queue_namespace: linearization_queue.namespace(),
        register_id: register.id(),
        server_map_locs: server_map.locs(),
    };


    let tracked state = State { linearization_queue, register, server_map };
    // TODO(assume): min quorum invariant
    assume(linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts()); // TODO
    assert(<StatePredicate as InvariantPredicate<_, _>>::inv(pred, state));
    let tracked state_inv = AtomicInvariant::new(pred, state, 1int);

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
