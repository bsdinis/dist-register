#![cfg_attr(verus_keep_ghost, verus::trusted)]
#![allow(dead_code)]

#[allow(unused_imports)]
use vstd::atomic::PermissionU64;
use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;

use crate::abd::min::MinOrd;
#[allow(unused_imports)]
use crate::abd::timestamp::Timestamp;

#[allow(unused_imports)]
use std::sync::Arc;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::default::DefaultSpec;

pub mod committed_to;
pub mod lin_queue;
pub mod logatom;
pub mod quorum;

use committed_to::*;
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
pub open spec fn state_inv_id() -> int {
    1int
}

pub struct StatePredicate {
    pub lin_queue_ids: LinQueueIds,
    pub register_id: int,
    pub server_locs: Map<nat, int>,
    pub commitments_ids: CommitmentIds,
}

#[verifier::reject_recursive_types(Id)]
pub struct State<ML, RL, Id: MinOrd> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    pub tracked register: GhostVarAuth<Option<u64>>,
    pub tracked linearization_queue: LinearizationQueue<ML, RL, Id>,
    pub tracked servers: ServerUniverse<Id>,
    pub tracked commitments: Commitments<Id>,
}

impl<ML, RL, Id> State<ML, RL, Id> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
    Id: MinOrd
 {
    pub open spec fn inv(self) -> bool {
        // member invariants
        &&& self.linearization_queue.inv()
        &&& self.servers.inv()
        &&& self.commitments.inv()
        &&& self.commitments.is_full()
        // id concordance
        &&& self.linearization_queue.register_id() == self.register.id()
        &&& self.linearization_queue.committed_to_id()
            == self.commitments.commitment_id()
        // matching state
        &&& self.linearization_queue.current_value() == self.register@
        &&& self.linearization_queue.known_timestamps() == self.commitments.allocated().dom()
        &&& forall|q: Quorum|
            #[trigger] self.servers.valid_quorum(q) ==> {
                self.linearization_queue.watermark() <= self.servers.quorum_timestamp(q)
            }
    }
}

impl<ML, RL, Id> InvariantPredicate<
    StatePredicate,
    State<ML, RL, Id>,
> for StatePredicate where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>, Id: MinOrd {
    open spec fn inv(
        p: StatePredicate,
        state: State<ML, RL, Id>,
    ) -> bool {
        &&& p.register_id == state.register.id()
        &&& p.lin_queue_ids == state.linearization_queue.ids()
        &&& p.server_locs == state.servers.locs()
        &&& p.commitments_ids == state.commitments.ids()
        &&& state.inv()
    }
}

pub type StateInvariant<ML, RL, Id: MinOrd> = AtomicInvariant<
    StatePredicate,
    State<ML, RL, Id>,
    StatePredicate,
>;

pub type RegisterView = GhostVar<Option<u64>>;

pub proof fn initialize_system_state<ML, RL, Id: MinOrd>(tracked zero_perm: PermissionU64) -> (tracked r: (
    Arc<StateInvariant<ML, RL, Id>>,
    RegisterView,
)) where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>, Id: MinOrd
    requires
        zero_perm.value() == 1,
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
{
    let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
    let tracked servers = ServerUniverse::dummy();
    let tracked (commitments, zero_commitment) = Commitments::new(zero_perm);
    let tracked mut linearization_queue = LinearizationQueue::new(register.id(), zero_commitment);

    commitments.agree_commitment_submap(linearization_queue.tracked_committed_values());
    // XXX: load bearing
    assert(linearization_queue.known_timestamps() == set![Timestamp::<Id>::minimum()]);

    let pred = StatePredicate {
        lin_queue_ids: linearization_queue.ids(),
        register_id: register.id(),
        server_locs: servers.locs(),
        commitments_ids: commitments.ids(),
    };

    let tracked state = State { register, linearization_queue, servers, commitments };

    assume(<StatePredicate as InvariantPredicate<_, _>>::inv(pred, state)); // TODO(id)
    let tracked state_inv = AtomicInvariant::new(pred, state, state_inv_id());

    (Arc::new(state_inv), view)
}

pub axiom fn get_system_state<ML, RL, Id: MinOrd>() -> (tracked r: (
    Arc<StateInvariant<ML, RL, Id>>,
    RegisterView,
)) where ML: MutLinearizer<RegisterWrite>, RL: ReadLinearizer<RegisterRead>
    ensures
        r.0.namespace() == state_inv_id(),
        r.0.constant().register_id == r.1.id(),
;

} // verus!
