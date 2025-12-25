//! Infrastructure of committed to values by clients
//!
//! In general, the way this happens is:
//! - Clients get access to their entire timestamp range
//! - When the timestamp is known, the client can commit to a value by persisting the kv-pair
#![allow(dead_code)]
use vstd::atomic::PermissionU64;
use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostPersistentPointsTo;
#[allow(unused_imports)]
use vstd::tokens::map::GhostPersistentSubmap;
use vstd::tokens::map::GhostPointsTo;

use crate::abd::proto::Timestamp;

use vstd::prelude::*;

verus! {

pub type WriteCommitment = GhostPersistentPointsTo<Timestamp, Option<u64>>;

pub type WriteAllocation = GhostPointsTo<Timestamp, Option<u64>>;

pub type CommitmentAuthMap = GhostMapAuth<Timestamp, Option<u64>>;

pub type ClientCtrToken = GhostPointsTo<u64, (u64, int)>;

pub struct Commitments {
    commitment_auth: GhostMapAuth<Timestamp, Option<u64>>,
    client_ctr_auth: GhostMapAuth<u64, (u64, int)>,
    client_perm: Map<u64, PermissionU64>,
    zero_client: ClientCtrToken,
    ghost missing_perm: Option<(u64, int)>,
}

pub struct CommitmentIds {
    pub commitment_id: int,
    pub client_ctr_id: int,
}

impl Commitments {
    // TODO(type_inv): move this type to having a #[verifier::type_invariant]
    // Problem: verus does not supoprt opening the type invariant. which precludes maintaining the type
    // Without it, there is no way of atomically update members here
    pub closed spec fn inv(self) -> bool {
        &&& self.commitment_auth@.contains_pair(Timestamp::spec_default(), None)
        &&& self.missing_perm is None ==> { self.client_ctr_auth@.dom() == self.client_perm.dom() }
        &&& self.missing_perm is Some ==> {
            let missing_client = self.missing_perm->Some_0.0;
            self.client_ctr_auth@.dom() == self.client_perm.dom().insert(missing_client)
        }
        &&& forall|client_id: u64|
            {
                &&& self.client_ctr_auth@.contains_key(client_id)
                &&& self.client_perm.contains_key(client_id)
            } ==> {
                &&& self.client_ctr_auth@[client_id].0 == self.client_perm[client_id].value()
                &&& self.client_ctr_auth@[client_id].1 == self.client_perm[client_id].id()
            }
        &&& forall|ts: Timestamp|
            self.commitment_auth@.contains_key(ts) ==> {
                &&& self.client_ctr_auth@.contains_key(ts.client_id)
                &&& ts.client_ctr < self.client_ctr_auth@[ts.client_id].0
            }
            // client 0 is reserved for the original write -- it never writes anything else
        &&& self.zero_client.id() == self.client_map_id()
        &&& self.zero_client.key() == 0
        &&& self.zero_client.value().0 == 1
        &&& self.client_perm.contains_key(0)  // 0 cannot be missing

    }

    pub open spec fn ids(self) -> CommitmentIds {
        CommitmentIds { commitment_id: self.commitment_id(), client_ctr_id: self.client_map_id() }
    }

    pub closed spec fn is_full(self) -> bool {
        self.missing_perm is None
    }

    pub closed spec fn missing_perm(self) -> (u64, int)
        recommends
            !self.is_full(),
    {
        self.missing_perm->Some_0
    }

    pub closed spec fn commitment_id(self) -> int {
        self.commitment_auth.id()
    }

    pub closed spec fn client_map_id(self) -> int {
        self.client_ctr_auth.id()
    }

    pub closed spec fn allocated(self) -> Map<Timestamp, Option<u64>> {
        self.commitment_auth.view()
    }

    pub closed spec fn client_map(self) -> Map<u64, (u64, int)> {
        self.client_ctr_auth@
    }

    pub closed spec fn client_perm(self) -> Map<u64, PermissionU64> {
        self.client_perm
    }

    pub proof fn new(tracked zero_perm: PermissionU64) -> (tracked r: (
        Commitments,
        WriteCommitment,
    ))
        requires
            zero_perm.value() == 1,
        ensures
            r.0.is_full(),
            r.0.inv(),
            r.0.commitment_id() == r.1.id(),
            r.0.allocated() == map![Timestamp::spec_default() => None::<u64>],
            r.0.client_map() == map![0u64 => (1u64, zero_perm.id())],
            r.0.client_perm() == map![0u64 => zero_perm],
            r.1.key() == Timestamp::spec_default(),
            r.1.value() == None::<u64>,
    {
        let tracked (commitment_auth, zero_submap) = GhostMapAuth::new(
            map![Timestamp::spec_default() => None],
        );
        let tracked mut zero_commitment = zero_submap.points_to();
        zero_commitment.agree(&commitment_auth);

        let tracked (client_ctr_auth, zero_client_submap) = GhostMapAuth::new(
            map![0 => (1, zero_perm.id())],
        );
        let tracked mut zero_client = zero_client_submap.points_to();
        zero_client.agree(&client_ctr_auth);

        let tracked mut client_perm = Map::tracked_empty();
        client_perm.tracked_insert(0u64, zero_perm);

        let tracked commitments = Commitments {
            commitment_auth,
            client_ctr_auth,
            client_perm,
            zero_client,
            missing_perm: None,
        };
        (commitments, zero_commitment.persist())
    }

    pub proof fn login(
        tracked &mut self,
        client_id: u64,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: ClientCtrToken)
        requires
            old(self).inv(),
            old(self).is_full(),
            !old(self).client_map().contains_key(client_id),
            client_perm.value() == 0,
        ensures
            self.inv(),
            self.is_full(),
            self.ids() == old(self).ids(),
            self.allocated() == old(self).allocated(),
            self.client_map() == old(self).client_map().insert(client_id, (0, client_perm.id())),
            self.client_perm() == old(self).client_perm().insert(client_id, client_perm),
            r.id() == self.client_map_id(),
            r.key() == client_id,
            r.value().0 == 0,
            r.value().1 == client_perm.id(),
    {
        let ghost client_perm_id = client_perm.id();
        self.client_perm.tracked_insert(client_id, client_perm);
        self.client_ctr_auth.insert(client_id, (0, client_perm_id))
    }

    pub proof fn take_permission(
        tracked &mut self,
        tracked client_token: &ClientCtrToken,
    ) -> (tracked r: PermissionU64)
        requires
            old(self).inv(),
            old(self).is_full(),
            client_token.id() == old(self).client_map_id(),
        ensures
            self.inv(),
            !self.is_full(),
            self.ids() == old(self).ids(),
            self.missing_perm() == (client_token.key(), r.id()),
            self.allocated() == old(self).allocated(),
            self.client_map() == old(self).client_map(),
            self.client_perm() == old(self).client_perm().remove(client_token.key()),
            r == old(self).client_perm()[client_token.key()],
            r.id() == client_token.value().1,
            r.value() == client_token.value().0,
    {
        assert(client_token.id() == self.client_map_id());
        assert(self.zero_client.id() == self.client_map_id());
        client_token.agree(&self.client_ctr_auth);
        self.zero_client.disjoint(client_token);
        let tracked r = self.client_perm.tracked_remove(client_token.key());
        self.missing_perm = Some((client_token.key(), r.id()));
        r
    }

    pub proof fn alloc_value(
        tracked &mut self,
        tracked client_token: &mut ClientCtrToken,
        timestamp: Timestamp,
        value: Option<u64>,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: WriteAllocation)
        requires
            old(self).inv(),
            !old(self).is_full(),
            old(client_token).id() == old(self).client_map_id(),
            old(self).missing_perm() == (old(client_token).key(), client_perm.id()),
            timestamp.client_id == old(client_token).key(),
            timestamp.client_ctr == old(client_token).value().0,
            timestamp.client_ctr < client_perm.value(),
            client_perm.id() == old(client_token).value().1,
        ensures
            self.inv(),
            self.is_full(),
            self.ids() == old(self).ids(),
            !old(self).allocated().contains_key(timestamp),
            self.allocated() == old(self).allocated().insert(timestamp, value),
            self.client_map() == old(self).client_map().insert(
                timestamp.client_id,
                (client_perm.value(), client_perm.id()),
            ),
            self.client_perm() == old(self).client_perm().insert(timestamp.client_id, client_perm),
            client_token.id() == old(client_token).id(),
            client_token.key() == old(client_token).key(),
            client_token.value().0 == client_perm.value(),
            client_token.value().1 == client_perm.id(),
            r.key() == timestamp,
            r.value() == value,
            r.id() == self.commitment_id(),
    {
        client_token.agree(&self.client_ctr_auth);
        client_token.disjoint(&self.zero_client);
        client_token.update(&mut self.client_ctr_auth, (client_perm.value(), client_perm.id()));

        // XXX: load bearing
        assert(self.client_perm.dom().insert(self.missing_perm->Some_0.0)
            == self.client_ctr_auth@.dom());

        self.client_perm.tracked_insert(client_token.key(), client_perm);
        self.missing_perm = None;
        self.commitment_auth.insert(timestamp, value)
    }

    pub proof fn return_permission(
        tracked &mut self,
        tracked client_token: &mut ClientCtrToken,
        tracked client_perm: PermissionU64,
    )
        requires
            old(self).inv(),
            !old(self).is_full(),
            old(client_token).id() == old(self).client_map_id(),
            old(self).missing_perm() == (old(client_token).key(), client_perm.id()),
            old(client_token).value().0 < client_perm.value(),
            old(client_token).value().1 == client_perm.id(),
        ensures
            self.inv(),
            self.is_full(),
            self.ids() == old(self).ids(),
            self.allocated() == old(self).allocated(),
            self.client_map() == old(self).client_map().insert(
                client_token.key(),
                (client_perm.value(), client_perm.id()),
            ),
            self.client_perm() == old(self).client_perm().insert(client_token.key(), client_perm),
            client_token.id() == old(client_token).id(),
            client_token.key() == old(client_token).key(),
            client_token.value().0 == client_perm.value(),
            client_token.value().1 == client_perm.id(),
    {
        client_token.agree(&self.client_ctr_auth);
        client_token.disjoint(&self.zero_client);
        client_token.update(&mut self.client_ctr_auth, (client_perm.value(), client_perm.id()));

        // XXX: load bearing
        assert(self.client_perm.dom().insert(self.missing_perm->Some_0.0)
            == self.client_ctr_auth@.dom());

        self.client_perm.tracked_insert(client_token.key(), client_perm);
        self.missing_perm = None;
    }

    pub proof fn agree_commitment(tracked &self, tracked commitment: &WriteCommitment)
        requires
            self.inv(),
            self.is_full(),
            commitment.id() == self.commitment_id(),
        ensures
            self.allocated().contains_key(commitment.key()),
    {
        commitment.agree(&self.commitment_auth);
    }

    pub proof fn agree_commitment_submap(
        tracked &self,
        tracked commitments: &GhostPersistentSubmap<Timestamp, Option<u64>>,
    )
        requires
            self.inv(),
            self.is_full(),
            commitments.id() == self.commitment_id(),
        ensures
            commitments@ <= self.allocated(),
    {
        commitments.agree(&self.commitment_auth);
    }

    pub proof fn agree_allocation(tracked &self, tracked allocation: &WriteAllocation)
        requires
            self.inv(),
            self.is_full(),
            allocation.id() == self.commitment_id(),
        ensures
            self.allocated().contains_key(allocation.key()),
    {
        allocation.agree(&self.commitment_auth);
    }

    pub proof fn remove_allocation(
        tracked &mut self,
        tracked allocation: WriteAllocation,
        tracked client_ctr_token: &ClientCtrToken,
    )
        requires
            old(self).inv(),
            old(self).is_full(),
            allocation.id() == old(self).commitment_id(),
            client_ctr_token.id() == old(self).client_map_id(),
            allocation.key().client_id == client_ctr_token.key(),
        ensures
            self.inv(),
            self.is_full(),
            self.ids() == old(self).ids(),
            self.allocated() == old(self).allocated().remove(allocation.key()),
    {
        client_ctr_token.agree(&self.client_ctr_auth);
        self.zero_client.disjoint(client_ctr_token);
        allocation.agree(&self.commitment_auth);
        self.commitment_auth.delete_points_to(allocation);
    }

    pub proof fn agree_client_token(tracked &self, tracked client_ctr_token: &ClientCtrToken)
        requires
            self.inv(),
            self.is_full(),
            client_ctr_token.id() == self.client_map_id(),
        ensures
            self.client_map().contains_key(client_ctr_token.key()),
    {
        client_ctr_token.agree(&self.client_ctr_auth);
    }
}

} // verus!
