//! Infrastructure of committed to values by clients
//!
//! In general, the way this happens is:
//! - Clients get access to their entire timestamp range
//! - When the timestamp is known, the client can commit to a value by persisting the kv-pair

use vstd::assert_by_contradiction;
use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostPersistentPointsTo;
use vstd::tokens::map::GhostPointsTo;
use vstd::tokens::map::GhostSubmap;

use crate::abd::proto::Timestamp;

use vstd::prelude::*;

verus! {

pub type WriteCommitment = GhostPersistentPointsTo<Timestamp, Option<u64>>;
pub type WriteAllocation = GhostPointsTo<Timestamp, Option<u64>>;
pub type CommitmentAuthMap = GhostMapAuth<Timestamp, Option<u64>>;
pub type ClientSeqnoToken = GhostPointsTo<u64, u64>;

pub struct Commitments {
    pub commitment_auth: GhostMapAuth<Timestamp, Option<u64>>,
    pub client_max_seqno: GhostMapAuth<u64, u64>,
    pub zero_client: GhostPointsTo<u64, u64>,
}

pub struct CommitmentIds {
    pub commitment_id: int,
    pub client_map_id: int,
}

impl Commitments {
    pub open spec fn inv(self) -> bool {
        &&& self.commitment_auth@.contains_pair(Timestamp { client_id: 0, seqno: 0 }, None)
        &&& forall |ts: Timestamp| self.commitment_auth@.contains_key(ts) ==> {
            &&& self.client_max_seqno@.contains_key(ts.client_id)
            &&& ts.seqno <= self.client_max_seqno@[ts.client_id]
        }
        // client 0 is reserved for the original write -- it never writes anything else
        &&& self.zero_client@ == (0u64, 0u64)
        &&& self.zero_client.id() == self.client_map_id()
    }

    pub open spec fn ids(self) -> CommitmentIds {
        CommitmentIds {
            commitment_id: self.commitment_auth.id(),
            client_map_id: self.client_max_seqno.id(),
        }
    }

    pub open spec fn commitment_id(self) -> int {
        self.commitment_auth.id()
    }

    pub open spec fn client_map_id(self) -> int {
        self.client_max_seqno.id()
    }

    pub open spec fn view(self) -> Map<Timestamp, Option<u64>> {
        self.commitment_auth.view()
    }

    pub proof fn new() -> (tracked r: (Commitments, WriteCommitment))
        ensures
            r.0.inv(),
            r.0.commitment_id() == r.1.id(),
            r.0.commitment_auth@ == map![Timestamp { client_id: 0, seqno: 0 } => None::<u64>],
            r.0.client_max_seqno@ == map![0u64 => 0u64],
            r.1.key() == (Timestamp { client_id: 0, seqno: 0 }),
            r.1.value() == None::<u64>
    {
        let tracked (commitment_auth, zero_submap) = GhostMapAuth::new(map![Timestamp { client_id: 0, seqno: 0 } => None]);
        let tracked mut zero_commitment = zero_submap.points_to();
        zero_commitment.agree(&commitment_auth);

        let tracked (client_max_seqno, zero_client_submap) = GhostMapAuth::new(map![0 => 0]);
        let tracked mut zero_client = zero_client_submap.points_to();
        zero_client.agree(&client_max_seqno);

        let tracked commitments = Commitments {
            commitment_auth,
            client_max_seqno,
            zero_client,
        };
        (commitments, zero_commitment.persist())
    }

    // TODO: must this be a monotonic increasing value?
    pub proof fn login(tracked &mut self, client_id: u64) -> (tracked r: GhostPointsTo<u64, u64>)
        requires
            old(self).inv(),
            !old(self).client_max_seqno@.contains_key(client_id),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.client_max_seqno@ == old(self).client_max_seqno@.insert(client_id, 0),
            self.commitment_auth@ == old(self).commitment_auth@,
            r.id() == self.client_map_id(),
            r.key() == client_id,
            r.value() == 0,
    {
        self.client_max_seqno.insert(client_id, 0)
    }

    pub proof fn alloc_value(tracked &mut self,
        tracked client_token: &mut ClientSeqnoToken,
        timestamp: Timestamp,
        value: Option<u64>
    ) -> (tracked r: WriteAllocation)
        requires
            old(self).inv(),
            old(client_token).id() == old(self).client_map_id(),
            timestamp.seqno > old(client_token).value(),
            timestamp.client_id == old(client_token).key(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.client_max_seqno@ == old(self).client_max_seqno@.insert(timestamp.client_id, timestamp.seqno),
            self.commitment_auth@ == old(self).commitment_auth@.insert(timestamp, value),
            client_token.id() == old(client_token).id(),
            client_token.key() == old(client_token).key(),
            client_token.value() == timestamp.seqno,
            r.key() == timestamp,
            r.value() == value,
            r.id() == self.commitment_id(),
    {
        client_token.agree(&self.client_max_seqno);
        client_token.disjoint(&self.zero_client);
        client_token.update(&mut self.client_max_seqno, timestamp.seqno);
        self.commitment_auth.insert(timestamp, value)
    }

    pub proof fn update_seqno(tracked &mut self, tracked client_token: &mut ClientSeqnoToken, seqno: u64)
        requires
            old(self).inv(),
            old(client_token).id() == old(self).client_map_id(),
            seqno > old(client_token).value()
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.commitment_auth@ == old(self).commitment_auth@,
            self.client_max_seqno@ == old(self).client_max_seqno@.insert(client_token.key(), client_token.value()),
            client_token.id() == old(client_token).id(),
            client_token.key() == old(client_token).key(),
            client_token.value() == if seqno < old(client_token).value() {
                old(client_token).value()
            } else {
                seqno
            },
    {
        client_token.agree(&self.client_max_seqno);
        client_token.disjoint(&self.zero_client);
        let ghost new_value = if seqno < client_token.value() {
            client_token.value()
        } else {
            seqno
        };
        client_token.update(&mut self.client_max_seqno, new_value);
    }
}

}
