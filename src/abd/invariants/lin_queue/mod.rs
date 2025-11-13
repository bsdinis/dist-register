use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;
#[allow(unused_imports)]
use vstd::tokens::map::GhostMapAuth;
#[allow(unused_imports)]
use vstd::tokens::map::GhostPointsTo;

#[allow(unused_imports)]
use vstd::assert_by_contradiction;
use vstd::prelude::*;

mod completed;
mod maybe_lin;
mod pending;

pub use completed::Completed;
pub use maybe_lin::MaybeLinearized;
pub use pending::Pending;

use super::logatom::RegisterRead;

verus! {


pub tracked enum InsertError<ML> {
    WatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked lin: ML,
        // Client token to return to client on error
        tracked client_token: ClientToken
    },
}

impl<ML: MutLinearizer<RegisterWrite>> InsertError<ML> {
    pub proof fn tracked_destruct(tracked self) -> (tracked r: (ML, ClientToken))
        requires self is WatermarkContradiction
        ensures (self->lin, self->client_token) == r
    {
        match self {
            InsertError::WatermarkContradiction { lin, client_token, .. } => (lin, client_token)
        }
    }

    pub proof fn lower_bound(tracked self) -> (tracked r: MonotonicTimestampResource)
        requires self is WatermarkContradiction,
        ensures r == self->watermark_lb
    {
        match self {
            InsertError::WatermarkContradiction { watermark_lb, .. } => watermark_lb
        }
    }
}


/* TODO(read_lin) - Explanation
 *
 * # Summary
 *
 * Read linearizers need to be included in the linearization queue
 *
 * # The problem
 * This is part due to the fact that if there is a read concurrent with a write, it might happen
 * that:
 *  - when the read reaches a quorum, it is unanimous
 *  - before the read returns to the client, the other write comes in and finishes and linearizes
 *  - when the read wants to run the linearizer, the ghost state (top of the queue) does not match
 *    the value the read wants to linearize to.
 *
 * # The solution
 *
 * The queue would map to a TLinearizer<ML, RL>
 *
 * TLinearizer<ML, RL> {
 *      write: MaybeLinearized<ML>,
 *      reads: Seq<MaybeLinearized<RL>>,
 * }
 *
 * Note: maybe we need it to be a set? how to count how many reads have been linearized?
 *
 * The watermark now is of the form (ts: TS, n: int), where
 * ts is the timestamp of the last linearized write and n is the number of reads
 * to that write that have been linearized.
 *
 * Invariants regarding this read linearizer.
 *
 * - watermark.ts > ts ==> write[ts] is applied
 *      watermark.ts > ts ==> all read[ts] are applied
 *
 * - watermark.ts < ts <==> write[ts] is not applied ==> all read[ts] are not applied
 *
 * - watermark.ts == ts ==> write[ts] is applied
 *      watermark.ts ==> some read[ts] may be applied
 */
pub struct LinearizationQueue<ML, RL, MC, RC> {
    // value history
    pub history: Map<Timestamp, Option<u64>>,

    // completed operations
    pub completed_writes: Map<Timestamp, Completed<ML, MC, RegisterWrite>>,

    // completed operations
    pub completed_reads: Map<(Timestamp, nat), Completed<RL, RC, RegisterRead>>,

    // pending operations
    pub pending_writes: Map<Timestamp, Pending<ML, RegisterWrite>>,

    // completed operations
    pub pending_reads: Map<(Timestamp, nat), Pending<RL, RegisterRead>>,

    // Why we need a token maps in addition to the completed + pending operations
    //
    // The values in the completed + pending are possibly all changed with apply_linearizer
    // This would require all Tokens to be passed, which is impossible

    pub write_token_map: GhostMapAuth<Timestamp, (ML, RegisterWrite)>,
    pub read_token_map: GhostMapAuth<(Timestamp, nat), (RL, RegisterRead)>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,

    // This is the register this lin queue refers to
    pub ghost register_id: int,

    // Id for the client token auth
    pub ghost client_token_auth_id: int,
}

pub type LinWriteToken<ML> = GhostPointsTo<Timestamp, (ML, RegisterWrite)>;
pub type LinReadToken<RL> = GhostPointsTo<(Timestamp, nat), (RL, RegisterRead)>;

pub struct LinQueueIds {
    pub write_token_map_id: int,
    pub read_token_map_id: int,
    pub watermark_id: int,
    pub register_id: int,
    pub client_token_auth_id: int,
}

impl<ML, RL> LinearizationQueue<ML, RL, ML::Completion, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    pub proof fn dummy(register_id: int, client_token_auth_id: int) -> (tracked result: Self)
        ensures
            result.inv(),
            result.register_id == register_id,
            result.client_token_auth_id == client_token_auth_id,
            result.watermark@.timestamp() == (Timestamp { seqno: 0, client_id: 0 }),
            result.history[Timestamp { seqno: 0, client_id: 0 }] == None::<u64>,
    {
        let tracked history = {
            let tracked mut m = Map::tracked_empty();
            m.tracked_insert(Timestamp { seqno: 0, client_id: 0 }, None);
            m
        };
        let tracked completed_writes = Map::tracked_empty();
        let tracked completed_reads = Map::tracked_empty();
        let tracked pending_writes = Map::tracked_empty();
        let tracked pending_reads = Map::tracked_empty();
        let tracked write_token_map = GhostMapAuth::new(Map::empty()).0;
        let tracked read_token_map = GhostMapAuth::new(Map::empty()).0;
        assert(write_token_map@.dom() == completed_writes.dom().union(pending_writes.dom()));
        assert(read_token_map@.dom() == completed_reads.dom().union(pending_reads.dom()));
        let tracked watermark = MonotonicTimestampResource::alloc();
        LinearizationQueue {
            history,
            completed_writes,
            completed_reads,
            pending_writes,
            pending_reads,
            write_token_map,
            read_token_map,
            watermark,
            register_id,
            client_token_auth_id,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.watermark@ is FullRightToAdvance
        &&& self.write_token_map@.dom().finite()
        &&& self.read_token_map@.dom().finite()
        &&& self.completed_writes.dom().finite()
        &&& self.completed_reads.dom().finite()
        &&& self.pending_writes.dom().finite()
        &&& self.pending_reads.dom().finite()
        &&& self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom())
        &&& self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom())
        &&& forall |ts: Timestamp| self.completed_writes.contains_key(ts) ==> {
            let comp = self.completed_writes[ts];
            &&& ts <= self.watermark@.timestamp()
            &&& comp.timestamp == ts
            &&& comp.inv()
            &&& comp.client_token.id() == self.client_token_auth_id
            &&& comp.op.id == self.register_id
            &&& self.write_token_map@[ts] == (comp.lin, comp.op)
        }
        &&& forall |ts: Timestamp| self.pending_writes.contains_key(ts) ==> {
            let pending = self.pending_writes[ts];
            &&& ts > self.watermark@.timestamp()
            &&& pending.timestamp == ts
            &&& pending.inv()
            &&& pending.client_token.id() == self.client_token_auth_id
            &&& pending.op.id == self.register_id
            &&& self.write_token_map@[ts] == (pending.lin, pending.op)
            &&& !pending.lin.namespaces().contains(super::state_inv_id())
        }
    }

    pub open spec fn ids(self) -> LinQueueIds {
        LinQueueIds {
            write_token_map_id: self.write_token_map.id(),
            read_token_map_id: self.read_token_map.id(),
            watermark_id: self.watermark.loc(),
            register_id: self.register_id,
            client_token_auth_id: self.client_token_auth_id,
        }
    }

    pub proof fn tracked_watermark(tracked &self) -> (tracked r: &MonotonicTimestampResource) {
        &self.watermark
    }

    /// Inserts the linearizer into the linearization queue
    pub proof fn insert_linearizer(tracked &mut self,
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
        tracked mut client_token: ClientToken,
    ) -> (tracked r: Result<LinWriteToken<ML>, InsertError<ML>>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id,
            client_token.id() == old(self).client_token_auth_id,
            timestamp.client_id == client_token@,
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).write_token_map@.dom() <= self.write_token_map@.dom(),
            old(self).watermark == self.watermark,
            r is Ok ==> ({
                let token = r->Ok_0;
                &&& token.key() == timestamp
                &&& token.value() == (lin, op)
                &&& token.id() == self.write_token_map.id()
                &&& self.write_token_map@.len() == old(self).write_token_map@.len() + 1
                &&& self.pending_writes.contains_key(token.key())
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let watermark_lb = r->Err_0->watermark_lb;
                &&& old(self) == self
                &&& err is WatermarkContradiction
                &&& err->lin == lin
                &&& err->client_token == client_token
                &&& watermark_lb@.timestamp() >= timestamp
                &&& watermark_lb.loc() == self.watermark.loc()
                &&& watermark_lb@ is LowerBound
            })
    {
        if self.watermark@.timestamp() >= timestamp {
            return Err(InsertError::WatermarkContradiction {
                watermark_lb: self.watermark.extract_lower_bound(),
                lin,
                client_token
            });
        }

        // check uniqueness by deriving contradiction
        if self.write_token_map@.contains_key(timestamp) {
            let tracked duptok = if self.completed_writes.contains_key(timestamp) {
                self.completed_writes.tracked_remove(timestamp).client_token
            } else {
                self.pending_writes.tracked_remove(timestamp).client_token
            };

            // This is surprisingly not needed, but clarifies what the contradiction is
            assert(client_token@ == duptok@);
            client_token.disjoint(&duptok);
            // CONTRADICTION
        }

        let ghost v = (lin, op);
        let tracked pending = Pending::new(lin, client_token, op, timestamp);

        self.pending_writes.tracked_insert(timestamp, pending);
        let tracked lin_token = self.write_token_map.insert(timestamp, v);
        // load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        lin_token.lemma_view();

        Ok(lin_token)
    }

    pub open spec fn pending_lins_up_to(self,
        max_timestamp: Timestamp
    ) -> (r: Set<Timestamp>)
        recommends self.inv()
    {
        self.pending_writes.dom().filter(|ts: Timestamp| ts <= max_timestamp)
    }

    proof fn lemma_pending_lins(self, max_timestamp: Timestamp)
        requires
            self.inv(),
        ensures
            self.pending_lins_up_to(max_timestamp).finite(),
            self.pending_lins_up_to(max_timestamp) <= self.pending_writes.dom(),
            self.pending_lins_up_to(max_timestamp).len() <= self.pending_writes.dom().len(),
    {
        self.pending_writes.dom().lemma_len_filter(|ts: Timestamp| ts <= max_timestamp);
    }

    /// Applies the linearizer for all writes prophecized to <= timestamp
    pub proof fn apply_linearizers_up_to(tracked &mut self,
        tracked mut register: GhostVarAuth<Option<u64>>,
        max_timestamp: Timestamp
    ) -> (tracked r: (MonotonicTimestampResource, GhostVarAuth<Option<u64>>))
        requires
            old(self).inv(),
            register.id() == old(self).register_id,
        ensures
            // invariants + ids
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).write_token_map@.dom() == self.write_token_map@.dom(),
            register.id() == r.1.id(),
            self.watermark.loc() == r.0.loc(),

            // post-condition changes
            old(self).write_token_map@.dom() == self.write_token_map@.dom(),
            self.write_token_map@.contains_key(max_timestamp) ==> ({
                &&& max_timestamp > old(self).watermark@.timestamp() ==> self.watermark@.timestamp() == max_timestamp
                &&& max_timestamp <= old(self).watermark@.timestamp() ==> self.watermark == old(self).watermark
            }),
            self.pending_lins_up_to(max_timestamp).len() == 0,

            // return values
            r.0@.timestamp() == self.watermark@.timestamp(),
            r.0@ is LowerBound,
            r.1.id() == register.id(),
        decreases
            old(self).pending_lins_up_to(max_timestamp).len()
        opens_invariants
            Set::new(|id: int| id != super::state_inv_id())
    {
        let pending_lins = self.pending_lins_up_to(max_timestamp);
        self.lemma_pending_lins(max_timestamp);
        // assert(pending_lins.finite());

        if pending_lins.len() == 0 {
            if self.pending_writes.contains_key(max_timestamp) {
                assert_by_contradiction!(self.watermark@.timestamp() >= max_timestamp,
                {
                    assert(self.pending_lins_up_to(max_timestamp).contains(max_timestamp)); // trigger
                });
            }
            return (self.watermark.extract_lower_bound(), register);
        }

        let ts_leq = |a: Timestamp, b: Timestamp| a <= b;
        let next_ts = pending_lins.find_unique_minimal(ts_leq);
        pending_lins.find_unique_minimal_ensures(ts_leq);

        // take linearizer, apply, move watermark, place in completed
        let tracked pending = self.pending_writes.tracked_remove(next_ts);
        let tracked completed = pending.apply_linearizer(&mut register, next_ts);

        let ghost old_watermark = self.watermark@.timestamp();
        self.watermark.advance(next_ts);

        self.completed_writes.tracked_insert(completed.timestamp, completed);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        assert forall |ts: Timestamp|
        {
            &&& self.pending_writes.contains_key(ts)
        } implies ts > self.watermark@.timestamp() by {
            assert_by_contradiction!(ts > self.watermark@.timestamp(), {
                if ts > old_watermark && ts < next_ts {
                    pending_lins.lemma_minimal_equivalent_least(ts_leq, next_ts);
                    assert(ts_leq(next_ts, ts)); // CONTRADICTION
                }
            });
        }

        // XXX: load bearing assert
        assert(self.pending_lins_up_to(max_timestamp) == old(self).pending_lins_up_to(max_timestamp).remove(next_ts));
        self.apply_linearizers_up_to(register, max_timestamp)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_completion(tracked &mut self,
        tracked token: LinWriteToken<ML>,
        tracked resource: MonotonicTimestampResource
    ) -> (tracked r: (ML::Completion, ClientToken))
        requires
            old(self).inv(),
            old(self).watermark@.timestamp() >= resource@.timestamp(),
            token.id() == old(self).write_token_map.id(),
            resource@.timestamp() >= token.key(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            self.write_token_map@ == old(self).write_token_map@.remove(token.key()),
            self.completed_writes == old(self).completed_writes.remove(token.key()),
            ({
                let (lin, op) = token.value();
                lin.post(op, (), r.0)
            }),
            // return values
            r.1@ == token.key().client_id,
            r.1.id() == self.client_token_auth_id,
    {
        token.agree(&self.write_token_map);

        let tracked completed = self.completed_writes.tracked_remove(token.key());
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        (completed.completion, completed.client_token)
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_lin(tracked &mut self,
        tracked token: LinWriteToken<ML>,
    ) -> (tracked r: (MaybeLinearized<ML, ML::Completion, RegisterWrite>, ClientToken))
        requires
            old(self).inv(),
            token.id() == old(self).write_token_map.id(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            self.write_token_map@ == old(self).write_token_map@.remove(token.key()),
            r.1@ == token.key().client_id,
            r.1.id() == self.client_token_auth_id,
            token.value().0 == r.0.lin(),
            token.value().1 == r.0.op(),
    {
        token.agree(&self.write_token_map);

        let tracked (lincomp, client_token) = if token.key() <= self.watermark@.timestamp() {
            self.completed_writes.tracked_remove(token.key()).maybe()
        } else {
            self.pending_writes.tracked_remove(token.key()).maybe()
        };
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        (lincomp, client_token)
    }

    /// Show that if we have a token for a key, then it exists
    pub proof fn lemma_token_is_in_queue(tracked &self, tracked token: &LinWriteToken<ML>)
        requires
            self.inv(),
            token.id() == self.write_token_map.id(),
        ensures
            ({
                ||| self.pending_writes.contains_key(token.key())
                ||| self.completed_writes.contains_key(token.key())
            })
    {
        token.agree(&self.write_token_map);
    }
}

}

impl<ML: MutLinearizer<RegisterWrite>> std::fmt::Debug for InsertError<ML> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::WatermarkContradiction { .. } => f.write_str("WatermarkContradiction"),
        }
    }
}
