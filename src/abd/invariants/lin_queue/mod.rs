use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
#[allow(unused_imports)]
use vstd::set_lib::*;
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

pub use completed::CompletedRead;
pub use completed::CompletedWrite;
pub use maybe_lin::MaybeReadLinearized;
pub use maybe_lin::MaybeWriteLinearized;
pub use pending::PendingRead;
pub use pending::PendingWrite;

use super::logatom::RegisterRead;

verus! {


pub tracked enum InsertError<ML, RL> {
    WriteWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked w_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked w_lin: ML,
        // Client token to return to client on error
        tracked client_token: ClientToken
    },
    ReadWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked r_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked r_lin: RL,
    },
}

impl<ML, RL> InsertError<ML, RL> {
    pub proof fn tracked_write_destruct(tracked self) -> (tracked r: (ML, ClientToken))
        requires self is WriteWatermarkContradiction
        ensures (self->w_lin, self->client_token) == r
    {
        match self {
            InsertError::WriteWatermarkContradiction { w_lin, client_token, .. } => (w_lin, client_token),
            _ => proof_from_false(),
        }
    }

    pub proof fn tracked_read_destruct(tracked self) -> (tracked r: RL)
        requires self is ReadWatermarkContradiction
        ensures self->r_lin == r
    {
        match self {
            InsertError::ReadWatermarkContradiction { r_lin, .. } => r_lin,
            _ => proof_from_false(),
        }
    }

    pub proof fn lower_bound(tracked self) -> (tracked r: MonotonicTimestampResource)
        requires
        ({
            ||| self is WriteWatermarkContradiction
            ||| self is ReadWatermarkContradiction
        }),
        ensures
            self is WriteWatermarkContradiction ==> r == self->w_watermark_lb,
            self is ReadWatermarkContradiction ==> r == self->r_watermark_lb,
    {
        match self {
            InsertError::WriteWatermarkContradiction { w_watermark_lb, .. } => w_watermark_lb,
            InsertError::ReadWatermarkContradiction { r_watermark_lb, .. } => r_watermark_lb,
        }
    }
}

pub struct LinearizationQueue<ML, RL, MC, RC> {
    // value history
    pub history: Map<Timestamp, Option<u64>>,

    // completed operations
    pub completed_writes: Map<Timestamp, CompletedWrite<ML, MC>>,

    // completed operations
    pub completed_reads: Map<(Option<u64>, nat), CompletedRead<RL, RC>>,

    // pending operations
    pub pending_writes: Map<Timestamp, PendingWrite<ML>>,

    // completed operations
    pub pending_reads: Map<(Option<u64>, nat), PendingRead<RL>>,

    // Why we need a token maps in addition to the completed + pending operations
    //
    // The values in the completed + pending are possibly all changed with apply_linearizer
    // This would require all Tokens to be passed, which is impossible

    pub write_token_map: GhostMapAuth<Timestamp, (ML, RegisterWrite)>,
    pub read_token_map: GhostMapAuth<(Option<u64>, nat), ReadTokenVal<RL>>,

    // counter for next read op
    pub next_read_op: nat,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,

    // This is the register this lin queue refers to
    pub ghost register_id: int,

    // Id for the client token auth
    pub ghost client_token_auth_id: int,
}

pub type LinWriteToken<ML> = GhostPointsTo<Timestamp, (ML, RegisterWrite)>;

pub type LinReadToken<RL> = GhostPointsTo<(Option<u64>, nat), ReadTokenVal<RL>>;

pub struct ReadTokenVal<RL> {
    pub ghost lin: RL,
    pub ghost op: RegisterRead,
    pub tracked min_ts: MonotonicTimestampResource,
}

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
            next_read_op: 0,
            watermark,
            register_id,
            client_token_auth_id,
        }
    }

    // basic invariant
    // - always true, asserts facts that are always true
    pub open spec fn basic_inv(&self) -> bool {
        &&& self.watermark@ is FullRightToAdvance
        &&& self.write_token_map@.dom().finite()
        &&& self.read_token_map@.dom().finite()
        &&& self.completed_writes.dom().finite()
        &&& self.completed_reads.dom().finite()
        &&& self.pending_writes.dom().finite()
        &&& self.pending_reads.dom().finite()
        &&& self.history.contains_key(self.watermark@.timestamp())
        &&& forall|ts: Timestamp|
            self.history.contains_key(ts) ==> ts <= self.watermark@.timestamp()
    }

    // full invariant over the write domain:
    //  1. the completed_writes + pending_writes match the write token domain
    //  2. everything below the watermark is completed, and matches the correct ids
    //  3. completed writes match the history
    //  4. everything above the watermark is pending and matches the correct ids
    pub open spec fn write_dom_inv(&self) -> bool {
        &&& self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom())
        &&& forall |ts: Timestamp| self.completed_writes.contains_key(ts) ==> {
            let comp = self.completed_writes[ts];
            &&& ts <= self.watermark@.timestamp()
            &&& comp.timestamp == ts
            &&& comp.inv()
            &&& comp.token.id() == self.client_token_auth_id
            &&& comp.op.id == self.register_id
            &&& self.write_token_map@[ts] == (comp.lin, comp.op)
            &&& self.history[ts] == comp.op.new_value
        }
        &&& forall |ts: Timestamp| self.pending_writes.contains_key(ts) ==> {
            let pending = self.pending_writes[ts];
            &&& ts > self.watermark@.timestamp()
            &&& pending.timestamp == ts
            &&& pending.inv()
            &&& pending.token.id() == self.client_token_auth_id
            &&& pending.op.id == self.register_id
            &&& self.write_token_map@[ts] == (pending.lin, pending.op)
            &&& !pending.lin.namespaces().contains(super::state_inv_id())
        }
    }

    pub open spec fn read_dom_composition(&self) -> bool {
        &&& self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom())
        &&& self.completed_reads.dom().disjoint(self.pending_reads.dom())
    }

    pub open spec fn read_tok_inv(&self) -> bool {
        forall|key: (Option<u64>, nat)|
            self.read_token_map@.contains_key(key) ==> {
                let tok = self.read_token_map@[key];
                &&& key.1 < self.next_read_op
                &&& tok.min_ts.loc() == self.watermark.loc()
                &&& tok.min_ts@.timestamp() <= self.watermark@.timestamp()
            }
    }

    pub open spec fn read_completed_inv(&self) -> bool {
        forall|key: (Option<u64>, nat)|
            self.completed_reads.contains_key(key) ==> {
                let comp = self.completed_reads[key];
                let token = self.read_token_map@[key];
                &&& comp.inv()
                &&& comp.value == key.0
                &&& comp.op.id == self.register_id
                &&& token.lin == comp.lin
                &&& token.op == comp.op
                &&& token.min_ts@.timestamp() <= comp.timestamp
                &&& comp.timestamp <= self.watermark@.timestamp()
                &&& self.history.contains_key(comp.timestamp)
                &&& self.history[comp.timestamp] == comp.value
            }
    }

    // full invariant over the read domain:
    //  1. the completed_reads + pending_reads match the read token domain
    //  2. every read that has had the opportunity to linearize (i.e., there has appeared a write
    //     with the target value) has
    //  3. everything pending matches the correct ids
    pub open spec fn read_dom_inv(&self) -> bool {
        &&& self.read_dom_composition()
        &&& self.read_tok_inv()
        &&& self.read_completed_inv()
        &&& forall |key: (Option<u64>, nat)| self.pending_reads.contains_key(key) ==> {
            let pending = self.pending_reads[key];
            let token = self.read_token_map@[key];
            &&& pending.inv()
            &&& pending.value == key.0
            &&& pending.op.id == self.register_id
            &&& token.lin == pending.lin
            &&& token.op == pending.op
            &&& forall |ts: Timestamp| token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp() && self.history.contains_key(ts) ==> {
                self.history[ts] != pending.value
            }
            &&& !pending.lin.namespaces().contains(super::state_inv_id())
        }
    }

    // weak invariant over the read domain:
    //  1. the completed_reads + pending_reads match the read token domain
    //  2. every read that has had the opportunity to linearize strictly below the watermark (i.e., there has appeared a write
    //     with the target value) has
    //  3. everything pending matches the correct ids
    pub open spec fn weak_read_dom_inv(&self) -> bool {
        &&& self.read_dom_composition()
        &&& self.read_tok_inv()
        &&& self.read_completed_inv()
        &&& forall |key: (Option<u64>, nat)| self.pending_reads.contains_key(key) ==> {
            let pending = self.pending_reads[key];
            let token = self.read_token_map@[key];
            &&& pending.inv()
            &&& pending.value == key.0
            &&& pending.op.id == self.register_id
            &&& token.lin == pending.lin
            &&& token.op == pending.op
            &&& forall |ts: Timestamp| token.min_ts@.timestamp() <= ts && ts < self.watermark@.timestamp() && self.history.contains_key(ts) ==> {
                self.history[ts] != pending.value
            }
            &&& !pending.lin.namespaces().contains(super::state_inv_id())
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.basic_inv()
        &&& self.write_dom_inv()
        &&& self.read_dom_inv()
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

    pub open spec fn current_value(self) -> Option<u64>
        recommends
            self.basic_inv(),
    {
        self.history[self.watermark@.timestamp()]
    }

    pub proof fn tracked_watermark(tracked &self) -> (tracked r: &MonotonicTimestampResource) {
        &self.watermark
    }

    /// Inserts the mut linearizer into the linearization queue
    pub proof fn insert_write_linearizer(tracked &mut self,
        tracked lin: ML,
        tracked op: RegisterWrite,
        timestamp: Timestamp,
        tracked mut client_token: ClientToken,
    ) -> (tracked r: Result<LinWriteToken<ML>, InsertError<ML, RL>>)
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
            old(self).ids() == self.ids(),
            old(self).write_token_map@.dom() <= self.write_token_map@.dom(),
            old(self).watermark == self.watermark,
            old(self).history == self.history,
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
                let watermark_lb = r->Err_0->w_watermark_lb;
                &&& old(self) == self
                &&& err is WriteWatermarkContradiction
                &&& err->w_lin == lin
                &&& err->client_token == client_token
                &&& watermark_lb@.timestamp() >= timestamp
                &&& watermark_lb.loc() == self.watermark.loc()
                &&& watermark_lb@ is LowerBound
            })
    {
        if self.watermark@.timestamp() >= timestamp {
            return Err(InsertError::WriteWatermarkContradiction {
                w_watermark_lb: self.watermark.extract_lower_bound(),
                w_lin: lin,
                client_token
            });
        }

        // check uniqueness by deriving contradiction
        if self.write_token_map@.contains_key(timestamp) {
            let tracked duptok = if self.completed_writes.contains_key(timestamp) {
                self.completed_writes.tracked_remove(timestamp).token
            } else {
                self.pending_writes.tracked_remove(timestamp).token
            };

            // This is surprisingly not needed, but clarifies what the contradiction is
            assert(client_token@ == duptok@);
            client_token.disjoint(&duptok);
            // CONTRADICTION
        }

        let ghost v = (lin, op);
        let tracked pending = PendingWrite::new(lin, client_token, op, timestamp);

        self.pending_writes.tracked_insert(timestamp, pending);
        let tracked lin_token = self.write_token_map.insert(timestamp, v);
        // load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        lin_token.lemma_view();

        Ok(lin_token)
    }

    /// Inserts the read linearizer into the linearization queue
    pub proof fn insert_read_linearizer(tracked &mut self,
        tracked lin: RL,
        tracked op: RegisterRead,
        value: Option<u64>,
        tracked register: &GhostVarAuth<Option<u64>>,
    ) -> (tracked token: LinReadToken<RL>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id,
            register.id() == old(self).register_id,
            old(self).current_value() == register@,
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).read_token_map@.dom() <= self.read_token_map@.dom(),
            old(self).watermark@ == self.watermark@,
            old(self).history == self.history,
            token.id() == self.read_token_map.id(),
            token.key().0 == value,
            token.value().lin == lin,
            token.value().op == op,
            token.value().min_ts.loc() == self.watermark.loc(),
            self.read_token_map@.len() == old(self).read_token_map@.len() + 1,
            value == self.current_value() ==> self.completed_reads.contains_key(token.key()),
            value != self.current_value() ==> self.pending_reads.contains_key(token.key()),
        opens_invariants
            Set::new(|id: int| id != super::state_inv_id())
    {
        let key = (value, self.next_read_op);
        let tracked v = ReadTokenVal { lin, op, min_ts: self.watermark.extract_lower_bound() };
        self.watermark.lemma_lower_bound(&v.min_ts);

        assert(!self.read_token_map@.contains_key(key));
        assert(!self.pending_reads.contains_key(key));
        assert(!self.completed_reads.contains_key(key));

        let tracked token = self.read_token_map.insert((value, self.next_read_op), v);
        token.lemma_view();
        self.next_read_op = self.next_read_op + 1;

        let tracked mut pending = PendingRead::new(lin, op, value);
        let current_value = self.history[self.watermark@.timestamp()];
        if value == current_value {
            let tracked completed = pending.apply_linearizer(register, self.watermark@.timestamp());
            self.completed_reads.tracked_insert(token.key(), completed);
        } else {
            self.pending_reads.tracked_insert(token.key(), pending);
        }

        // load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

        token
    }

    pub open spec fn pending_writes_up_to(self,
        max_timestamp: Timestamp
    ) -> (r: Set<Timestamp>)
        recommends self.inv()
    {
        self.pending_writes.dom().filter(|ts: Timestamp| ts <= max_timestamp)
    }

    proof fn lemma_pending_writes(self, max_timestamp: Timestamp)
        requires
            self.inv(),
        ensures
            self.pending_writes_up_to(max_timestamp).finite(),
            self.pending_writes_up_to(max_timestamp) <= self.pending_writes.dom(),
            self.pending_writes_up_to(max_timestamp).len() <= self.pending_writes.dom().len(),
    {
        self.pending_writes.dom().lemma_len_filter(|ts: Timestamp| ts <= max_timestamp);
    }

    pub open spec fn pending_reads_with_value(self, value: Option<u64>) -> (r: Set<
        (Option<u64>, nat),
    >)
        recommends
            self.pending_reads.dom().finite(),
            self.inv() || self.history[self.watermark@.timestamp()] == value,
    {
        self.pending_reads.dom().filter(|k: (Option<u64>, nat)| k.0 == value)
    }

    proof fn lemma_pending_reads(self, value: Option<u64>)
        requires
            self.pending_reads.dom().finite(),
            self.inv() || self.history[self.watermark@.timestamp()] == value,
        ensures
            self.pending_reads_with_value(value).finite(),
            self.pending_reads_with_value(value) <= self.pending_reads.dom(),
            self.pending_reads_with_value(value).len() <= self.pending_reads.dom().len(),
            forall|x: (Option<u64>, nat)|
                self.pending_reads_with_value(value).contains(x) ==> x.0 == value,
    {
        self.pending_reads.dom().lemma_len_filter(|k: (Option<u64>, nat)| k.0 == value);
        lemma_len_subset(self.pending_reads_with_value(value), self.pending_reads.dom());
    }

    /// Applies the linearizer for all operations prophecized to <= timestamp
    pub proof fn apply_linearizers_up_to(tracked &mut self,
        tracked mut register: GhostVarAuth<Option<u64>>,
        max_timestamp: Timestamp
    ) -> (tracked r: (MonotonicTimestampResource, GhostVarAuth<Option<u64>>))
        requires
            old(self).inv(),
            register.id() == old(self).register_id,
            old(self).current_value() == register@,
        ensures
            // invariants + ids
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).write_token_map@.dom() == self.write_token_map@.dom(),
            register.id() == r.1.id(),
            self.watermark.loc() == r.0.loc(),
            self.current_value() == r.1@,

            // post-condition changes
            old(self).write_token_map@.dom() == self.write_token_map@.dom(),
            old(self).read_token_map@.dom() == self.read_token_map@.dom(),
            self.write_token_map@.contains_key(max_timestamp) ==> ({
                &&& max_timestamp > old(self).watermark@.timestamp() ==> self.watermark@.timestamp() == max_timestamp
                &&& max_timestamp <= old(self).watermark@.timestamp() ==> self.watermark == old(self).watermark
            }),
            self.pending_writes_up_to(max_timestamp).len() == 0,

            // return values
            r.0@.timestamp() == self.watermark@.timestamp(),
            r.0@ is LowerBound,
            r.1.id() == register.id(),
        decreases
            old(self).pending_writes_up_to(max_timestamp).len()
        opens_invariants
            Set::new(|id: int| id != super::state_inv_id())
    {
        let pending_writes = self.pending_writes_up_to(max_timestamp);
        self.lemma_pending_writes(max_timestamp);
        assert(pending_writes.finite());

        if pending_writes.len() == 0 {
            if self.pending_writes.contains_key(max_timestamp) {
                assert_by_contradiction!(self.watermark@.timestamp() >= max_timestamp,
                {
                    assert(self.pending_writes_up_to(max_timestamp).contains(max_timestamp)); // trigger
                });
            }
            return (self.watermark.extract_lower_bound(), register);
        }


        let ts_leq = |a: Timestamp, b: Timestamp| a <= b;
        let next_ts = pending_writes.find_unique_minimal(ts_leq);
        pending_writes.find_unique_minimal_ensures(ts_leq);

        // take linearizer, apply, move watermark, place in completed
        let tracked pending = self.pending_writes.tracked_remove(next_ts);
        let tracked completed = pending.apply_linearizer(&mut register, next_ts);

        let ghost old_watermark = self.watermark@.timestamp();
        self.watermark.advance(next_ts);
        self.history.tracked_insert(next_ts, completed.op.new_value);
        self.completed_writes.tracked_insert(completed.timestamp, completed);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(self.pending_writes.dom()));

        assert forall |ts: Timestamp|
        {
            &&& self.pending_writes.contains_key(ts)
        } implies ts > self.watermark@.timestamp() by {
            assert_by_contradiction!(ts > self.watermark@.timestamp(), {
                if ts > old_watermark && ts < next_ts {
                    pending_writes.lemma_minimal_equivalent_least(ts_leq, next_ts);
                    assert(ts_leq(next_ts, ts)); // CONTRADICTION
                }
            });
        }

        // linearize any reads at the current value
        self.apply_read_linearizers_at_value(&register, self.current_value());

        // XXX: load bearing assert
        assert(self.pending_writes_up_to(max_timestamp) == old(self).pending_writes_up_to(max_timestamp).remove(next_ts));
        self.apply_linearizers_up_to(register, max_timestamp)
    }

    proof fn apply_read_linearizers_at_value(
        tracked &mut self,
        tracked register: &GhostVarAuth<Option<u64>>,
        value: Option<u64>,
    )
        requires
            register.id() == old(self).register_id,
            old(self).basic_inv(),
            old(self).write_dom_inv(),
            old(self).weak_read_dom_inv(),
            old(self).current_value() == register@,
            register@ == value,
        ensures
            self.ids() == old(self).ids(),
            self.inv(),
            old(self).watermark == self.watermark,
            old(self).write_token_map@.dom() == self.write_token_map@.dom(),
            old(self).read_token_map@.dom() == self.read_token_map@.dom(),
            old(self).completed_writes == self.completed_writes,
            old(self).pending_writes == self.pending_writes,
            old(self).history == self.history,
            self.pending_reads.dom() == old(self).pending_reads.dom().difference(old(self).pending_reads_with_value(value)),
            self.completed_reads.dom() == old(self).completed_reads.dom().union(old(self).pending_reads_with_value(value)),
        decreases
            old(self).pending_reads_with_value(value).len()
        opens_invariants
            Set::new(|id: int| id != super::state_inv_id())
    {
        let ghost old_watermark = self.watermark@.timestamp();
        let pending_reads = self.pending_reads_with_value(value);
        self.lemma_pending_reads(value);
        if pending_reads.len() == 0 {
            // TODO(meeting): scary
            assert forall|key: (Option<u64>, nat)| self.pending_reads.contains_key(key) implies {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp()
                        && self.history.contains_key(ts) ==> { self.history[ts] != pending.value }
            } by {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                assert forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp()
                        && self.history.contains_key(ts) implies { self.history[ts] != pending.value
                } by {
                    if ts == self.watermark@.timestamp() {
                        assert_by_contradiction!(self.history[ts] != pending.value, {
                            assert(self.pending_reads_with_value(pending.value).contains(key)); // trigger
                        });
                    }
                }
            };
            return;
        }
        assert(!pending_reads.is_empty());

        let next_key = choose|k: (Option<u64>, nat)| pending_reads.contains(k);

        // take linearizer, apply, move watermark, place in completed
        let tracked pending = self.pending_reads.tracked_remove(next_key);
        let tracked completed = pending.apply_linearizer(register, self.watermark@.timestamp());
        self.completed_reads.tracked_insert(next_key, completed);

        // XXX: load bearing asserts
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom()));
        assert(self.completed_reads.dom() <= self.read_token_map@.dom());
        assert(self.pending_reads_with_value(value) == old(self).pending_reads_with_value(
            value,
        ).remove(next_key));

        self.apply_read_linearizers_at_value(register, value)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_write_completion(tracked &mut self,
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
            old(self).history == self.history,
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

        (completed.completion, completed.token)
    }

    /// Return the completion of a read at the timestamp - removing it from the sequence
    pub proof fn extract_read_completion(tracked &mut self,
        tracked token: LinReadToken<RL>,
        exec_timestamp: Timestamp,
        tracked resource: MonotonicTimestampResource,
    ) -> (tracked r: RL::Completion)
        requires
            old(self).inv(),
            // TODO(bsdinis): move this to resource@@ is LowerBound
            old(self).watermark@.timestamp() >= resource@.timestamp(),
            resource@.timestamp() >= exec_timestamp,
            exec_timestamp >= token.value().min_ts@.timestamp(),
            token.id() == old(self).read_token_map.id(),
            // TODO: add dup resource ts -> v
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            old(self).history == self.history,
            self.read_token_map@ == old(self).read_token_map@.remove(token.key()),
            self.completed_reads == old(self).completed_reads.remove(token.key()),
            token.value().lin.post(token.value().op, token.key().0, r),
    {
        token.agree(&self.read_token_map);

        // TODO(assume/dup): need the dup resource right about now
        assume(self.history.contains_key(exec_timestamp));
        assume(self.history[exec_timestamp] == token.key().0);
        assert(self.completed_reads.contains_key(token.key()));

        let tracked completed = self.completed_reads.tracked_remove(token.key());
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom()));

        completed.completion
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_write_lin(tracked &mut self,
        tracked token: LinWriteToken<ML>,
    ) -> (tracked r: (MaybeWriteLinearized<ML, ML::Completion>, ClientToken))
        requires
            old(self).inv(),
            token.id() == old(self).write_token_map.id(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            old(self).history == self.history,
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

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_read_lin(tracked &mut self,
        tracked token: LinReadToken<RL>,
    ) -> (tracked r: MaybeReadLinearized<RL, RL::Completion>)
        requires
            old(self).inv(),
            token.id() == old(self).read_token_map.id(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            old(self).history == self.history,
            self.read_token_map@ == old(self).read_token_map@.remove(token.key()),
            token.value().lin == r.lin(),
            token.value().op == r.op(),
    {
        token.agree(&self.read_token_map);

        let completed = exists|ts: Timestamp|
            {
                &&& token.value().min_ts@.timestamp() <= ts
                &&& ts <= self.watermark@.timestamp()
                &&& self.history.contains_key(ts)
                &&& self.history[ts] == token.key().0
            };

        let tracked lincomp = if completed {
            self.completed_reads.tracked_remove(token.key()).maybe()
        } else {
            self.pending_reads.tracked_remove(token.key()).maybe()
        };
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(self.pending_reads.dom()));

        lincomp
    }

    /// Show that if we have a write token for a key, then it exists
    pub proof fn lemma_write_token_is_in_queue(tracked &self, tracked token: &LinWriteToken<ML>)
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

    /// Show that if we have a read token for a key, then it exists
    pub proof fn lemma_read_token_is_in_queue(tracked &self, tracked token: &LinReadToken<RL>)
        requires
            self.inv(),
            token.id() == self.read_token_map.id(),
        ensures
            ({
                ||| self.pending_reads.contains_key(token.key())
                ||| self.completed_reads.contains_key(token.key())
            })
    {
        token.agree(&self.read_token_map);
    }
}

}

impl<ML, RL> std::fmt::Debug for InsertError<ML, RL> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::WriteWatermarkContradiction { .. } => {
                f.write_str("WriteWatermarkContradiction")
            }
            InsertError::ReadWatermarkContradiction { .. } => {
                f.write_str("ReadWatermarkContradiction")
            }
        }
    }
}
