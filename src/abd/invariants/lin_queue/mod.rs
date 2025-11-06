#![allow(dead_code)]

#[allow(unused_imports)]
use crate::abd::invariants::committed_to::WriteAllocation;
#[allow(unused_imports)]
use crate::abd::invariants::committed_to::WriteCommitment;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
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
use vstd::tokens::map::GhostPersistentSubmap;
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

verus! {

pub tracked enum InsertError<ML, RL> {
    WriteWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked w_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked w_lin: ML,
    },
    ReadWatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked r_watermark_lb: MonotonicTimestampResource,
        // Linearizer to return to user on error
        tracked r_lin: RL,
    },
}

impl<ML, RL> InsertError<ML, RL> {
    pub proof fn tracked_write_destruct(tracked self) -> (tracked r: ML)
        requires
            self is WriteWatermarkContradiction,
        ensures
            self->w_lin == r,
    {
        match self {
            InsertError::WriteWatermarkContradiction { w_lin, .. } => w_lin,
            _ => vstd::pervasive::proof_from_false(),
        }
    }

    pub proof fn tracked_read_destruct(tracked self) -> (tracked r: RL)
        requires
            self is ReadWatermarkContradiction,
        ensures
            self->r_lin == r,
    {
        match self {
            InsertError::ReadWatermarkContradiction { r_lin, .. } => r_lin,
            _ => vstd::pervasive::proof_from_false(),
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
    // commitment to values
    pub committed_to: GhostPersistentSubmap<Timestamp, Option<u64>>,
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
    pub write_token_map: GhostMapAuth<Timestamp, WriteTokenVal<ML>>,
    pub read_token_map: GhostMapAuth<(Option<u64>, nat), ReadTokenVal<RL>>,
    // counter for next read op
    pub next_read_op: nat,
    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,
    // This is the register this lin queue refers to
    pub ghost register_id: int,
}

pub type LinWriteToken<ML> = GhostPointsTo<Timestamp, WriteTokenVal<ML>>;

pub type LinReadToken<RL> = GhostPointsTo<(Option<u64>, nat), ReadTokenVal<RL>>;

pub struct ReadTokenVal<RL> {
    pub ghost lin: RL,
    pub ghost op: RegisterRead,
    pub tracked min_ts: MonotonicTimestampResource,
}

pub struct WriteTokenVal<ML> {
    pub ghost lin: ML,
    pub ghost op: RegisterWrite,
    pub ghost committed: bool,
}

pub struct LinQueueIds {
    pub committed_to_id: int,
    pub write_token_map_id: int,
    pub read_token_map_id: int,
    pub watermark_id: int,
    pub register_id: int,
}

impl<ML, RL> LinearizationQueue<ML, RL, ML::Completion, RL::Completion> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub proof fn dummy(
        register_id: int,
        tracked zero_commitment: WriteCommitment,
    ) -> (tracked result: Self)
        requires
            zero_commitment.key() == Timestamp::spec_default(),
            zero_commitment.value() == None::<u64>,
        ensures
            result.inv(),
            result.register_id == register_id,
            result.watermark@.timestamp() == Timestamp::spec_default(),
            result.committed_to@ == map![Timestamp::spec_default() => None::<u64>],
            result.committed_to.id() == zero_commitment.id(),
            result.read_token_map@.is_empty(),
            result.write_token_map@.is_empty(),
    {
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
            committed_to: zero_commitment.submap(),
            completed_writes,
            completed_reads,
            pending_writes,
            pending_reads,
            write_token_map,
            read_token_map,
            next_read_op: 0,
            watermark,
            register_id,
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
        &&& self.committed_to@.contains_key(self.watermark@.timestamp())
        &&& forall|ts: Timestamp|
            self.committed_to@.contains_key(ts) ==> ts <= self.watermark@.timestamp()
        &&& forall|ts: Timestamp|
            self.write_token_map@.contains_key(ts) && ts <= self.watermark@.timestamp()
                ==> self.committed_to@.contains_key(ts)
    }

    // full invariant over the write domain:
    //  1. the completed_writes + pending_writes match the write token domain
    //  2. everything below the watermark is completed, and matches the correct ids
    //  3. completed writes match the history
    //  4. everything above the watermark is pending and matches the correct ids
    pub open spec fn write_dom_inv(&self) -> bool {
        &&& self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        )
        &&& self.completed_writes.dom() <= self.committed_to@.dom()
        &&& self.completed_writes.dom().disjoint(self.pending_writes.dom())
        &&& self.committed_to@.dom().disjoint(self.pending_writes.dom())
        &&& forall|ts: Timestamp|
            self.completed_writes.contains_key(ts) ==> {
                let comp = self.completed_writes[ts];
                &&& ts <= self.watermark@.timestamp()
                &&& comp.timestamp == ts
                &&& comp.inv()
                &&& comp.commitment.id() == self.committed_to.id()
                &&& comp.op.id == self.register_id
                &&& self.write_token_map@[ts].lin == comp.lin
                &&& self.write_token_map@[ts].op == comp.op
                &&& self.committed_to@.contains_key(ts)
                &&& self.committed_to@[ts] == comp.op.new_value
            }
        &&& forall|ts: Timestamp|
            self.pending_writes.contains_key(ts) ==> {
                let pending = self.pending_writes[ts];
                &&& ts > self.watermark@.timestamp()
                &&& pending.timestamp == ts
                &&& pending.inv()
                &&& pending.write_status.id() == self.committed_to.id()
                &&& pending.op.id == self.register_id
                &&& self.write_token_map@[ts].lin == pending.lin
                &&& self.write_token_map@[ts].op == pending.op
                &&& self.write_token_map@[ts].committed == pending.write_status is Committed
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
                &&& tok.min_ts@ is LowerBound
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
                &&& self.committed_to@.contains_key(comp.timestamp)
                &&& self.committed_to@[comp.timestamp] == comp.value
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
        &&& forall|key: (Option<u64>, nat)|
            self.pending_reads.contains_key(key) ==> {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                &&& pending.inv()
                &&& pending.value == key.0
                &&& pending.lin == token.lin
                &&& pending.op == token.op
                &&& pending.op.id == self.register_id
                &&& forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp()
                        && self.committed_to@.contains_key(ts) ==> {
                        self.committed_to@[ts] != pending.value
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
        &&& forall|key: (Option<u64>, nat)|
            self.pending_reads.contains_key(key) ==> {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                &&& pending.inv()
                &&& pending.value == key.0
                &&& pending.op.id == self.register_id
                &&& token.lin == pending.lin
                &&& token.op == pending.op
                &&& forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts < self.watermark@.timestamp()
                        && self.committed_to@.contains_key(ts) ==> {
                        self.committed_to@[ts] != pending.value
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
            committed_to_id: self.committed_to.id(),
            write_token_map_id: self.write_token_map.id(),
            read_token_map_id: self.read_token_map.id(),
            watermark_id: self.watermark.loc(),
            register_id: self.register_id,
        }
    }

    pub open spec fn current_value(self) -> Option<u64>
        recommends
            self.basic_inv(),
    {
        self.committed_to@[self.watermark@.timestamp()]
    }

    pub open spec fn known_timestamps(self) -> Set<Timestamp>
        recommends
            self.basic_inv(),
    {
        self.committed_to@.dom().union(self.pending_writes.dom())
    }

    /// Inserts the mut linearizer into the linearization queue
    pub proof fn insert_write_linearizer(
        tracked &mut self,
        tracked lin: ML,
        tracked op: RegisterWrite,
        timestamp: Timestamp,
        tracked allocation_opt: Option<WriteAllocation>,
    ) -> (tracked r: Result<LinWriteToken<ML>, InsertError<ML, RL>>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id,
            allocation_opt is Some <==> timestamp > old(self).watermark@.timestamp(),
            allocation_opt is Some ==> ({
                let allocation = allocation_opt->Some_0;
                &&& allocation.key() == timestamp
                &&& allocation.value() == op.new_value
                &&& allocation.id() == old(self).committed_to.id()
                &&& !old(self).write_token_map@.contains_key(timestamp)
            }),
        ensures
            self.inv(),
            old(self).ids() == self.ids(),
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.read_token_map@ == old(self).read_token_map@,
            r is Ok <==> timestamp > old(self).watermark@.timestamp(),
            r is Ok ==> ({
                let token = r->Ok_0;
                &&& token.id() == self.write_token_map.id()
                &&& token.key() == timestamp
                &&& token.value().lin == lin
                &&& token.value().op == op
                &&& !token.value().committed
                &&& self.write_token_map@ == old(self).write_token_map@.insert(
                    token.key(),
                    token.value(),
                )
                &&& self.pending_writes.dom() == old(self).pending_writes.dom().insert(token.key())
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let watermark_lb = r->Err_0->w_watermark_lb;
                &&& *old(self) == *self
                &&& err is WriteWatermarkContradiction
                &&& err->w_lin == lin
                &&& watermark_lb@.timestamp() >= timestamp
                &&& watermark_lb.loc() == self.watermark.loc()
                &&& watermark_lb@ is LowerBound
            }),
    {
        if timestamp <= self.watermark@.timestamp() {
            return Err(
                InsertError::WriteWatermarkContradiction {
                    w_watermark_lb: self.watermark.extract_lower_bound(),
                    w_lin: lin,
                },
            );
        }
        let tracked allocation = allocation_opt.tracked_unwrap();
        let tracked v = WriteTokenVal { lin, op, committed: false };
        let tracked pending = PendingWrite::new(lin, op, allocation, timestamp);

        self.pending_writes.tracked_insert(timestamp, pending);
        let tracked lin_token = self.write_token_map.insert(timestamp, v);
        // load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        lin_token.lemma_view();

        assert(self.write_dom_inv());
        Ok(lin_token)
    }

    /// Inserts the read linearizer into the linearization queue
    pub proof fn insert_read_linearizer(
        tracked &mut self,
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
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.write_token_map@ == old(self).write_token_map@,
            self.read_token_map@ == old(self).read_token_map@.insert(token.key(), token.value()),
            self.pending_writes == old(self).pending_writes,
            token.id() == self.read_token_map.id(),
            token.key().0 == value,
            token.value().lin == lin,
            token.value().op == op,
            token.value().min_ts.loc() == self.watermark.loc(),
            value == self.current_value() ==> self.completed_reads.contains_key(token.key()),
            value != self.current_value() ==> self.pending_reads.contains_key(token.key()),
        opens_invariants Set::new(|id: int| id != super::state_inv_id())
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
        if value == self.current_value() {
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

    pub proof fn commit_value(
        tracked &mut self,
        tracked write_token: &mut LinWriteToken<ML>,
    ) -> (tracked r: WriteCommitment)
        requires
            old(self).inv(),
            old(write_token).id() == old(self).write_token_map.id(),
            !old(write_token).value().committed,
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.write_token_map@.dom() == old(self).write_token_map@.dom(),
            self.read_token_map@ == old(self).read_token_map@,
            self.pending_writes.dom() == old(self).pending_writes.dom(),
            write_token.id() == old(write_token).id(),
            write_token.key() == old(write_token).key(),
            write_token.value().lin == old(write_token).value().lin,
            write_token.value().op == old(write_token).value().op,
            write_token.value().committed == true,
            r.id() == self.committed_to.id(),
            r.key() == write_token.key(),
            r.value() == write_token.value().op.new_value,
    {
        write_token.agree(&self.write_token_map);
        let tracked commitment = if write_token.key() <= self.watermark@.timestamp() {
            let tracked mut completed = self.completed_writes.tracked_remove(write_token.key());
            let tracked commitment = completed.commitment.duplicate();
            self.completed_writes.tracked_insert(write_token.key(), completed);
            commitment
        } else {
            let tracked pending = self.pending_writes.tracked_remove(write_token.key());
            let tracked (pending, commitment) = pending.commit();
            self.pending_writes.tracked_insert(write_token.key(), pending);
            commitment
        };

        let new_write_val = WriteTokenVal {
            lin: write_token.value().lin,
            op: write_token.value().op,
            committed: true,
        };
        write_token.update(&mut self.write_token_map, new_write_val);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));
        commitment
    }

    pub open spec fn pending_writes_up_to(self, max_timestamp: Timestamp) -> (r: Set<Timestamp>)
        recommends
            self.inv(),
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
            self.inv() || self.current_value() == value,
    {
        self.pending_reads.dom().filter(|k: (Option<u64>, nat)| k.0 == value)
    }

    proof fn lemma_pending_reads(self, value: Option<u64>)
        requires
            self.pending_reads.dom().finite(),
            self.inv() || self.current_value() == value,
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
    pub proof fn apply_linearizers_up_to(
        tracked &mut self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        max_timestamp: Timestamp,
    ) -> (tracked r: MonotonicTimestampResource)
        requires
            old(self).inv(),
            old(register).id() == old(self).register_id,
            old(self).current_value() == old(register)@,
            old(self).known_timestamps().contains(max_timestamp),
        ensures
    // invariants + ids

            self.inv(),
            self.ids() == old(self).ids(),
            self.watermark.loc() == r.loc(),
            self.current_value() == register@,
            register.id() == old(register).id(),
            // post-condition changes
            self.write_token_map@.dom() == old(self).write_token_map@.dom(),
            self.read_token_map@.dom() == old(self).read_token_map@.dom(),
            max_timestamp > old(self).watermark@.timestamp() ==> self.watermark@.timestamp()
                == max_timestamp,
            max_timestamp <= old(self).watermark@.timestamp() ==> self.watermark == old(
                self,
            ).watermark,
            self.committed_to@.dom() == old(self).committed_to@.dom().union(
                old(self).pending_writes_up_to(max_timestamp),
            ),
            self.pending_writes == old(self).pending_writes.remove_keys(
                old(self).pending_writes_up_to(max_timestamp),
            ),
            self.pending_writes_up_to(max_timestamp).len() == 0,
            // return values
            r@.timestamp() == self.watermark@.timestamp(),
            r@ is LowerBound,
        decreases old(self).pending_writes_up_to(max_timestamp).len(),
        opens_invariants Set::new(|id: int| id != super::state_inv_id())
    {
        let pending_writes = self.pending_writes_up_to(max_timestamp);
        self.lemma_pending_writes(max_timestamp);
        assert(pending_writes.finite());

        if pending_writes.len() == 0 {
            if self.pending_writes.contains_key(max_timestamp) {
                assert_by_contradiction!(max_timestamp <= self.watermark@.timestamp(),
                {
                    assert(self.pending_writes_up_to(max_timestamp).contains(max_timestamp)); // trigger
                });
            }
            return self.watermark.extract_lower_bound();
        }
        let ts_leq = |a: Timestamp, b: Timestamp| a <= b;
        let next_ts = pending_writes.find_unique_minimal(ts_leq);
        pending_writes.find_unique_minimal_ensures(ts_leq);

        // take linearizer, apply, move watermark, place in completed
        let tracked (pending, cur_commitment) = self.pending_writes.tracked_remove(
            next_ts,
        ).commit();
        let tracked mut completed = pending.apply_linearizer(register, next_ts);

        let ghost old_committed = self.committed_to@;
        self.committed_to.intersection_agrees_points_to(&completed.commitment);
        self.committed_to.combine_points_to(cur_commitment);
        assert(self.committed_to@ == old_committed.insert(
            cur_commitment.key(),
            cur_commitment.value(),
        ));
        assert(old_committed <= self.committed_to@);

        let ghost old_watermark = self.watermark@.timestamp();
        self.watermark.advance(next_ts);
        self.completed_writes.tracked_insert(completed.timestamp, completed);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        assert forall|ts: Timestamp|
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
        self.apply_read_linearizers_at_value(&*register, self.current_value());

        // XXX: load bearing assert
        assert(self.pending_writes_up_to(max_timestamp) == old(self).pending_writes_up_to(
            max_timestamp,
        ).remove(next_ts));
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
            self.watermark == old(self).watermark,
            self.write_token_map@ == old(self).write_token_map@,
            self.read_token_map@ == old(self).read_token_map@,
            self.completed_writes == old(self).completed_writes,
            self.pending_writes == old(self).pending_writes,
            self.committed_to@ == old(self).committed_to@,
            self.pending_reads.dom() == old(self).pending_reads.dom().difference(
                old(self).pending_reads_with_value(value),
            ),
            self.completed_reads.dom() == old(self).completed_reads.dom().union(
                old(self).pending_reads_with_value(value),
            ),
        decreases old(self).pending_reads_with_value(value).len(),
        opens_invariants Set::new(|id: int| id != super::state_inv_id())
    {
        let ghost old_watermark = self.watermark@.timestamp();
        let pending_reads = self.pending_reads_with_value(value);
        self.lemma_pending_reads(value);
        if pending_reads.len() == 0 {
            assert forall|key: (Option<u64>, nat)| self.pending_reads.contains_key(key) implies {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp()
                        && self.committed_to@.contains_key(ts) ==> {
                        self.committed_to@[ts] != pending.value
                    }
            } by {
                let pending = self.pending_reads[key];
                let token = self.read_token_map@[key];
                assert forall|ts: Timestamp|
                    token.min_ts@.timestamp() <= ts && ts <= self.watermark@.timestamp()
                        && self.committed_to@.contains_key(ts) implies {
                    self.committed_to@[ts] != pending.value
                } by {
                    if ts == self.watermark@.timestamp() {
                        assert_by_contradiction!(self.committed_to@[ts] != pending.value, {
                            assert(self.pending_reads_with_value(pending.value).contains(key)); // trigger
                        });
                    }
                }
            };
            return ;
        }
        assert(!pending_reads.is_empty());

        let next_key = choose|k: (Option<u64>, nat)| pending_reads.contains(k);

        // take linearizer, apply, move watermark, place in completed
        let tracked pending = self.pending_reads.tracked_remove(next_key);
        let tracked completed = pending.apply_linearizer(register, self.watermark@.timestamp());
        self.completed_reads.tracked_insert(next_key, completed);

        // XXX: load bearing asserts
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));
        assert(self.completed_reads.dom() <= self.read_token_map@.dom());
        assert(self.pending_reads_with_value(value) == old(self).pending_reads_with_value(
            value,
        ).remove(next_key));

        assert(self.read_completed_inv());
        self.apply_read_linearizers_at_value(register, value)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_write_completion(
        tracked &mut self,
        tracked token: LinWriteToken<ML>,
        tracked resource: MonotonicTimestampResource,
    ) -> (tracked r: ML::Completion)
        requires
            old(self).inv(),
            old(self).watermark@.timestamp() >= resource@.timestamp(),
            token.id() == old(self).write_token_map.id(),
            resource@.timestamp() >= token.key(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.write_token_map@ == old(self).write_token_map@.remove(token.key()),
            self.completed_writes == old(self).completed_writes.remove(token.key()),
            self.pending_writes == old(self).pending_writes,
            ({
                let WriteTokenVal { lin, op, .. } = token.value();
                lin.post(op, (), r)
            }),
    {
        token.agree(&self.write_token_map);

        let tracked completed = self.completed_writes.tracked_remove(token.key());
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        completed.completion
    }

    /// Return the completion of a read at the timestamp - removing it from the sequence
    pub proof fn extract_read_completion(
        tracked &mut self,
        tracked token: LinReadToken<RL>,
        exec_timestamp: Timestamp,
        tracked mut resource: MonotonicTimestampResource,
        tracked mut commitment: WriteCommitment,
    ) -> (tracked r: RL::Completion)
        requires
            old(self).inv(),
            resource@ is LowerBound,
            resource.loc() == old(self).watermark.loc(),
            resource@.timestamp() >= exec_timestamp,
            exec_timestamp >= token.value().min_ts@.timestamp(),
            token.id() == old(self).read_token_map.id(),
            commitment.id() == old(self).committed_to.id(),
            commitment.key() == exec_timestamp,
            commitment.value() == token.key().0,
            old(self).committed_to@.contains_key(exec_timestamp),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.write_token_map@ == old(self).write_token_map@,
            self.read_token_map@ == old(self).read_token_map@.remove(token.key()),
            self.completed_reads == old(self).completed_reads.remove(token.key()),
            self.completed_writes == old(self).completed_writes,
            self.pending_writes == old(self).pending_writes,
            token.value().lin.post(token.value().op, token.key().0, r),
    {
        token.agree(&self.read_token_map);
        resource.lemma_lower_bound(&self.watermark);
        commitment.intersection_agrees_submap(&self.committed_to);

        let tracked completed = self.completed_reads.tracked_remove(token.key());
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

        assert(self.inv());
        completed.completion
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_write_lin(
        tracked &mut self,
        tracked token: LinWriteToken<ML>,
    ) -> (tracked r: (MaybeWriteLinearized<ML, ML::Completion>, Option<WriteAllocation>))
        requires
            old(self).inv(),
            token.id() == old(self).write_token_map.id(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).watermark == self.watermark,
            old(self).committed_to@ == self.committed_to@,
            self.write_token_map@ == old(self).write_token_map@.remove(token.key()),
            self.completed_writes == old(self).completed_writes.remove(token.key()),
            token.value().lin == r.0.lin(),
            token.value().op == r.0.op(),
            !token.value().committed && r.1 is Some ==> {
                let allocation = r.1->Some_0;
                &&& allocation.id() == self.committed_to.id()
                &&& allocation.key() == token.key()
                &&& allocation.value() == token.value().op.new_value
                &&& self.pending_writes == old(self).pending_writes.remove(token.key())
                &&& old(self).pending_writes.contains_key(token.key())
            },
            !token.value().committed && r.1 is None ==> {
                self.pending_writes == old(self).pending_writes
            },
    {
        token.agree(&self.write_token_map);

        let tracked (lincomp, allocation_opt) = if token.key() <= self.watermark@.timestamp() {
            (self.completed_writes.tracked_remove(token.key()).maybe(), None)
        } else {
            let tracked pending = self.pending_writes.tracked_remove(token.key());
            if token.value().committed {
                pending.maybe()
            } else {
                pending.maybe()
            }
        };
        self.write_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.write_token_map@.dom() == self.completed_writes.dom().union(
            self.pending_writes.dom(),
        ));

        (lincomp, allocation_opt)
    }

    /// Remove the linearizer/completion from the queue (for error cases)
    pub proof fn remove_read_lin(tracked &mut self, tracked token: LinReadToken<RL>) -> (tracked r:
        MaybeReadLinearized<RL, RL::Completion>)
        requires
            old(self).inv(),
            token.id() == old(self).read_token_map.id(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.watermark@ == old(self).watermark@,
            self.committed_to@ == old(self).committed_to@,
            self.write_token_map@ == old(self).write_token_map@,
            self.read_token_map@ == old(self).read_token_map@.remove(token.key()),
            self.pending_writes == old(self).pending_writes,
            self.completed_writes == old(self).completed_writes,
            token.value().lin == r.lin(),
            token.value().op == r.op(),
    {
        token.agree(&self.read_token_map);

        let completed = exists|ts: Timestamp|
            {
                &&& token.value().min_ts@.timestamp() <= ts
                &&& ts <= self.watermark@.timestamp()
                &&& self.committed_to@.contains_key(ts)
                &&& self.committed_to@[ts] == token.key().0
            };

        let tracked lincomp = if completed {
            self.completed_reads.tracked_remove(token.key()).maybe()
        } else {
            self.pending_reads.tracked_remove(token.key()).maybe()
        };
        self.read_token_map.delete_points_to(token);

        // XXX: load bearing assert
        assert(self.read_token_map@.dom() == self.completed_reads.dom().union(
            self.pending_reads.dom(),
        ));

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
            }),
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
            }),
    {
        token.agree(&self.read_token_map);
    }
}

} // verus!
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
