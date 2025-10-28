use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;
#[allow(unused_imports)]
use vstd::tokens::map::GhostMapAuth;

#[allow(unused_imports)]
use vstd::assert_by_contradiction;
use vstd::prelude::*;

mod maybe_lin;
mod token;

use maybe_lin::MaybeLinearized;
#[allow(unused_imports)]
use token::LinToken;

verus! {


pub tracked enum InsertError {
    WatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked watermark_lb: MonotonicTimestampResource,
    },
}

/* TODO(read_lin)
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
pub struct LinearizationQueue<ML: MutLinearizer<RegisterWrite>> {
    pub queue: Map<Timestamp, MaybeLinearized<ML>>,

    // Why we need a token map in addition to the queue
    //
    // The values in the queue are possibly all changed with apply_linearizer
    // This would require all Submaps to be passed, which is impossible
    pub token_map: GhostMapAuth<Timestamp, (ML, RegisterWrite)>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,

    // This is the register this lin queue refers to
    pub ghost register_id: int,
}

pub struct LinQueueIds {
    pub token_map_id: int,
    pub watermark_id: int,
    pub register_id: int,
}

impl<ML: MutLinearizer<RegisterWrite>> LinearizationQueue<ML> {
    pub proof fn dummy(register_id: int) -> (tracked result: Self)
        ensures
            result.inv(),
            result.register_id == register_id,
    {
        let tracked queue = Map::tracked_empty();
        let tracked token_map = GhostMapAuth::new(Map::empty()).0;
        let tracked watermark = MonotonicTimestampResource::alloc();
        LinearizationQueue {
            queue,
            token_map,
            watermark,
            register_id,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.watermark@ is FullRightToAdvance
        &&& self.token_map@.dom().finite()
        &&& self.queue.dom().finite()
        &&& self.token_map@.dom() == self.queue.dom()
        &&& forall |ts: Timestamp| {
            &&& self.queue.contains_key(ts) ==> {
                &&& self.queue[ts].inv()
                &&& self.queue[ts].timestamp() == ts
                &&& self.queue[ts].op().id == self.register_id
                &&& !self.queue[ts].namespaces().contains(super::state_inv_id())
                &&& ts <= self.watermark@.timestamp() ==> self.queue[ts] is Comp
                &&& ts > self.watermark@.timestamp() ==> self.queue[ts] is Linearizer
                &&& self.token_map@.contains_key(ts) ==> {
                    let maybe_lin = self.queue[ts];
                    self.token_map@[ts] == (maybe_lin.lin(), maybe_lin.op())
                }
            }
        }
    }

    pub open spec fn ids(self) -> LinQueueIds {
        LinQueueIds {
            token_map_id: self.token_map.id(),
            watermark_id: self.watermark.loc(),
            register_id: self.register_id,
        }
    }

    /// Inserts the linearizer into the linearization queue
    pub proof fn insert_linearizer(tracked &mut self,
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (tracked r: Result<LinToken<ML>, InsertError>)
        requires
            old(self).inv(),
            lin.pre(op),
            lin.namespaces().finite(),
            !lin.namespaces().contains(super::state_inv_id()),
            op.id == old(self).register_id,
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).queue.dom() <= self.queue.dom(),
            r is Ok ==> ({
                let token = r->Ok_0;
                &&& token.inv()
                &&& token.timestamp() == timestamp
                &&& token.lin() == lin
                &&& token.op() == op
                &&& token.id() == self.token_map.id()
                &&& self.token_map@.len() == old(self).token_map@.len() + 1
                &&& self.queue.contains_key(token.timestamp())
            }),
            r is Err ==> old(self) == self,
    {
        if self.watermark@.timestamp() >= timestamp {
            return Err(InsertError::WatermarkContradiction {
                watermark_lb: self.watermark.extract_lower_bound()
            });
        }

        // TODO(assume): get client lease on timestamp to prove uniqueness
        assume(!self.token_map@.contains_key(timestamp));

        let m = map![timestamp => (lin, op)];
        // contains key is a load bearing assert here, allows verus to understand that
        // m.contains_value(...) and that is enough to prove the rest
        assert(m.contains_key(timestamp));

        let tracked maybe_lin = MaybeLinearized::linearizer(lin, op, timestamp);

        self.queue.tracked_insert(timestamp, maybe_lin);
        let tracked submap = self.token_map.insert(m);
        // load bearing assert
        assert(self.queue.dom() == self.token_map@.dom());

        Ok(LinToken { submap })
    }

    pub open spec fn pending_lins_up_to(self,
        max_timestamp: Timestamp
    ) -> (r: Set<Timestamp>)
        recommends self.inv()
    {
        self.queue.dom().filter(|ts: Timestamp| self.watermark@.timestamp() < ts && ts <= max_timestamp)
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
            self.inv(),
            self.ids() == old(self).ids(),
            old(self).queue.dom() == self.queue.dom(),
            register.id() == r.1.id(),
            self.queue.contains_key(max_timestamp) ==> self.watermark@.timestamp() >= max_timestamp,
            self.watermark.loc() == r.0.loc(),
            r.0@.timestamp() == self.watermark@.timestamp(),
            r.0@ is LowerBound,
            r.1.id() == register.id(),
            self.pending_lins_up_to(max_timestamp).len() == 0,
        decreases
            old(self).pending_lins_up_to(max_timestamp).len()
        opens_invariants
            Set::new(|id: int| id != super::state_inv_id())
    {
        let pending_lins = self.pending_lins_up_to(max_timestamp);

        if pending_lins.is_empty() {
            if self.queue.contains_key(max_timestamp) {
                assert_by_contradiction!(self.watermark@.timestamp() >= max_timestamp,
                {
                    if self.watermark@.timestamp() < max_timestamp {
                        assert(self.pending_lins_up_to(max_timestamp).contains(max_timestamp)); // trigger
                    }
                });
            }
            return (self.watermark.extract_lower_bound(), register);
        }

        let ts_leq = |a: Timestamp, b: Timestamp| a <= b;
        let next_ts = pending_lins.find_unique_minimal(ts_leq);
        pending_lins.find_unique_minimal_ensures(ts_leq);

        let tracked lin = self.queue.tracked_remove(next_ts);

        let tracked comp = lin.apply_linearizer(&mut register, next_ts);

        let ghost old_watermark = self.watermark@.timestamp();
        self.watermark.advance(next_ts);
        self.queue.tracked_insert(next_ts, comp);

        assert forall |ts: Timestamp|
        {
            &&& self.queue.contains_key(ts)
            && ts <= self.watermark@.timestamp()
        }
            implies self.queue[ts] is Comp by {
            assert_by_contradiction!(self.queue[ts] is Comp,
            {
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
        tracked token: LinToken<ML>,
        tracked resource: MonotonicTimestampResource
    ) -> (tracked r: ML::Completion)
        requires
            old(self).inv(),
            old(self).watermark@.timestamp() >= resource@.timestamp(),
            token.inv(),
            token.id() == old(self).token_map.id(),
            resource@.timestamp() >= token.timestamp(),
        ensures
            self.inv(),
            self.ids() == old(self).ids(),
            self.queue.dom() <= old(self).queue.dom(),
            token.lin().post(token.op(), (), r),
    {
        token.submap.agree(&self.token_map);
        // load bearing asserts
        assert(token.submap@.dom() <= self.token_map@.dom());
        assert(token.submap@.dom() == set![token.timestamp()]) by {
            token.lemma_dom()
        };

        let tracked comp = self.queue.tracked_remove(token.timestamp());
        let ghost new_queue_dom = self.queue.dom();

        self.token_map.delete(token.submap);
        // load bearing assert
        assert(self.queue.dom() == self.token_map@.dom());

        comp.tracked_get_completion()
    }
}

}

impl std::fmt::Debug for InsertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::WatermarkContradiction { .. } => f.write_str("WatermarkContradiction"),
        }
    }
}
