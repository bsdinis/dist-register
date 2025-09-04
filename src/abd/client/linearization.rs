use crate::abd::proto::Timestamp;
use crate::abd::resource::register::MonotonicRegisterResource;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use crate::abd::client::logatom::*;

verus! {

pub enum MaybeLinearized<ML: MutLinearizer<RegisterWrite>> {
    // TODO: we need to establish that the op here has a one-to-one correspondence to the token map
    // values in the linearization queue
    Linearizer {
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
    },
    Comp {
        // is GhostVar<Option<u64>>
        tracked completion: ML::Completion,
        timestamp: Timestamp,
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub proof fn apply_linearizer(self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: &Timestamp
    ) -> Self {
        match self {
            MaybeLinearized::Linearizer { lin, op, timestamp } => {
                if timestamp.le(resolved_timestamp) {
                    // ???? - this is not true
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Comp { completion, timestamp }
                } else {
                    MaybeLinearized::Linearizer { lin, op, timestamp }
                }
            },
            completed => completed
        }
    }
}

enum InsertError {
    WatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        watermark_lb: MonotonicRegisterResource,
    },
    UniquenessContradiction {
        // Read-only duplicable resource about the existence of the timestamp in the
        // global invariant set timestamp
        // dup_witness: TimestampWitness,
        dup_witness: (),
    },
}

// IDEA:
//  - insert_linearizer returns a Token
//  - Token can be complemented by the resource given by apply_linearizer
//  - Together, they can be used to extract the completion

pub struct LinearizationQueue<ML: MutLinearizer<RegisterWrite>> {
    pub queue: Map<Timestamp, MaybeLinearized<ML>>,

    pub token_map: GhostMapAuth<int, (RegisterWrite, Timestamp)>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicRegisterResource,
}

pub type Token = GhostSubmap<int, (RegisterWrite, Timestamp)>;

impl<ML: MutLinearizer<RegisterWrite>> LinearizationQueue<ML> {
    // TODO:
    //  - create function to "create" the atomic invariant with the linearization queue in it
    //  - this queue is assumed to be common to all the clients
    pub proof fn dummy() -> (tracked result: Self) {
        let tracked queue = Map::tracked_empty();
        let tracked token_map = GhostMapAuth::new(Map::empty()).0;
        let tracked watermark = MonotonicRegisterResource::alloc();
        LinearizationQueue {
            queue,
            token_map,
            watermark,
        }
    }

    pub open spec fn inv(&self) -> bool {
        self.watermark@ is FullRightToAdvance
    }

    /// Inserts the linearizer into the linearization queue
    pub proof fn insert_linearizer(tracked &mut self,
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (r: Result<Tracked<Token>, Tracked<InsertError>>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            r is Ok ==> ({
                let tok = r->Ok_0;
                &&& tok@.id() == self.token_map.id()
                &&& tok@.dom().len() == 1
                &&& tok@@.contains_value((op, timestamp))
            })
    {
        if self.watermark@.timestamp().ge(&timestamp) {
            return Err(Tracked(InsertError::WatermarkContradiction {
                watermark_lb: self.watermark.extract_lower_bound()
            }));
        }

        // TODO: get witness to the timestamp in the maybe linearized to derive contradiction
        if self.queue.contains_key(timestamp) {
            return Err(Tracked(InsertError::UniquenessContradiction { dup_witness: () }));
        }

        let dup_op = op.spec_clone();
        // TODO: timestamp --> witness to the timestamp
        let pushed = MaybeLinearized::Linearizer { lin, op, timestamp };

        let ghost token_key = self.token_map.dom().find_unique_maximal(|a: int, b: int| a > b);
        assert(self.token_map.dom().disjoint(set![token_key]));
        let m = map![token_key => (dup_op, timestamp)];
        let tracked token = self.token_map.insert(m);
        self.queue.tracked_insert(timestamp, pushed);

        Ok(Tracked(token))
    }


    /// Applies the linearizer for all writes prophecized to <= timestamp
    pub proof fn apply_linearizer(tracked &mut self,
        tracked register: GhostVarAuth<Option<u64>>,
        timestamp: &Timestamp
    ) -> (tracked r: (MonotonicRegisterResource, GhostVarAuth<Option<u64>>))
        requires old(self).inv(),
        ensures
            self.inv(),
            self.watermark@.timestamp().ge(timestamp),
            self.watermark@ == r.0@,
            r.0@ is LowerBound,
            r.1.id() == register.id(),
    {
        self.queue = self.queue.map_values(|v: MaybeLinearized<ML>| v.apply_linearizer(&mut register, timestamp));
        self.watermark.advance(*timestamp);

        (self.watermark.extract_lower_bound(), register)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_completion(tracked &mut self,
        tracked token: Token,
        tracked resource: MonotonicRegisterResource
    ) -> (tracked r: ML::Completion)
        requires
            old(self).inv(),
            old(self).watermark@.timestamp().ge(&resource@.timestamp()),
            token@.dom().len() == 1,
        ensures
            self.inv(),
            // TODO { somehow the token is related to the completion }
    {
        let timestamp = token@.values().choose().1;

        let tracked comp = self.queue.tracked_remove(timestamp);
        assume(comp is Comp); // this is known because the resource has been given
        let tracked c = comp->completion;

        c
    }
}

}

impl std::fmt::Debug for InsertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::WatermarkContradiction { .. } => f.write_str("WatermarkContradiction"),
            InsertError::UniquenessContradiction { .. } => f.write_str("UniquenessContradiction"),
        }
    }
}
