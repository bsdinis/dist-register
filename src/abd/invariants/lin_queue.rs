use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use crate::abd::invariants::logatom::*;

verus! {

pub tracked enum MaybeLinearized<ML: MutLinearizer<RegisterWrite>> {
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
        // TODO: add token that can be extracted
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Self) {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp } if timestamp < resolved_timestamp => {
                    // TODO(nickolai): interesting to figure out at this stage how to verify the
                    // linearizer requirements
                    // TODO(assume): linearizer assumes
                    assume(lin.pre(op));
                    assume(op.requires(*register, (), ()));
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Comp { completion, timestamp }
            } ,
            other => other
        }
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeLinearized::Comp { timestamp, .. } => timestamp,
        }
    }

    pub proof fn tracked_get_completion(tracked self) -> (tracked r: ML::Completion)
        requires self is Comp,
        ensures self->completion == r
    {
        match self {
            MaybeLinearized::Comp { completion, .. } => completion,
            _ => proof_from_false()
        }
    }
}

pub tracked enum InsertError {
    WatermarkContradiction {
        // LowerBound resource saying that the watermark is bigger than the timestamp
        tracked watermark_lb: MonotonicTimestampResource,
    },
}

// IDEA:
//  - insert_linearizer returns a Token
//  - Token can be complemented by the resource given by apply_linearizer
//  - Together, they can be used to extract the completion

pub struct LinearizationQueue<ML: MutLinearizer<RegisterWrite>> {
    // TODO: needs to be monotonic map?
    pub queue: Map<Timestamp, MaybeLinearized<ML>>,

    // Why we need a token map in addition to the queue
    //
    // The values in the queue are possibly all changed with apply_linearizer
    // This would require all Submaps to be passed, which is impossible
    pub token_map: GhostMapAuth<int, (RegisterWrite, Timestamp)>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,
}

pub type Token = GhostSubmap<int, (RegisterWrite, Timestamp)>;

impl<ML: MutLinearizer<RegisterWrite>> LinearizationQueue<ML> {
    pub proof fn dummy() -> (tracked result: Self)
        ensures result.inv()
    {
        let tracked queue = Map::tracked_empty();
        let tracked token_map = GhostMapAuth::new(Map::empty()).0;
        let tracked watermark = MonotonicTimestampResource::alloc();
        LinearizationQueue {
            queue,
            token_map,
            watermark,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.watermark@ is FullRightToAdvance
        &&& self.token_map@.dom().finite()
        &&& self.queue.dom().finite()
        // TODO
        // &&& forall |timestamp: Timestamp|
        // timestamp <= self.watermark && self.queue.contains_key(timestamp) ==> self.queue[timestamp] is Comp
    }

    // TODO(nickolai): there must be a better way
    pub open spec fn namespace(self) -> Map<&'static str, int> {
        map![
            "token_map" => self.token_map.id(),
            "watermark" => self.watermark.loc(),
        ]
    }

    /// Inserts the linearizer into the linearization queue
    pub proof fn insert_linearizer(tracked &mut self,
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (tracked r: Result<Token, InsertError>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.namespace() == old(self).namespace(),
            r is Ok ==> ({
                let tok = r->Ok_0;
                &&& tok@.dom().finite()
                &&& tok.id() == self.token_map.id()
                &&& tok.dom().len() == 1
                &&& tok@.contains_value((op, timestamp))
                &&& self.token_map@.len() == old(self).token_map@.len() + 1
                &&& self.token_map@.dom().intersect(tok@.dom()) == tok@.dom()
                &&& self.queue.contains_key(timestamp)
            }),
            r is Err ==> old(self) == self,
    {
        if self.watermark@.timestamp() >= timestamp {
            assert(self.inv());
            return Err(InsertError::WatermarkContradiction {
                watermark_lb: self.watermark.extract_lower_bound()
            });
        }
        let ghost token_key = if self.token_map@.is_empty() {
            0
        } else {
            let k = self.token_map@.dom().find_unique_maximal(|a: int, b: int| a <= b) + 1;
            // TODO(assume): figure out goddamn maps
            // Investigation: contains_key is just dom().contains
            // dom is a closed spec, with no proofs so there is no info on this
            assume(!self.token_map@.contains_key(k));
            k
        };
        let m = map![token_key => (op, timestamp)];
        // TODO(nickolai): what???
        assert(m.contains_value((op, timestamp))) by {
            Map::axiom_map_insert_same_contains(Map::empty(), token_key, (op, timestamp));
        };
        let ghost old_len = self.token_map@.len();

        assert(self.token_map@.dom().finite());
        assert(m.dom().finite());
        self.queue.insert(timestamp, MaybeLinearized::Linearizer { lin, op, timestamp });
        // TODO(assume): goddamn maps
        assume(self.queue.contains_key(timestamp));
        let tracked token = self.token_map.insert(m);
        assert(self.token_map@.dom().finite());
        assert(self.token_map@.len() == old_len + 1);

        assert(token.id() == self.token_map.id());
        assert(token.dom().len() == 1);

        Ok(token)
    }


    /// Applies the linearizer for all writes prophecized to <= timestamp
    pub proof fn apply_linearizer(tracked &mut self,
        tracked register: GhostVarAuth<Option<u64>>,
        timestamp: Timestamp
    ) -> (tracked r: (MonotonicTimestampResource, GhostVarAuth<Option<u64>>))
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.namespace() == old(self).namespace(),
            self.watermark@.timestamp() >= timestamp,
            self.watermark.loc() == r.0.loc(),
            r.0@.timestamp() == self.watermark@.timestamp(),
            r.0@ is LowerBound,
            r.1.id() == register.id(),
    {
        if timestamp > self.watermark@.timestamp() {
            // TODO: verus proof fn tracked_map_values
            // self.queue = self.queue.map_values(|v: MaybeLinearized<ML>| v.apply_linearizer(&mut register, timestamp));
            self.watermark.advance(timestamp);
        }

        (self.watermark.extract_lower_bound(), register)
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    pub proof fn extract_completion(tracked &mut self,
        tracked token: Token,
        tracked resource: MonotonicTimestampResource
    ) -> (tracked r: ML::Completion)
        requires
            old(self).inv(),
            old(self).watermark@.timestamp() >= resource@.timestamp(),
            token@.dom().len() == 1,
            token@.dom().finite(),
            token.id() == old(self).token_map.id(),
            // resource@.timestamp() == token@.timestamp
            // old(self).queue.contains_key(token@.timestamp)
        ensures
            self.inv(),
            self.namespace() == old(self).namespace(),
            // r.timestamp == token@.timestamp
    {
        let timestamp = token@.values().choose().1;

        // TODO(assume): this is actually a precondition
        assume(self.queue.contains_key(timestamp));
        let tracked comp = self.queue.tracked_remove(timestamp);
        // TODO(assume): comes from lin queue invariant + resource
        assume(comp is Comp);
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
