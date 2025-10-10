use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use vstd::logatom::*;
use vstd::map::*;
use vstd::prelude::*;
use vstd::set::*;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use crate::abd::invariants::logatom::*;

verus! {

pub enum MaybeLinearized<ML: MutLinearizer<RegisterWrite>> {
    // TODO: we need to establish that the op here
    // has a one-to-one correspondence to the token map
    // values in the linearization queue
    Linearizer {
        lin: ML,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
    },
    Comp {
        // is GhostVar<Option<u64>>
        completion: ML::Completion,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
        ghost lin: ML,
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub proof fn linearizer(tracked lin: ML, op: RegisterWrite, timestamp: Timestamp) -> (tracked result: Self)
        ensures
            result == (MaybeLinearized::Linearizer { lin, op, timestamp, })
    {
        MaybeLinearized::Linearizer {
            lin,
            op,
            timestamp,
        }
    }

    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            self is Linearizer ==> self.lin().pre(self.op()),
            old(register).id() == self.op().id,
        ensures
            old(register).id() == register.id(),
        opens_invariants
            self.namespaces()
    {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp, .. } if timestamp < resolved_timestamp => {
                    let ghost lin_copy = lin;
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Comp { completion, timestamp, lin: lin_copy, op }
            } ,
            other => other
        }
    }

    pub closed spec fn lin(self) -> ML {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin,
            MaybeLinearized::Comp { lin, .. } => lin,
        }
    }

    pub closed spec fn op(self) -> RegisterWrite {
        match self {
            MaybeLinearized::Linearizer { op, .. } => op,
            MaybeLinearized::Comp { op, .. } => op,
        }
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeLinearized::Comp { timestamp, .. } => timestamp,
        }
    }

    pub closed spec fn namespaces(self) -> Set<int> {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeLinearized::Comp { .. } => Set::empty(),
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

pub struct LinearizationQueue<ML: MutLinearizer<RegisterWrite>> {
    pub queue: Map<Timestamp, MaybeLinearized<ML>>,

    // Why we need a token map in addition to the queue
    //
    // The values in the queue are possibly all changed with apply_linearizer
    // This would require all Submaps to be passed, which is impossible
    pub token_map: GhostMapAuth<Timestamp, (ML, RegisterWrite)>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: MonotonicTimestampResource,
}

pub struct LinToken<ML: MutLinearizer<RegisterWrite>> {
    pub submap: GhostSubmap<Timestamp, (ML, RegisterWrite)>,
}

impl<ML: MutLinearizer<RegisterWrite>> LinToken<ML> {
    pub open spec fn inv(self) -> bool {
        &&& self.submap@.len() == 1
        &&& self.submap@.dom().finite()
    }

    pub open spec fn id(self) -> int {
        self.submap.id()
    }

    pub open spec fn timestamp(self) -> Timestamp
        recommends self.inv()
    {
        self.submap@.dom().choose()
    }

    pub open spec fn lin(self) -> ML
        recommends self.inv()
    {
        self.submap@[self.timestamp()].0
    }

    pub open spec fn op(self) -> RegisterWrite
        recommends self.inv()
    {
        self.submap@[self.timestamp()].1
    }

    pub proof fn lemma_dom(self)
        requires
            self.inv(),
        ensures
            self.submap@.dom() == set![self.timestamp()]
    {
        let timestamp = self.timestamp();
        let target_dom = set![timestamp];

        assert(self.submap@.dom().len() == 1);
        assert(target_dom.len() == 1);

        assert(self.submap@.dom().finite());
        assert(target_dom.finite());

        assert(self.submap@.dom().contains(timestamp));
        assert(target_dom.contains(timestamp));

        assert(target_dom <= self.submap@.dom());
        // assert(self.submap@.dom() <= target_dom);

        // TODO(assume): sets
        assume(self.submap@.dom() == target_dom);
    }
}

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
        &&& self.token_map@.dom() == self.queue.dom()
        &&& forall |timestamp: Timestamp| {
            &&& timestamp <= self.watermark@.timestamp() && self.queue.contains_key(timestamp) ==> {
                let comp = self.queue[timestamp];
                &&& comp is Comp
                &&& comp.lin().post(comp.op(), (), comp->completion)
            }
            &&& timestamp > self.watermark@.timestamp() && self.queue.contains_key(timestamp) ==> {
                let lin = self.queue[timestamp];
                &&& lin is Linearizer
                &&& lin.lin().pre(lin.op())
            }
            &&& self.token_map@.contains_key(timestamp) ==> {
                let maybe_lin = self.queue[timestamp];
                self.token_map@[timestamp] == (maybe_lin.lin(), maybe_lin.op())
            }
        }
    }

    // TODO(nickolai): there must be a better way
    pub open spec fn named_ids(self) -> Map<&'static str, int> {
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
    ) -> (tracked r: Result<LinToken<ML>, InsertError>)
        requires
            old(self).inv(),
            lin.pre(op),
        ensures
            self.inv(),
            self.named_ids() == old(self).named_ids(),
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


    /// Applies the linearizer for all writes prophecized to <= timestamp
    pub proof fn apply_linearizer(tracked &mut self,
        tracked register: GhostVarAuth<Option<u64>>,
        timestamp: Timestamp
    ) -> (tracked r: (MonotonicTimestampResource, GhostVarAuth<Option<u64>>))
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.named_ids() == old(self).named_ids(),
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
            // TODO(assume): requires proof fn enabled tracked_map_values
            assume(forall |timestamp: Timestamp| {
                timestamp <= self.watermark@.timestamp() && self.queue.contains_key(timestamp) ==> self.queue[timestamp] is Comp
            });
        }

        (self.watermark.extract_lower_bound(), register)
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
            self.named_ids() == old(self).named_ids()
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
