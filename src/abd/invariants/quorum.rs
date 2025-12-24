#[allow(unused_imports)]
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

#[allow(unused_imports)]
use vstd::map_lib::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::set::*;
#[allow(unused_imports)]
use vstd::set_lib::*;

verus! {

pub struct ServerUniverse {
    /// mapping from server index to its lower bound
    pub tracked map: Map<nat, Tracked<MonotonicTimestampResource>>,
}

pub struct Quorum {
    pub servers: Set<nat>,
}

impl ServerUniverse {
    pub proof fn dummy() -> (tracked r: Self)
        ensures
            r.inv(),
            forall|q: Quorum|
                r.valid_quorum(q) ==> r.quorum_timestamp(q) >= Timestamp::spec_default(),
    {
        let tracked set = ServerUniverse { map: Map::tracked_empty() };
        set
    }

    pub open spec fn inv(self) -> bool {
        &&& forall|k: nat| self.map.contains_key(k) ==> self.map[k]@@ is LowerBound
        &&& self.map.dom().finite()
    }

    pub open spec fn dom(self) -> Set<nat> {
        self.map.dom()
    }

    pub open spec fn contains_key(self, idx: nat) -> bool {
        self.map.contains_key(idx)
    }

    pub open spec fn spec_index(self, idx: nat) -> Tracked<MonotonicTimestampResource> {
        self.map[idx]
    }

    pub open spec fn locs(self) -> Map<nat, int>
        recommends
            self.inv(),
    {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    pub open spec fn valid_quorum(self, q: Quorum) -> bool
        recommends
            self.inv(),
    {
        &&& q.inv()
        &&& q@ <= self.dom()
        &&& 2 * q@.len() > self.map.len()
    }

    pub open spec fn unanimous_quorum(self, q: Quorum, lb: Timestamp) -> bool
        recommends
            self.valid_quorum(q),
    {
        forall|idx: nat| q@.contains(idx) ==> self[idx]@@.timestamp() >= lb
    }

    pub open spec fn quorum_timestamp(self, q: Quorum) -> Timestamp
        recommends
            self.inv(),
            self.valid_quorum(q),
    {
        self.quorum_vals(q).find_unique_maximal(Self::ts_leq())
    }

    pub open spec fn quorum_vals(self, q: Quorum) -> Set<Timestamp>
        recommends
            self.inv(),
            self.valid_quorum(q),
    {
        self.map.restrict(q@).values().map(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
    }

    proof fn lemma_vals(self, q: Quorum) -> (r: (Set<Timestamp>, Timestamp))
        requires
            self.inv(),
            self.valid_quorum(q),
        ensures
            r.0 == self.quorum_vals(q),
            r.1 == self.quorum_timestamp(q),
            forall|idx: nat| q@.contains(idx) ==> r.0.contains(self[idx]@@.timestamp()),
            r.0.finite(),
            r.0.len() <= q@.len(),
    {
        let ts_leq = Self::ts_leq();
        let ts = self.quorum_timestamp(q);
        let lb_map = self.map.restrict(q@);
        let vals = self.quorum_vals(q);

        assert forall|idx: nat| q@.contains(idx) implies vals.contains(self[idx]@@.timestamp()) by {
            assert(self.map.restrict(q@).contains_key(idx));
            assert(self.map.restrict(q@).values().contains(self[idx]));
        }
        assert(vals.finite()) by {
            assert(self.map.dom().finite());
            axiom_set_intersect_finite(self.map.dom(), q@);
            assert(self.map.restrict(q@).dom() == self.map.dom().intersect(q@));
            assert(self.map.restrict(q@).dom().finite());
            lemma_values_finite(self.map.restrict(q@));
            self.map.restrict(q@).values().lemma_map_finite(
                |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
            );
        }

        // lb_map.dom().len() <= q@.len()
        assert(lb_map.dom() == self.map.dom().intersect(q@));
        assert(lb_map.dom() <= q@);
        assert(lb_map.dom().finite());
        lemma_len_subset(lb_map.dom(), q@);
        assert(lb_map.dom().len() <= q@.len());

        // lb_map.values().len() <= lb_map.dom().len()
        lb_map.lemma_values_len();
        assert(lb_map.values().len() <= lb_map.dom().len());
        assert(lb_map.values().finite());

        // vals <= lb_map.values().len()
        lemma_map_size_bound(
            lb_map.values(),
            vals,
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        );

        assert(vals.len() <= q@.len());
        (vals, ts)
    }

    proof fn lemma_quorum_timestamp_is_upper_bound(self, q: Quorum)
        requires
            self.inv(),
            self.valid_quorum(q),
        ensures
            forall|idx: nat|
                q@.contains(idx) ==> self.quorum_timestamp(q) >= self[idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q@).values().map(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        assert(forall|idx: nat| q@.contains(idx) ==> ts_leq(self[idx]@@.timestamp(), ts));
    }

    proof fn lemma_quorum_timestamp_witness(self, q: Quorum) -> (idx: nat)
        requires
            self.inv(),
            self.valid_quorum(q),
        ensures
            q@.contains(idx),
            self.quorum_timestamp(q) == self[idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q@).values().map(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        let witness_idx = choose|idx: nat| q@.contains(idx) && self[idx]@@.timestamp() == ts;
        assert(q@.contains(witness_idx));
        assert(self.quorum_timestamp(q) == self[witness_idx]@@.timestamp());
        witness_idx
    }

    proof fn lemma_quorum_witness_implies_lb(self, q: Quorum, witness_idx: nat)
        requires
            self.inv(),
            self.valid_quorum(q),
            q@.contains(witness_idx),
        ensures
            self.quorum_timestamp(q) >= self[witness_idx]@@.timestamp(),
    {
        let ts_leq = Self::ts_leq();
        let (vals, ts) = self.lemma_vals(q);

        self.map.restrict(q@).values().map(
            |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
        ).find_unique_maximal_ensures(ts_leq);
        vals.lemma_maximal_equivalent_greatest(ts_leq, ts);

        assert(forall|idx: nat| q@.contains(idx) ==> ts_leq(self[idx]@@.timestamp(), ts));
        assert(ts_leq(self[witness_idx]@@.timestamp(), ts));
    }

    pub open spec fn ts_leq() -> spec_fn(Timestamp, Timestamp) -> bool {
        |a: Timestamp, b: Timestamp| a <= b
    }

    pub open spec fn leq(self, other: ServerUniverse) -> bool
        recommends
            self.inv(),
            other.inv(),
    {
        &&& forall|k: nat| self.contains_key(k) ==> self[k]@@.timestamp() <= other[k]@@.timestamp()
        &&& self.locs() == other.locs()
    }

    proof fn lemma_leq_implies_validity(self, other: ServerUniverse, q: Quorum)
        requires
            self.inv(),
            other.inv(),
            self.leq(other) || other.leq(self),
        ensures
            self.valid_quorum(q) <==> other.valid_quorum(q),
    {
        assert(self.locs().dom() == other.locs().dom());
        assert(self.locs().dom() == self.dom());
        assert(self.dom() == other.dom());
        assert(self.map.len() == other.map.len());

        let dom = self.dom();
        let len = self.map.len();

        if self.valid_quorum(q) {
            assert(q@ <= dom);
            assert(2 * q@.len() > len);
        }
    }

    proof fn lemma_leq_retains_unanimity(self, other: ServerUniverse, q: Quorum, lb: Timestamp)
        requires
            self.inv(),
            other.inv(),
            self.leq(other),
            self.valid_quorum(q),
        ensures
            self.unanimous_quorum(q, lb) ==> other.unanimous_quorum(q, lb),
    {
        self.lemma_leq_implies_validity(other, q);
        assert(other.valid_quorum(q));
        if self.unanimous_quorum(q, lb) {
            assert forall|idx: nat| q@.contains(idx) implies other[idx]@@.timestamp() >= lb by {
                assert(self.contains_key(idx));
                assert(self[idx]@@.timestamp() <= other[idx]@@.timestamp());
            }
        }
    }

    pub proof fn lemma_leq_quorums(self, other: ServerUniverse, min: Timestamp)
        requires
            self.inv(),
            other.inv(),
            self.locs() == other.locs(),
            self.leq(other),
            forall|q: Quorum| self.valid_quorum(q) ==> self.quorum_timestamp(q) >= min,
        ensures
            forall|q: Quorum| other.valid_quorum(q) ==> other.quorum_timestamp(q) >= min,
    {
        assert forall|q: Quorum| other.valid_quorum(q) implies other.quorum_timestamp(q) >= min by {
            assert(other.valid_quorum(q));

            self.lemma_leq_implies_validity(other, q);
            assert(self.valid_quorum(q));
            assert(self.quorum_timestamp(q) >= min);

            let witness_idx = self.lemma_quorum_timestamp_witness(q);
            assert(self.contains_key(witness_idx));

            assert(forall|idx: nat|
                self.contains_key(idx) ==> other[idx]@@.timestamp() >= self[idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= self[witness_idx]@@.timestamp());
            assert(other[witness_idx]@@.timestamp() >= min);

            assert(exists|idx: nat| q@.contains(idx) ==> other[idx]@@.timestamp() >= min);
            other.lemma_quorum_witness_implies_lb(q, witness_idx);
            assert(other.quorum_timestamp(q) >= min);
        }
    }

    // This is the big quorum lemma
    pub proof fn lemma_quorum_lb(self, lb_quorum: Quorum, ts: Timestamp)
        requires
            self.inv(),
            self.valid_quorum(lb_quorum),
            self.unanimous_quorum(lb_quorum, ts),
        ensures
            forall|q: Quorum| self.valid_quorum(q) ==> self.quorum_timestamp(q) >= ts,
    {
        assert forall|q: Quorum| self.valid_quorum(q) implies self.quorum_timestamp(q) >= ts by {
            self.lemma_quorum_agree(lb_quorum, q, ts);
            self.lemma_quorum_timestamp_is_upper_bound(q);
            let witness_idx = self.lemma_quorum_intersection(lb_quorum, q);
            assert(q@.contains(witness_idx));
            assert(lb_quorum@.contains(witness_idx));
            assert(self[witness_idx]@@.timestamp() >= ts);
            self.lemma_quorum_witness_implies_lb(q, witness_idx);
            assert(self.quorum_timestamp(q) >= ts);
        }
    }

    proof fn lemma_quorum_intersection(self, q1: Quorum, q2: Quorum) -> (witness_idx: nat)
        requires
            self.inv(),
            self.valid_quorum(q1),
            self.valid_quorum(q2),
        ensures
            !q1@.disjoint(q2@),
            q1@.contains(witness_idx),
            q2@.contains(witness_idx),
    {
        assert(q1@ <= self.dom());
        assert(q2@ <= self.dom());
        assert(q1@.len() + q2@.len() > self.dom().len());
        vstd::assert_by_contradiction!(!q1@.disjoint(q2@), {
            let u = q1@.union(q2@);
            assert(u <= self.dom());
            lemma_set_disjoint_lens(q1@, q2@);

            assert(u.len() == q1@.len() + q2@.len());
            assert(u.len() > self.dom().len());
            lemma_len_subset(u, self.dom());
        });

        lemma_disjoint_iff_empty_intersection(q1@, q2@);
        let witness_idx = choose|idx: nat| q1@.contains(idx) && q2@.contains(idx);
        witness_idx
    }

    proof fn lemma_quorum_agree(self, q1: Quorum, q2: Quorum, lb: Timestamp)
        requires
            self.inv(),
            self.valid_quorum(q1),
            self.valid_quorum(q2),
            self.unanimous_quorum(q1, lb),
        ensures
            forall|idx: nat|
                q1@.contains(idx) && q2@.contains(idx) ==> self[idx]@@.timestamp() >= lb,
    {
        let restr = self.map.restrict(q1@.intersect(q2@));
        assert forall|idx: nat|
            q1@.contains(idx) && q2@.contains(idx) implies self[idx]@@.timestamp() >= lb by {
            assert(restr.contains_key(idx));
            vstd::assert_by_contradiction!(self[idx]@@.timestamp() >= lb,
            {

            });
        }
    }
}

impl Quorum {
    pub open spec fn view(self) -> Set<nat> {
        self.servers
    }

    pub open spec fn inv(self) -> bool {
        &&& self@.finite()
        &&& self@.len() > 0
        &&& !self@.is_empty()
    }
}

} // verus!
