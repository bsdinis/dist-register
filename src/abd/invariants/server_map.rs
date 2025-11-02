#[allow(unused_imports)]
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::prelude::*;

verus! {

pub struct ServerMap {
    /// mapping from server index to its lower bound
    pub tracked map: Map<nat, Tracked<MonotonicTimestampResource>>,
}

impl ServerMap {
    pub proof fn dummy() -> (tracked r: Self)
        ensures
            r.inv(),
            forall |q: Quorum| r.valid_quorum(q) ==> q.timestamp() >= (Timestamp { seqno: 0, client_id: 0}),
    {
        let tracked set = ServerMap { map: Map::tracked_empty() };
        set
    }

    pub open spec fn inv(self) -> bool {
        &&& forall |k: nat| self.map.contains_key(k) ==> self.map[k]@@ is LowerBound
    }

    pub open spec fn view(self) -> Map<nat, Timestamp>
        recommends self.inv(),
    {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
    }

    pub open spec fn locs(self) -> Map<nat, int>
        recommends self.inv(),
    {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    pub open spec fn valid_quorum(self, q: Quorum) -> bool
        recommends self.inv()
    {
        &&& q.inv()
        &&& q.submap <= self.map
        &&& q.locs() <= self.locs()
        &&& q.n == self.map.len()
    }

    pub open spec fn leq(self, other: ServerMap) -> bool
        recommends
            self.inv(),
            other.inv(),
            self.locs() == other.locs()
    {
        forall |k: nat| self.map.contains_key(k) ==> self.map[k]@@.timestamp() <= other.map[k]@@.timestamp()
    }

    pub proof fn lemma_leq_quorums(self, other: ServerMap, min: Timestamp)
        requires
            self.inv(),
            other.inv(),
            self.locs() == other.locs(),
            self.leq(other),
            forall |q: Quorum| self.valid_quorum(q) ==> min <= q.timestamp(),
        ensures
            forall |q: Quorum| other.valid_quorum(q) ==> min <= q.timestamp(),
    {
        assume(forall |q: Quorum| other.valid_quorum(q) ==> min <= q.timestamp())
    }
}

pub struct Quorum {
    pub tracked submap: Map<nat, Tracked<MonotonicTimestampResource>>,
    pub ghost n: nat,
}

impl Quorum {
    pub open spec fn view(self) -> Map<nat, Timestamp>
        recommends self.inv(),
    {
        self.submap.map_values(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
    }

    pub open spec fn locs(self) -> Map<nat, int>
        recommends self.inv(),
    {
        self.submap.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    pub open spec fn inv(self) -> bool {
        // quorum intersection
        &&& 2 * self.submap.len() > self.n
        &&& self.submap.len() > 0
        &&& !self.submap.is_empty()
        &&& forall |k: nat| self.submap.contains_key(k) ==> self.submap[k]@@ is LowerBound
    }

    pub open spec fn timestamp(self) -> Timestamp
        recommends self.inv()
    {
        self.submap
            .values()
            .map(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
            .find_unique_maximal(|a: Timestamp, b: Timestamp| a <= b)
    }
}

}
