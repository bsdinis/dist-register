use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use vstd::prelude::*;

use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

verus! {

pub struct ServerMap {
    /// mapping from server id to its lower bound
    pub tracked map: Map<u64, Tracked<MonotonicTimestampResource>>,
}

impl ServerMap {
    pub proof fn dummy() -> (tracked r: Self) {
        let tracked set = ServerMap { map: Map::tracked_empty() };
        set
    }

    pub open spec fn view(self) -> Map<u64, Timestamp> {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
    }

    pub open spec fn locs(self) -> Map<u64, int> {
        self.map.map_values(|r: Tracked<MonotonicTimestampResource>| r@.loc())
    }

    /// Return the minimum timestamp that a quorum can observe
    pub closed spec fn min_quorum_ts(self) -> Timestamp
    {
        self@.values().choose()
    }
}


}
