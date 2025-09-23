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

    /*
    pub open spec fn loc(self) -> int {
        self.map.id()
    }
    */

    /* TODO: unclear if this is needed
    pub proof fn reserve(tracked &mut self, server_id: u64, tracked resource: MonotonicTimestampResource) -> (r: ServerOwns)
        requires
            !old(self)@.contains_key(server_id),
            resource@.timestamp() == Timestamp::spec_default(),
            resource is LowerBound,
        ensures
            old(self).id() == self.id(),
            r.id() == self.id(),
            self@.contains_pair(server_id, Timestamp::spec_default()),
            r@ == (server_id, Timestamp::spec_default()),
            self@[server_id] == resource,
    {
        let map_to_insert = map![server_id => Tracked(resource)];
        let tracked singleton = self.map.insert(map_to_insert);
        assert(singleton@ =~= map_to_insert);
        assume(singleton@.kv_pairs().finite());
        assume(singleton@.kv_pairs().len() == 1);
        assume(singleton@.kv_pairs().choose().0 == server_id);
        assume(singleton@.kv_pairs().choose().1 == resource);
        ServerOwns { singleton }
    }
    */

    /// Return the minimum timestamp that a quorum can observe
    pub closed spec fn min_quorum_ts(self) -> Timestamp
    {
        self@.values().choose() // TODO: make server_map a universe
    }
}


}
