use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use vstd::prelude::*;

use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

verus! {

pub struct ServerMap {
    /// mapping from server id to its resource
    pub map: GhostMapAuth<u64, Tracked<MonotonicTimestampResource>>,
}

impl ServerMap {
    pub proof fn dummy() -> (tracked r: Self) {
        let tracked map = ServerMap { map: GhostMapAuth::dummy() };
        map
    }

    pub open spec fn view(self) -> Map<u64, Timestamp> {
        self.map@.map_values(|r: Tracked<MonotonicTimestampResource>| r@@.timestamp())
    }

    pub open spec fn id(self) -> int {
        self.map.id()
    }

    pub proof fn reserve(tracked &mut self, server_id: u64) -> (r: ServerOwns)
        requires
            !old(self)@.contains_key(server_id)
        ensures
            old(self).id() == self.id(),
            r.id() == self.id(),
            self@.contains_pair(server_id, Timestamp::spec_default()),
            r@ == (server_id, Timestamp::spec_default()),
    {
        let tracked resource = Tracked(MonotonicTimestampResource::alloc());
        let tracked singleton = self.map.insert(map![server_id => resource]);
        ServerOwns { singleton }
    }
}

pub struct ServerOwns {
    tracked singleton: GhostSubmap<u64, Tracked<MonotonicTimestampResource>>,
}

impl ServerOwns {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.singleton@.dom().is_singleton()
    }

    pub closed spec fn id(self) -> int {
        self.singleton.id()
    }

    pub closed spec fn view(self) -> (u64, Timestamp) {
        let (id, ts) = self.singleton@.kv_pairs().choose();
        (id, ts@@.timestamp())
    }
}

}
