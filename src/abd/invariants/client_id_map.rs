use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use vstd::prelude::*;

verus! {

pub struct ClientMap {
    /// mapping from client_id => max seqno allocated
    /// is also used to reserve client ids
    pub map: GhostMapAuth<u64, u64>
}

impl ClientMap {
    pub proof fn dummy() -> (tracked r: Self) {
        let tracked map = ClientMap { map: GhostMapAuth::dummy() };
        map
    }

    pub open spec fn view(self) -> Map<u64, u64> {
        self.map@
    }

    pub open spec fn id(self) -> int {
        self.map.id()
    }

    pub proof fn reserve(tracked &mut self, client_id: u64) -> (r: ClientOwns)
        requires
            !old(self)@.contains_key(client_id)
        ensures
            old(self).id() == self.id(),
            r.id() == self.id(),
            self@.contains_pair(client_id, 0),
            r@ == (client_id, 0u64),
    {
        let tracked singleton = self.map.insert(map![client_id => 0]);
        ClientOwns { singleton }
    }
}

pub struct ClientOwns {
    tracked singleton: GhostSubmap<u64, u64>,
}

impl ClientOwns {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.singleton@.dom().is_singleton()
    }

    pub closed spec fn view(self) -> (u64, u64) {
        self.singleton@.kv_pairs().choose()
    }

    pub closed spec fn id(self) -> int {
        self.singleton.id()
    }
}

}
