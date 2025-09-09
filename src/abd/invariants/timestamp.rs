use vstd::map::Map;

use crate::abd::proto::Timestamp;
use crate::abd::resource::ghost_set::Exclusive;
use crate::abd::resource::ghost_set::GhostSetAuth;
use crate::abd::resource::ghost_set::GhostSubset;
use crate::abd::resource::ghost_set::Monotonic;

use vstd::prelude::*;

verus! {

pub struct TimestampAuth {
    // linked
    tracked timestamp_auth: GhostSetAuth<Timestamp, Exclusive>,
    tracked timestamp_witness: GhostSetAuth<Timestamp, Monotonic>,
}

pub struct TimestampOwns {
    tracked singleton: GhostSubset<Timestamp, Exclusive>,
}

pub struct TimestampWitness {
    tracked singleton: GhostSubset<Timestamp, Monotonic>,
}


impl TimestampAuth {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.timestamp_auth@ == self.timestamp_witness@
    }

    pub closed spec fn witness_id(self) -> int {
        self.timestamp_witness.id()
    }

    pub closed spec fn auth_id(self) -> int {
        self.timestamp_auth.id()
    }

    pub closed spec fn view(self) -> Set<Timestamp> {
        self.timestamp_auth@
    }

    pub proof fn insert(tracked &mut self, timestamp: Timestamp) -> (tracked result: TimestampOwns)
        requires
            !old(self)@.contains(timestamp)
        ensures
            self@ == old(self)@.insert(timestamp),
            result.id() == self.auth_id(),
            result@ == timestamp
    {
        let singleton = set![timestamp];
        let tracked owns = self.timestamp_auth.insert(singleton);
        self.timestamp_auth.insert(singleton);
        TimestampOwns { singleton: owns }
    }

}

impl TimestampOwns {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.singleton@.is_singleton()
    }

    pub closed spec fn view(self) -> Timestamp {
        self.singleton@.choose()
    }

    pub closed spec fn id(self) -> int {
        self.singleton.id()
    }
}

impl TimestampWitness {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        self.singleton@.is_singleton()
    }

    pub closed spec fn view(self) -> Timestamp {
        self.singleton@.choose()
    }

    pub closed spec fn id(self) -> int {
        self.singleton.id()
    }

    pub axiom fn cheat(timestamp: Timestamp) -> (tracked result: Self)
        ensures
            result@ == timestamp
    ;
}

}
