use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;
use verdist::rpc::proto::TaggedMessage;

use vstd::pervasive::unreached;
use vstd::prelude::*;
use vstd::resource::map::{GhostPersistentPointsTo, GhostPersistentSubmap};
use vstd::resource::Loc;

verus! {

pub struct WriteRequest {
    value: Option<u64>,
    timestamp: Timestamp,
    #[allow(unused)]
    commitment: Tracked<
        WriteCommitment,
    >,
    // TODO(qed/read/proto): add lower bound to write request
}

#[allow(unused)]
pub struct WriteResponse {
    #[allow(unused)]
    lb: Tracked<MonotonicTimestampResource>,
    #[allow(unused)]
    server_token: Tracked<ServerToken>,
    // TODO(qed/read/phase_2):
    //  - return the ghost request that was sent in the request to tie down the lb here
}

#[allow(unused)]
impl WriteRequest {
    pub fn new(
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
    ) -> (r: Self)
        requires
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.spec_timestamp() == timestamp,
            r.spec_value() == value,
            r.commitment_id() == commitment@.id(),
    {
        WriteRequest { value, timestamp, commitment }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.commitment@.key() == self.timestamp
        &&& self.commitment@.value() == self.value
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment@.id()
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn spec_value(self) -> Option<u64> {
        self.value
    }

    pub fn destruct(self) -> (r: (Option<u64>, Timestamp, Tracked<WriteCommitment>))
        ensures
            r.0 == self.spec_value(),
            r.1 == self.spec_timestamp(),
            r.2@.key() == self.spec_timestamp(),
            r.2@.value() == self.spec_value(),
            r.2@.id() == self.commitment_id(),
    {
        proof {
            use_type_invariant(&self);
        }

        (self.value, self.timestamp, self.commitment)
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.value == other.value
        &&& self.timestamp == other.timestamp
        &&& self.commitment@.id() == other.commitment@.id()
        &&& self.commitment@@ == other.commitment@@
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
    }
}

#[allow(unused)]
impl WriteResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@.loc() == self.server_token@.value()
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.lb@@.timestamp()
    }

    pub closed spec fn spec_server_token(self) -> ServerToken {
        self.server_token@
    }

    pub closed spec fn server_token_id(self) -> Loc {
        self.server_token@.id()
    }

    pub closed spec fn server_id(self) -> u64 {
        self.server_token@.key()
    }

    pub open spec fn loc(self) -> Loc {
        self.lb().loc()
    }

    pub fn new(lb: Tracked<MonotonicTimestampResource>, server_token: Tracked<ServerToken>) -> (r:
        Self)
        requires
            lb@@ is LowerBound,
            lb@.loc() == server_token@.value(),
        ensures
            r.lb() == lb@,
            r.lb().loc() == lb@.loc(),
            r.spec_timestamp() == lb@@.timestamp(),
            r.spec_server_token() == server_token@,
            r.server_id() == server_token@.key(),
            r.server_token_id() == server_token@.id(),
    {
        WriteResponse { lb, server_token }
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.lb@.loc() == other.lb@.loc()
        &&& self.lb@@.timestamp()
            == other.lb@@.timestamp()
        // TODO server token

    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
    }
}

impl Clone for WriteResponse {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_lb;
        let tracked server_token;
        proof {
            use_type_invariant(self);
            new_lb = self.lb.borrow().extract_lower_bound();
            server_token = self.server_token.borrow().duplicate();
        }
        WriteResponse::new(Tracked(new_lb), Tracked(server_token))
    }
}

impl Clone for WriteRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_commitment;
        proof {
            use_type_invariant(self);
            new_commitment = self.commitment.borrow().duplicate()
        }
        WriteRequest {
            value: self.value.clone(),
            timestamp: self.timestamp.clone(),
            commitment: Tracked(new_commitment),
        }
    }
}

} // verus!
impl std::fmt::Debug for WriteRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteRequest")
            .field("value", &self.value)
            .field("timestamp", &self.timestamp)
            .finish()
    }
}
impl std::fmt::Debug for WriteResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteResponse").finish()
    }
}
