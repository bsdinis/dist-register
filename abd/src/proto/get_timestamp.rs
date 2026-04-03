use crate::invariants::quorum::ServerUniverse;
use crate::invariants::ServerToken;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

pub struct GetTimestampRequest {
    #[allow(unused)]
    servers: Tracked<ServerUniverse>,
}

pub struct GetTimestampResponse {
    timestamp: Timestamp,
    #[allow(unused)]
    lb: Tracked<MonotonicTimestampResource>,
    #[allow(unused)]
    server_token: Tracked<ServerToken>,
}

#[allow(unused)]
impl GetTimestampRequest {
    pub fn new(servers: Tracked<ServerUniverse>) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
        ensures
            r.servers() == servers@,
    {
        GetTimestampRequest { servers }
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.servers@.eq(other.servers@)
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
        assume(a.servers@.inv());  // TODO(verus): type invariants on spec items
        ServerUniverse::lemma_eq_refl(a.servers@)
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
        assume(a.servers@.inv());  // TODO(verus): type invariants on spec items
        assume(b.servers@.inv());  // TODO(verus): type invariants on spec items
        assume(c.servers@.inv());  // TODO(verus): type invariants on spec items
        ServerUniverse::lemma_eq_trans(a.servers@, b.servers@, c.servers@)
    }
}

#[allow(unused)]
impl GetTimestampResponse {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.lb@@ is LowerBound
        &&& self.lb@@.timestamp() == self.timestamp
        &&& self.lb@.loc() == self.server_token@.value()
    }

    pub closed spec fn lb(self) -> MonotonicTimestampResource {
        self.lb@
    }

    pub closed spec fn spec_timestamp(self) -> Timestamp {
        self.timestamp
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

    pub fn new(
        timestamp: Timestamp,
        lb: Tracked<MonotonicTimestampResource>,
        server_token: Tracked<ServerToken>,
    ) -> (r: Self)
        requires
            lb@@ is LowerBound,
            lb@@.timestamp() == timestamp,
            lb@.loc() == server_token@.value(),
        ensures
            r.lb() == lb@,
            r.spec_timestamp() == timestamp,
            r.spec_server_token() == server_token@,
            r.server_id() == server_token@.key(),
            r.server_token_id() == server_token@.id(),
            r.loc() == server_token@.value(),
    {
        GetTimestampResponse { timestamp, lb, server_token }
    }

    pub fn timestamp(&self) -> (ts: Timestamp)
        ensures
            ts == self.spec_timestamp(),
    {
        self.timestamp.clone()
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        &&& self.timestamp == other.timestamp
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

impl Clone for GetTimestampRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        let tracked new_servers;
        proof {
            use_type_invariant(self);
            new_servers = self.servers.borrow().extract_lbs();
            ServerUniverse::lemma_eq_timestamp_lb_is_eq(new_servers, self.servers@);
        }
        GetTimestampRequest { servers: Tracked(new_servers) }
    }
}

impl Clone for GetTimestampResponse {
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
        GetTimestampResponse::new(self.timestamp.clone(), Tracked(new_lb), Tracked(server_token))
    }
}

} // verus!
impl std::fmt::Debug for GetTimestampRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampRequest").finish()
    }
}

impl std::fmt::Debug for GetTimestampResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GetTimestampResponse")
            .field("timestamp", &self.timestamp)
            .finish()
    }
}
