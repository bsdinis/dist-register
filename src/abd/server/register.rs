use std::sync::Arc;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;

use crate::abd::invariants;
use crate::abd::invariants::committed_to::WriteCommitment;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ServerToken;
use crate::abd::invariants::StateInvariant;
use crate::abd::proto::{GetResponse, GetTimestampResponse};
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::timestamp::Timestamp;

verus! {

pub struct RegisterIds {
    resource_loc: Loc,
    state_inv_id: int,
}

pub struct MonotonicRegisterInner<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub value: Option<u64>,
    pub timestamp: Timestamp,
    pub commitment: Tracked<WriteCommitment>,
    pub resource: Tracked<MonotonicTimestampResource>,
    pub state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    pub server_token: Tracked<ServerToken>,
}

impl<ML, RL> MonotonicRegisterInner<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(server_id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
        ensures
            r.value is None,
            r.timestamp == Timestamp::spec_default(),
            r.resource@@ is HalfRightToAdvance,
            r.inv(),
    {
        let tracked zero_commitment;
        let tracked resource;
        let tracked server_token;
        vstd::open_atomic_invariant!(&state_inv.borrow() => state => {
            proof {
                zero_commitment = state.commitments.zero_commitment();

                let ghost old_servers = state.servers;
                let ghost old_unclaimed = state.unclaimed_servers();
                let ghost old_tokens = state.server_tokens@;

                assume(state.unclaimed_servers().contains(server_id)); // XXX: server login
                resource = state.servers.split_auth(server_id);
                server_token = state.server_tokens.insert(server_id, resource.loc());
                assert forall |id| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                    assert(old_servers.contains_key(id)); // TRIGGER
                    // TRIGGER case search (?)
                    if old_unclaimed.contains(id) {
                    } else {
                    }
                }

                assert(state.server_tokens@ <= state.servers.locs());
                assert(state.servers.locs().dom() == state.servers.dom());
                assert forall |id| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                    assert(old_servers.contains_key(id)); // TRIGGER
                }

                old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());
            }
            // XXX: debug assert
            assert(state.inv());
        });
        MonotonicRegisterInner {
            value: None,
            timestamp: Timestamp::default(),
            resource: Tracked(resource),
            commitment: Tracked(zero_commitment),
            server_token: Tracked(server_token),
            state_inv,
        }
    }

    pub closed spec fn ids(self) -> RegisterIds {
        RegisterIds {
            resource_loc: self.resource@.loc(),
            state_inv_id: self.state_inv@.namespace(),
        }
    }

    pub closed spec fn resource_loc(self) -> Loc {
        self.resource@.loc()
    }

    pub closed spec fn state_inv_id(self) -> int {
        self.state_inv@.namespace()
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.timestamp == self.resource@@.timestamp()
        &&& self.timestamp == self.commitment@.key()
        &&& self.value == self.commitment@.value()
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.server_token@.value() == self.resource@.loc()
        &&& self.server_token@.id() == self.state_inv@.constant().server_tokens_id
    }

    #[allow(unused_variables)]
    pub fn read(&self) -> (r: GetResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
        ensures
            r.spec_value() == self.value,
            r.spec_timestamp() == self.timestamp,
            r.loc() == self.resource_loc(),
    {
        let tracked r = self.resource.borrow();
        let tracked lb = r.extract_lower_bound();

        proof {
            lb.lemma_lower_bound(r);
        }

        GetResponse::new(self.value.clone(), self.timestamp.clone(), Tracked(lb))
    }

    #[allow(unused_variables)]
    pub fn read_timestamp(&self) -> (r: GetTimestampResponse)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
        ensures
            r.spec_timestamp() == self.timestamp,
            r.loc() == self.resource_loc(),
    {
        let tracked r = self.resource.borrow();
        let tracked lb = r.extract_lower_bound();

        proof {
            lb.lemma_lower_bound(r);
        }

        GetTimestampResponse::new(self.timestamp.clone(), Tracked(lb))
    }

    pub fn write(
        self,
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
    ) -> (r: Self)
        requires
            self.resource@@ is HalfRightToAdvance,
            self.inv(),
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r.inv(),
            r.ids() == self.ids(),
            r.resource@@ is HalfRightToAdvance,
            timestamp > self.timestamp ==> r.timestamp == timestamp && r.value == value,
            timestamp <= self.timestamp ==> self == r,
    {
        if timestamp > self.timestamp {
            let tracked mut r = self.resource.get();
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let ghost old_servers = state.servers;
                    assert(state.server_tokens@ <= old_servers.locs());
                    assert(old_servers.locs().dom() == old_servers.dom());

                    self.server_token.borrow().agree(&state.server_tokens);
                    let ghost server_id = self.server_token@.key();
                    assert(state.servers.locs().contains_key(server_id));

                    let tracked mut other_half = state.servers.tracked_remove(server_id);
                    let ghost unchanged_servers = state.servers;
                    r.lemma_halves_agree(&other_half);
                    r.advance_halves(&mut other_half, timestamp);
                    state.servers.tracked_insert(server_id, other_half);

                    assert(old_servers.leq(state.servers)) by {
                        assert(old_servers.locs() == state.servers.locs());
                        assert forall |id| #[trigger] old_servers.contains_key(id)
                            implies state.servers[id]@@.timestamp() >= old_servers[id]@@.timestamp() by {
                            if id != server_id {
                                assert(unchanged_servers.contains_key(id)); // TRIGGER
                            }
                        }
                    }
                    assert forall |id: u64| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                        if id != server_id {
                            assert(unchanged_servers.contains_key(id));
                        }
                    }
                    assert forall |id: u64| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                        if id != server_id {
                            assert(unchanged_servers.contains_key(id));
                        }
                    }
                    old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());
                }
                // XXX: debug assert
                assert(state.inv());
            });

            MonotonicRegisterInner {
                value,
                timestamp,
                resource: Tracked(r),
                commitment,
                server_token: self.server_token,
                state_inv: self.state_inv,
            }
        } else {
            self
        }
    }
}

pub struct MonotonicRegisterInv {
    pub ids: RegisterIds,
}

impl<ML, RL> vstd::rwlock::RwLockPredicate<
    MonotonicRegisterInner<ML, RL>,
> for MonotonicRegisterInv where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    open spec fn inv(self, v: MonotonicRegisterInner<ML, RL>) -> bool {
        &&& v.inv()
        &&& v.ids() == self.ids
        &&& v.resource@@ is HalfRightToAdvance
    }
}

pub struct MonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    inner: RwLock<MonotonicRegisterInner<ML, RL>, MonotonicRegisterInv>,
}

impl<ML, RL> MonotonicRegister<ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(server_id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
    {
        let inner_reg = MonotonicRegisterInner::new(server_id, state_inv);

        let pred = Ghost(MonotonicRegisterInv { ids: inner_reg.ids() });
        assert(<MonotonicRegisterInv as vstd::rwlock::RwLockPredicate<_>>::inv(pred@, inner_reg));
        let inner = RwLock::new(inner_reg, pred);

        MonotonicRegister { inner }
    }

    pub closed spec fn resource_loc(self) -> Loc {
        self.inner.pred().ids.resource_loc
    }

    pub fn read(&self) -> (r: GetResponse)
        ensures
            r.loc() == self.resource_loc(),
    {
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read();
        handle.release_read();

        res
    }

    pub fn read_timestamp(&self) -> (r: GetTimestampResponse)
        ensures
            r.loc() == self.resource_loc(),
    {
        let handle = self.inner.acquire_read();
        let inner = handle.borrow();
        let res = inner.read_timestamp();
        handle.release_read();

        res
    }

    pub fn write(
        &self,
        value: Option<u64>,
        timestamp: Timestamp,
        commitment: Tracked<WriteCommitment>,
    ) -> (r: Tracked<MonotonicTimestampResource>)
        requires
            commitment@.key() == timestamp,
            commitment@.value() == value,
        ensures
            r@@ is LowerBound,
            r@.loc() == self.resource_loc(),
            timestamp <= r@@.timestamp(),
    {
        let (guard, handle) = self.inner.acquire_write();

        let new_value = guard.write(value, timestamp, commitment);
        let tracked r = new_value.resource.borrow();
        let tracked lower_bound = r.extract_lower_bound();

        proof {
            lower_bound.lemma_lower_bound(r);
        }

        handle.release_write(new_value);

        Tracked(lower_bound)
    }
}

} // verus!
