use std::collections::{BTreeMap, BTreeSet};

use vstd::prelude::*;
use vstd::resource::Loc;

#[cfg(verus_only)]
use crate::abd::invariants::quorum::Quorum;
use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::proto::{GetResponse, WriteResponse};
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::verdist::rpc::replies::ReplyAccumulator;

verus! {

#[allow(dead_code)]
pub struct ReadAccumulator {
    // EXEC state
    /// The max response from the first round
    /// This is the value that will ultimately be returned
    max_resp: Option<GetResponse>,
    /// The set of servers that we know are >= max_resp.timestamp()
    agree_with_max: BTreeSet<u64>,
    /// Number of received get replies
    n_get_replies: usize,
    // TODO: finangle
    wb_replies: BTreeMap<(u64, u64), WriteResponse>,
    // Spec state
    // TODO: persistent server_tokens_submap (MonotonicMap?)
    /// Constructed view over the server map
    ///
    /// In the beginning, we only know that every quorum is bounded bellow by the watermark
    /// Over time, we monotonically gain knowledge that every quorum is bounded bellow by
    /// `max_resp.timestamp()`
    servers: Tracked<ServerUniverse>,
    /// The original watermark at creation time
    old_watermark: Ghost<MonotonicTimestampResource>,
    /// The quorum being constructed
    quorum: Tracked<Set<u64>>,
}

impl ReadAccumulator {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        old_watermark: Ghost<MonotonicTimestampResource>,
    ) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    old_watermark@@.timestamp() <= servers@.quorum_timestamp(q)
                },
        ensures
            r.spec_n_get_replies() == 0,
            r.spec_n_wb_replies() == 0,
            r.server_locs() == servers@.locs(),
            r.watermark_loc() == old_watermark@.loc(),
    {
        ReadAccumulator {
            max_resp: None,
            agree_with_max: BTreeSet::new(),
            n_get_replies: 0,
            wb_replies: BTreeMap::new(),
            servers,
            old_watermark,
            quorum: Tracked(Set::tracked_empty()),
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.quorum@.finite()
        &&& self.max_resp is None ==> self.quorum@.is_empty()
        &&& self.quorum@ <= self.servers@.dom()
        &&& self.agree_with_max@.finite()
        &&& self.agree_with_max@ <= self.quorum@
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
        &&& forall|q: Quorum| #[trigger]
            self.servers@.valid_quorum(q) ==> {
                self.old_watermark@@.timestamp() <= self.servers@.quorum_timestamp(q)
            }
        &&& self.max_resp is Some ==> forall|id| #[trigger]
            self.agree_with_max@.contains(id) ==> {
                self.servers@[id]@@.timestamp() == self.max_resp->Some_0.spec_timestamp()
            }
        &&& self.n_get_replies as nat == self.quorum@.len()
        &&& self.wb_replies@.dom().finite()
        &&& self.wb_replies@.len() == self.spec_n_wb_replies()
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers@.locs()
    }

    pub closed spec fn old_watermark(self) -> MonotonicTimestampResource {
        self.old_watermark@
    }

    pub closed spec fn watermark_loc(self) -> Loc {
        self.old_watermark@.loc()
    }

    pub closed spec fn quorum(self) -> Quorum {
        Quorum::from_set(self.quorum@)
    }

    pub fn max_resp(&self) -> (r: &GetResponse)
        requires
            self.spec_n_get_replies() > 0,
    {
        proof {
            use_type_invariant(self);
        }
        self.max_resp.as_ref().unwrap()
    }

    pub fn agree_with_max(&self) -> &BTreeSet<u64> {
        &self.agree_with_max
    }

    fn update_max_resp_and_quorum(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        quorum: &mut Tracked<Set<u64>>,
        n_get_replies: &mut usize,
        resp: GetResponse,
        server_id: u64,
    )
        requires
            !old(quorum)@.contains(server_id),
            old(quorum)@.finite(),
            old(quorum)@.len() == *old(n_get_replies),
        ensures
            *max_resp is Some,
            *old(max_resp) is Some ==> {
                let old_max_ts = old(max_resp)->Some_0.spec_timestamp();
                let new_max_ts = max_resp->Some_0.spec_timestamp();
                &&& resp.spec_timestamp() > old_max_ts ==> {
                    &&& *max_resp == Some(resp)
                    &&& agree_with_max@ == set![server_id]
                }
                &&& resp.spec_timestamp() == old_max_ts ==> {
                    &&& *max_resp == *old(max_resp)
                    &&& agree_with_max@ == old(agree_with_max)@.insert(server_id)
                }
                &&& resp.spec_timestamp() < old_max_ts ==> {
                    &&& *max_resp == *old(max_resp)
                    &&& agree_with_max@ == old(agree_with_max)@
                }
                &&& old_max_ts <= new_max_ts
            },
            *old(max_resp) is None ==> {
                &&& *max_resp == Some(resp)
                &&& agree_with_max@ == set![server_id]
            },
            quorum@.finite(),
            quorum@ == old(quorum).insert(server_id),
            quorum@.len() == *n_get_replies,
            *n_get_replies == *old(n_get_replies) + 1,
        no_unwind
    {
        let mut new_val = None;
        if let Some(max_resp) = max_resp.as_ref() {
            if resp.timestamp() > max_resp.timestamp() {
                new_val = Some(resp);
            } else if resp.timestamp() == max_resp.timestamp() {
                agree_with_max.insert(server_id);
            }
        } else {
            new_val = Some(resp);
        }

        if new_val.is_some() {
            *max_resp = new_val;
            agree_with_max.clear();
            agree_with_max.insert(server_id);
        }
        proof {
            quorum.borrow_mut().tracked_insert(server_id);
        }
        assume(n_get_replies < usize::MAX);
        *n_get_replies += 1
    }

    proof fn update_servers(
        tracked servers: &mut ServerUniverse,
        old_watermark: &MonotonicTimestampResource,
        agree_with_max: Set<u64>,
        max_resp: &Option<GetResponse>,
        server_id: u64,
        tracked lb: MonotonicTimestampResource,
    )
        requires
            old(servers).inv(),
            old(servers).is_lb(),
            old(servers).contains_key(server_id),
            old(servers)[server_id]@.loc() == lb.loc(),
            old(servers)[server_id]@@.timestamp() <= lb@.timestamp(),
            agree_with_max <= old(servers).dom(),
            forall|q: Quorum| #[trigger]
                old(servers).valid_quorum(q) ==> {
                    old_watermark@.timestamp() <= old(servers).quorum_timestamp(q)
                },
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    old(servers)[id]@@.timestamp() == max_resp->Some_0.spec_timestamp()
                },
            lb@ is LowerBound,
            !agree_with_max.contains(server_id),
        ensures
            servers.inv(),
            servers.is_lb(),
            servers.dom() == old(servers).dom(),
            servers.locs() == old(servers).locs(),
            forall|id| #[trigger]
                servers.contains_key(id) ==> {
                    &&& id != server_id ==> servers[id]@@.timestamp() == old(
                        servers,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> servers[id]@@.timestamp() == lb@.timestamp()
                },
            servers[server_id]@@.timestamp() == lb@.timestamp(),
            old(servers).leq(*servers),
            forall|q: Quorum| #[trigger]
                servers.valid_quorum(q) ==> {
                    old_watermark@.timestamp() <= servers.quorum_timestamp(q)
                },
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    servers[id]@@.timestamp() == max_resp->Some_0.spec_timestamp()
                },
    {
        let ghost old_servers = *old(servers);
        assert(forall|q: Quorum| #[trigger]
            servers.valid_quorum(q) ==> {
                old_watermark@.timestamp() <= old_servers.quorum_timestamp(q)
            });
        if max_resp is Some {
            assert(forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    servers[id]@@.timestamp() == max_resp->Some_0.spec_timestamp()
                });
        }
        servers.tracked_update_lb(server_id, lb);
        assert(forall|id| #[trigger]
            servers.contains_key(id) ==> {
                &&& id != server_id ==> servers[id]@@.timestamp() == old_servers[id]@@.timestamp()
                &&& id == server_id ==> servers[id]@@.timestamp() == lb@.timestamp()
            });
        assert(old_servers.leq(*servers));
        old_servers.lemma_leq_quorums(*servers, old_watermark@.timestamp());
        assert(forall|q: Quorum| #[trigger]
            servers.valid_quorum(q) ==> { old_watermark@.timestamp() <= servers.quorum_timestamp(q)
            });
        if max_resp is Some {
            assert forall|id| #[trigger]
                agree_with_max.contains(id) implies servers[id]@@.timestamp()
                == max_resp->Some_0.spec_timestamp() by {
                assert(servers.contains_key(id));
                if id != server_id {
                    assert(id != server_id ==> servers[id]@@.timestamp()
                        == old_servers[id]@@.timestamp())
                } else {
                    assert(!agree_with_max.contains(id));
                }
            }
        }
    }

    fn lemma_unanimous(&self)
        requires
            self.servers@.valid_quorum(Quorum::from_set(self.quorum@)),
            self.quorum@ == self.agree_with_max@,
            self.max_resp is Some,
        ensures
            forall|q: Quorum| #[trigger]
                self.servers@.valid_quorum(q) ==> {
                    self.old_watermark@@.timestamp() <= self.servers@.quorum_timestamp(q)
                },
    {
        proof {
            use_type_invariant(self);

            let ghost quorum = Quorum::from_set(self.quorum@);
            let ghost timestamp = self.max_resp->Some_0.spec_timestamp();

            assert forall|id| #[trigger]
                quorum@.contains(id) implies self.servers@[id]@@.timestamp() >= timestamp by {
                assert(self.agree_with_max@.contains(id));
            }

            self.servers@.lemma_quorum_lb(quorum, timestamp);
        }
    }

    fn insert_get(&mut self, id: (u64, u64), resp: GetResponse)
        ensures
    // TODO: this must be asserted by come constant associated with this

            self.server_locs() == old(self).server_locs(),
            self.watermark_loc() == old(self).watermark_loc(),
            self.spec_n_get_replies() == old(self).spec_n_get_replies() + 1,
            self.spec_n_wb_replies() == old(self).spec_n_wb_replies(),
        no_unwind
    {
        resp.lemma_get_response();
        assert(resp.lb()@ is LowerBound);
        let Tracked(lb) = resp.duplicate_lb();
        assert(lb@ is LowerBound);
        proof {
            use_type_invariant(&*self);

            // ASSUMPTIONS

            // HACK
            // We could instead derive these by agreement on resp.server_token
            // TODO(chan_pred)
            assume(self.servers.contains_key(id.1));
            assume(self.servers[id.1]@.loc() == resp.lb().loc());
            // This requires the request <-> reply matching predicate on the channel
            // see TODO(proto_lb)
            assume(self.servers[id.1]@@.timestamp() <= resp.lb()@.timestamp());
            // This requires the uniqueness of the request tag
            // TODO(chan_pred)
            assume(!self.quorum@.contains(id.1));

            Self::update_servers(
                self.servers.borrow_mut(),
                self.old_watermark.borrow(),
                self.agree_with_max@,
                &self.max_resp,
                id.1,
                lb,
            );
        }

        Self::update_max_resp_and_quorum(
            &mut self.max_resp,
            &mut self.agree_with_max,
            &mut self.quorum,
            &mut self.n_get_replies,
            resp,
            id.1,
        );
    }

    pub closed spec fn spec_n_get_replies(self) -> nat {
        self.quorum@.len()
    }

    pub fn n_get_replies(&self) -> (r: usize)
        ensures
            r == self.spec_n_get_replies(),
    {
        proof {
            use_type_invariant(self);
        }
        self.n_get_replies
    }

    fn insert_write(&mut self, id: (u64, u64), resp: WriteResponse)
        ensures
    // TODO: this must be asserted by come constant associated with this

            self.server_locs() == old(self).server_locs(),
            self.watermark_loc() == old(self).watermark_loc(),
            self.wb_replies@ == old(self).wb_replies@.insert(id, resp),
            self.spec_n_get_replies() == old(self).spec_n_get_replies(),
            self.spec_n_wb_replies() == old(self).spec_n_wb_replies() + 1,
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
            assume(!self.wb_replies@.contains_key(id));
            assert(self.wb_replies@.insert(id, resp).contains_key(id));
            assert(self.wb_replies@.insert(id, resp).len() == self.wb_replies@.len() + 1);
        }
        self.wb_replies.insert(id, resp);
    }

    pub closed spec fn spec_n_wb_replies(self) -> nat {
        self.wb_replies@.len()
    }

    pub fn n_wb_replies(&self) -> (r: usize)
        ensures
            r == self.spec_n_wb_replies(),
    {
        proof {
            use_type_invariant(self);
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        }
        self.wb_replies.len()
    }
}

pub struct ReadAccumGetPhase(ReadAccumulator);

pub struct ReadAccumWbPhase(ReadAccumulator);

impl ReadAccumGetPhase {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        old_watermark: Ghost<MonotonicTimestampResource>,
    ) -> (r: Self)
        requires
            servers@.inv(),
            servers@.is_lb(),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    old_watermark@@.timestamp() <= servers@.quorum_timestamp(q)
                },
        ensures
            r.spec_n_replies() == 0,
            r.server_locs() == servers@.locs(),
            r.watermark_loc() == old_watermark@.loc(),
    {
        ReadAccumGetPhase(ReadAccumulator::new(servers, old_watermark))
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.0.spec_n_wb_replies() == 0
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.0.server_locs()
    }

    pub closed spec fn watermark_loc(self) -> Loc {
        self.0.watermark_loc()
    }

    pub fn destruct(self) -> (r: ReadAccumulator)
        ensures
            r.spec_n_wb_replies() == 0,
    {
        proof { use_type_invariant(&self) }

        self.0
    }
}

impl ReadAccumWbPhase {
    pub fn new(accum: ReadAccumulator) -> (r: Self)
        requires
            accum.spec_n_wb_replies() == 0,
        ensures
            r.spec_n_replies() == 0,
            r.server_locs() == accum.server_locs(),
            r.watermark_loc() == accum.watermark_loc(),
    {
        ReadAccumWbPhase(accum)
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.0.server_locs()
    }

    pub closed spec fn watermark_loc(self) -> Loc {
        self.0.watermark_loc()
    }

    pub fn destruct(self) -> (r: ReadAccumulator) {
        self.0
    }
}

impl ReplyAccumulator<(u64, u64)> for ReadAccumGetPhase {
    type T = GetResponse;

    fn insert(&mut self, id: (u64, u64), resp: GetResponse)
        ensures
            self.server_locs() == old(self).server_locs(),
            self.watermark_loc() == old(self).watermark_loc(),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.0.insert_get(id, resp);
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.0.spec_n_get_replies()
    }

    fn n_replies(&self) -> usize {
        self.0.n_get_replies()
    }
}

impl ReplyAccumulator<(u64, u64)> for ReadAccumWbPhase {
    type T = WriteResponse;

    fn insert(&mut self, id: (u64, u64), resp: WriteResponse)
        ensures
            self.server_locs() == old(self).server_locs(),
            self.watermark_loc() == old(self).watermark_loc(),
    {
        self.0.insert_write(id, resp);
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.0.spec_n_wb_replies()
    }

    fn n_replies(&self) -> usize {
        self.0.n_wb_replies()
    }
}

pub struct BadAccumulator<T> {
    replies: BTreeMap<(u64, u64), T>,
}

impl<T> ReplyAccumulator<(u64, u64)> for BadAccumulator<T> {
    type T = T;

    #[allow(unused_variables)]
    fn insert(&mut self, id: (u64, u64), resp: T) {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, resp);
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.replies@.len()
    }

    fn n_replies(&self) -> usize {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        self.replies.len()
    }
}

impl<T> BadAccumulator<T> {
    pub fn new() -> (r: Self)
        ensures
            r.spec_n_replies() == 0,
    {
        BadAccumulator { replies: BTreeMap::new() }
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), T>)
        ensures
            r@.len() == self.spec_n_replies(),
    {
        self.replies
    }
}

} // verus!
