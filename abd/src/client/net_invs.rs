use std::collections::{BTreeMap, BTreeSet};

use vstd::invariant::InvariantPredicate;
#[cfg(verus_only)]
use vstd::map_lib::lemma_values_finite;
use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;

#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
use crate::invariants::quorum::ServerUniverse;
#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::Timestamp;

use crate::proto::{GetResponse, GetTimestampResponse, Response, WriteResponse};
#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use verdist::rpc::replies::ReplyAccumulator;

verus! {

#[allow(unused_variables, dead_code)]
pub ghost struct ReadPred {
    pub server_locs: Map<u64, Loc>,
    pub commitment_id: Loc,
    pub server_tokens_id: Loc,
    pub min_timestamp: Timestamp,
}

impl ReadPred {
    pub open spec fn from_state(
        state: StatePredicate,
        old_watermark: MonotonicTimestampResource,
    ) -> ReadPred {
        ReadPred {
            server_locs: state.server_locs,
            commitment_id: state.commitments_ids.commitment_id,
            server_tokens_id: state.server_tokens_id,
            min_timestamp: old_watermark@.timestamp(),
        }
    }
}

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
    // TODO(qed/read/phase_2/write_inv): add write inv
    wb_replies: BTreeMap<(u64, u64), WriteResponse>,
    // Spec state
    // TODO(qed/read): persistent server_tokens_submap (MonotonicMap?)
    /// Constructed view over the server map
    ///
    /// In the beginning, we only know that every quorum is bounded bellow by the watermark
    /// Over time, we monotonically gain knowledge that every quorum is bounded bellow by
    /// `max_resp.timestamp()`
    servers: Tracked<ServerUniverse>,
    /// Lower bound for the server tokens
    server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
    /// The original watermark at creation time
    min_timestamp: Ghost<Timestamp>,
    /// The id of the commitment map
    commitment_id: Ghost<Loc>,
}

impl InvariantPredicate<ReadPred, ReadAccumulator> for ReadPred {
    open spec fn inv(pred: ReadPred, v: ReadAccumulator) -> bool {
        pred == v.constant()
    }
}

impl ReadAccumulator {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        #[allow(unused_variables)]
        read_pred: Ghost<ReadPred>,
    ) -> (r: Self)
        requires
            read_pred@.server_locs == servers@.locs(),
            read_pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    read_pred@.min_timestamp <= servers@.quorum_timestamp(q)
                },
        ensures
            r.constant() == read_pred@,
            r.spec_n_get_replies() == 0,
            r.spec_n_wb_replies() == 0,
            r.server_locs() == servers@.locs(),
            r.server_tokens_id() == server_tokens@.id(),
    {
        ReadAccumulator {
            max_resp: None,
            agree_with_max: BTreeSet::new(),
            n_get_replies: 0,
            wb_replies: BTreeMap::new(),
            servers,
            server_tokens,
            min_timestamp: Ghost(read_pred@.min_timestamp),
            commitment_id: Ghost(read_pred@.commitment_id),
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.max_resp is None <==> self.agree_with_max@.is_empty()
        &&& self.agree_with_max@.is_empty() <==> self.n_get_replies@ == 0
        &&& self.agree_with_max@ <= self.servers@.dom()
        &&& self.agree_with_max@.finite()
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
        &&& self.server_tokens@@ <= self.servers@.locs()
        &&& forall|q: Quorum| #[trigger]
            self.servers@.valid_quorum(q) ==> {
                self.min_timestamp@ <= self.servers@.quorum_timestamp(q)
            }
        &&& self.max_resp is Some ==> {
            let resp = self.max_resp->Some_0;
            &&& forall|id| #[trigger]
                self.agree_with_max@.contains(id) ==> {
                    self.servers@[id]@@.timestamp() == resp.spec_timestamp()
                }
            &&& resp.spec_commitment().id() == self.commitment_id@
            &&& resp.server_token_id() == self.server_tokens_id()
        }
        &&& self.wb_replies@.dom().finite()
        &&& self.wb_replies@.len() == self.spec_n_wb_replies()
    }

    pub open spec fn constant(self) -> ReadPred {
        ReadPred {
            server_locs: self.server_locs(),
            commitment_id: self.commitment_id(),
            server_tokens_id: self.server_tokens_id(),
            min_timestamp: self.spec_min_timestamp(),
        }
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers@.locs()
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment_id@
    }

    pub closed spec fn server_tokens_id(self) -> Loc {
        self.server_tokens@.id()
    }

    pub closed spec fn quorum(self) -> Quorum {
        Quorum::from_set(self.agree_with_max@)
    }

    pub closed spec fn spec_agree_with_max(self) -> Set<u64> {
        self.agree_with_max@
    }

    pub fn servers_lb(&self) -> (r: Tracked<ServerUniverse>)
        requires
            self.spec_n_get_replies() > 0,
        ensures
            self.server_locs() == r@.locs(),
            self.servers().leq(r@),
            self.servers().inv(),
            r@.leq(self.servers()),
            r@.inv(),
            r@.is_lb(),
            r@.valid_quorum(self.quorum()) ==> r@.unanimous_quorum(
                self.quorum(),
                self.spec_max_timestamp(),
            ),
            forall|q: Quorum|
                {
                    &&& #[trigger] self.servers().valid_quorum(q) <==> #[trigger] r@.valid_quorum(q)
                    &&& #[trigger] self.servers().valid_quorum(q)
                        ==> self.servers().quorum_timestamp(q) == r@.quorum_timestamp(q)
                },
    {
        let tracked lbs;
        proof {
            use_type_invariant(self);
            lbs = self.servers.borrow().extract_lbs();
            lbs.lemma_locs();
            let ghost quorum = self.quorum();
            let ghost max_ts = self.spec_max_timestamp();
            assert forall|id| #[trigger] quorum@.contains(id) implies lbs[id]@@.timestamp()
                == max_ts by {
                assert(self.servers@.contains_key(id));
                assert(lbs.contains_key(id));
            }

            lbs.lemma_eq(self.servers());
        }
        Tracked(lbs)
    }

    pub fn lemma_quorum(&self)
        requires
            self.spec_n_get_replies() > 0,
        ensures
            self.quorum().inv(),
            self.quorum()@ <= self.server_locs().dom(),
            self.quorum()@.len() == self.spec_agree_with_max().len(),
    {
        proof {
            use_type_invariant(self);
        }
    }

    pub fn max_resp(&self) -> (r: &GetResponse)
        requires
            self.spec_n_get_replies() > 0,
        ensures
            r == self.spec_max_resp(),
            r.spec_commitment().id() == self.commitment_id(),
    {
        proof {
            use_type_invariant(self);
        }
        self.max_resp.as_ref().unwrap()
    }

    pub closed spec fn spec_max_resp(&self) -> GetResponse
        recommends
            self.spec_n_get_replies() > 0,
    {
        self.max_resp->Some_0
    }

    pub open spec fn spec_max_timestamp(&self) -> Timestamp
        recommends
            self.spec_n_get_replies() > 0,
    {
        self.spec_max_resp().spec_timestamp()
    }

    pub closed spec fn spec_min_timestamp(&self) -> Timestamp {
        self.min_timestamp@
    }

    pub fn agree_with_max(&self) -> (r: &BTreeSet<u64>)
        ensures
            r@ == self.spec_agree_with_max(),
    {
        &self.agree_with_max
    }

    fn update_max_resp_and_quorum(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        n_get_replies: &mut usize,
        resp: GetResponse,
        server_id: u64,
    )
        requires
            !old(agree_with_max)@.contains(server_id),
            old(agree_with_max)@.finite(),
            old(agree_with_max)@.is_empty() <==> old(n_get_replies)@ == 0,
            *old(max_resp) is None <==> old(agree_with_max)@.is_empty(),
        ensures
            *max_resp is Some,
            agree_with_max@.finite(),
            !agree_with_max@.is_empty(),
            *n_get_replies == *old(n_get_replies) + 1,
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
        assume(n_get_replies < usize::MAX);  // XXX: integer overflow
        *n_get_replies += 1
    }

    proof fn update_servers(
        tracked servers: &mut ServerUniverse,
        min_timestamp: Timestamp,
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
                old(servers).valid_quorum(q) ==> { min_timestamp <= old(servers).quorum_timestamp(q)
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
                servers.valid_quorum(q) ==> { min_timestamp <= servers.quorum_timestamp(q) },
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    servers[id]@@.timestamp() == max_resp->Some_0.spec_timestamp()
                },
    {
        let ghost old_servers = *old(servers);
        assert(forall|q: Quorum| #[trigger]
            servers.valid_quorum(q) ==> { min_timestamp <= old_servers.quorum_timestamp(q) });
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
        old_servers.lemma_leq_quorums(*servers, min_timestamp);
        assert(forall|q: Quorum| #[trigger]
            servers.valid_quorum(q) ==> { min_timestamp <= servers.quorum_timestamp(q) });
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

    #[allow(dead_code)]  // TODO: unsure we need this
    fn lemma_unanimous(&self)
        requires
            self.servers@.valid_quorum(self.quorum()),
            self.max_resp is Some,
        ensures
            forall|q: Quorum| #[trigger]
                self.servers@.valid_quorum(q) ==> {
                    self.min_timestamp@ <= self.servers@.quorum_timestamp(q)
                },
    {
        proof {
            use_type_invariant(self);

            let ghost quorum = self.quorum();
            let ghost timestamp = self.max_resp->Some_0.spec_timestamp();

            assert forall|id| #[trigger]
                quorum@.contains(id) implies self.servers@[id]@@.timestamp() >= timestamp by {
                assert(self.agree_with_max@.contains(id));
            }

            self.servers@.lemma_quorum_lb(quorum, timestamp);
        }
    }

    pub fn lemma_max_timestamp(&self)
        requires
            self.spec_n_get_replies() > 0,
        ensures
            self.servers().inv(),
            self.servers().valid_quorum(self.quorum()) ==> {
                let q_ts = self.servers().quorum_timestamp(self.quorum());
                &&& q_ts == self.spec_max_timestamp()
                &&& self.spec_min_timestamp() <= q_ts
            },
    {
        proof {
            use_type_invariant(self);
            if self.servers().valid_quorum(self.quorum()) {
                assert(self.servers().inv());
                assert(self.max_resp is Some);
                assert(forall|id| #[trigger]
                    self.agree_with_max@.contains(id) ==> {
                        self.servers@[id]@@.timestamp() == self.spec_max_timestamp()
                    });
                assert(forall|id| #[trigger]
                    self.quorum()@.contains(id) ==> {
                        self.servers()[id]@@.timestamp() == self.spec_max_timestamp()
                    });
                let quorum_map = self.servers().map.restrict(self.quorum()@);
                assert(quorum_map.dom() == self.quorum()@);
                let quorum_vals = self.servers().quorum_vals(self.quorum());
                assert(quorum_vals == quorum_map.values().map(
                    |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
                ));
                assert(quorum_vals.finite()) by {
                    assert(quorum_map.dom().finite());
                    lemma_values_finite(quorum_map);
                    assert(quorum_map.values().finite());
                    quorum_map.values().lemma_map_finite(
                        |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
                    );
                };
                assume(quorum_vals.len() > 0);  // TODO(verus): this needs a verus lemma
                assert forall|id| #[trigger]
                    quorum_map.contains_key(id) implies quorum_map[id]@@.timestamp()
                    == self.spec_max_timestamp() by {
                    assert(self.quorum()@.contains(id));
                    assert(self.agree_with_max@.contains(id));
                    assert(self.servers()[id]@@.timestamp() == self.spec_max_timestamp());
                }
                assert(forall|v| quorum_vals.contains(v) ==> v == self.spec_max_timestamp());
                assert(quorum_vals.find_unique_maximal(ServerUniverse::ts_leq())
                    == self.spec_max_timestamp()) by {
                    quorum_vals.find_unique_maximal_ensures(ServerUniverse::ts_leq())
                };
                assert(self.servers().quorum_timestamp(self.quorum()) == self.spec_max_timestamp());
            }
        }
    }

    fn insert_get(&mut self, id: (u64, u64), resp: GetResponse)
        requires
            ReadPred::inv(old(self).constant(), *old(self)),
            resp.server_id() == id.1,
            old(self).constant().server_tokens_id == resp.server_token_id(),
            old(self).constant().server_locs.contains_key(resp.server_id()),
            old(self).constant().server_locs[resp.server_id()] == resp.loc(),
            resp.spec_commitment().id() == old(self).commitment_id(),
        ensures
            ReadPred::inv(self.constant(), *self),
            self.constant() == old(self).constant(),
            self.spec_n_get_replies() == old(self).spec_n_get_replies() + 1,
            self.spec_n_wb_replies() == old(self).spec_n_wb_replies(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }

        resp.lemma_get_response();
        resp.lemma_token_agree(&mut self.server_tokens);
        assert(resp.lb()@ is LowerBound);
        let Tracked(lb) = resp.duplicate_lb();
        assert(lb@ is LowerBound);
        proof {
            // ASSUMPTIONS
            // HACK
            // This requires the request <-> reply matching predicate on the channel
            // see TODO(proto_lb)
            assume(self.servers[id.1]@@.timestamp() <= resp.spec_timestamp());
            // This requires the uniqueness of the request tag
            assume(!self.agree_with_max@.contains(id.1));

            Self::update_servers(
                self.servers.borrow_mut(),
                self.min_timestamp@,
                self.agree_with_max@,
                &self.max_resp,
                id.1,
                lb,
            );
        }

        Self::update_max_resp_and_quorum(
            &mut self.max_resp,
            &mut self.agree_with_max,
            &mut self.n_get_replies,
            resp,
            id.1,
        );
    }

    pub closed spec fn spec_n_get_replies(self) -> nat {
        self.n_get_replies@ as nat
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
        requires
            ReadPred::inv(old(self).constant(), *old(self)),
        ensures
            ReadPred::inv(self.constant(), *self),
            self.constant() == old(self).constant(),
            self.wb_replies@ == old(self).wb_replies@.insert(id, resp),
            self.spec_n_get_replies() == old(self).spec_n_get_replies(),
            self.spec_n_wb_replies() == old(self).spec_n_wb_replies() + 1,
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
            // TODO(qed/read/phase_2): write back phase
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
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        read_pred: Ghost<ReadPred>,
    ) -> (r: Self)
        requires
            read_pred@.server_locs == servers@.locs(),
            read_pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    read_pred@.min_timestamp <= servers@.quorum_timestamp(q)
                },
        ensures
            r.constant() == read_pred@,
            r.spec_n_replies() == 0,
    {
        ReadAccumGetPhase(ReadAccumulator::new(servers, server_tokens, read_pred))
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.0.spec_n_wb_replies() == 0
    }

    pub closed spec fn constant(self) -> ReadPred {
        self.0.constant()
    }

    pub fn destruct(self) -> (r: ReadAccumulator)
        ensures
            r.constant() == self.constant(),
            r.spec_n_wb_replies() == 0,
            r.spec_n_get_replies() == self.spec_n_replies(),
    {
        proof { use_type_invariant(&self) }

        self.0
    }
}

impl InvariantPredicate<ReadPred, ReadAccumGetPhase> for ReadPred {
    open spec fn inv(pred: ReadPred, v: ReadAccumGetPhase) -> bool {
        pred == v.constant()
    }
}

impl ReadAccumWbPhase {
    pub fn new(accum: ReadAccumulator) -> (r: Self)
        requires
            accum.spec_n_wb_replies() == 0,
        ensures
            r.spec_n_replies() == 0,
            r.constant() == accum.constant(),
    {
        ReadAccumWbPhase(accum)
    }

    pub closed spec fn constant(self) -> ReadPred {
        self.0.constant()
    }

    pub fn destruct(self) -> (r: ReadAccumulator)
        ensures
            r.constant() == self.constant(),
    {
        self.0
    }
}

impl InvariantPredicate<ReadPred, ReadAccumWbPhase> for ReadPred {
    open spec fn inv(pred: ReadPred, v: ReadAccumWbPhase) -> bool {
        pred == v.constant()
    }
}

impl ReplyAccumulator<(u64, u64), ReadPred> for ReadAccumGetPhase {
    type T = Response;

    #[verifier::exec_allows_no_decreases_clause]
    fn insert(
        &mut self,
        #[allow(unused_variables)]
        pred: Ghost<ReadPred>,
        id: (u64, u64),
        resp: Response,
    )
        ensures
            self.constant() == old(self).constant(),
    {
        proof {
            use_type_invariant(&*self);
        }
        assert(self.constant() == pred@);
        assume(resp is Get);
        let resp = match resp {
            Response::Get(g) => g,
            _ => {
                assert(false);
                loop {
                }
            },
        };
        // TODO(qed/read/phase_1/chan_pred): add these to the recv_inv
        assume(resp.server_id() == id.1);
        assume(resp.spec_commitment().id() == self.constant().commitment_id);
        assume(self.constant().server_locs.contains_key(resp.server_id()));
        assume(self.constant().server_locs[resp.server_id()] == resp.loc());
        assume(self.constant().server_tokens_id == resp.server_token_id());
        self.0.insert_get(id, resp);
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.0.spec_n_get_replies()
    }

    fn n_replies(&self) -> usize {
        self.0.n_get_replies()
    }
}

impl ReplyAccumulator<(u64, u64), ReadPred> for ReadAccumWbPhase {
    type T = Response;

    #[verifier::exec_allows_no_decreases_clause]
    fn insert(
        &mut self,
        #[allow(unused_variables)]
        pred: Ghost<ReadPred>,
        id: (u64, u64),
        resp: Response,
    )
        ensures
            self.constant() == old(self).constant(),
    {
        assume(resp is Write);
        let resp = match resp {
            Response::Write(w) => w,
            _ => {
                assert(false);
                loop {
                }
            },
        };
        self.0.insert_write(id, resp);
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.0.spec_n_wb_replies()
    }

    fn n_replies(&self) -> usize {
        self.0.n_wb_replies()
    }
}

pub struct GetTimestampAccumulator {
    replies: BTreeMap<(u64, u64), GetTimestampResponse>,
}

pub struct WriteAccumulator {
    replies: BTreeMap<(u64, u64), ()>,
}

impl ReplyAccumulator<(u64, u64), EmptyPred> for GetTimestampAccumulator {
    type T = Response;

    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response) {
        assume(resp is GetTimestamp);
        let resp = match resp {
            Response::GetTimestamp(g) => g,
            _ => {
                assert(false);
                loop {
                }
            },
        };
        // TODO(qed): remove later on
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

impl GetTimestampAccumulator {
    pub fn new() -> (r: Self)
        ensures
            r.spec_n_replies() == 0,
    {
        GetTimestampAccumulator { replies: BTreeMap::new() }
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), GetTimestampResponse>)
        ensures
            r@.len() == self.spec_n_replies(),
    {
        self.replies
    }
}

impl ReplyAccumulator<(u64, u64), EmptyPred> for WriteAccumulator {
    type T = Response;

    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response) {
        assume(resp is Write);
        let resp = match resp {
            Response::Write(w) => w,
            _ => {
                assert(false);
                loop {
                }
            },
        };
        // TODO(qed): remove later on
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, ());
    }

    closed spec fn spec_n_replies(self) -> nat {
        self.replies@.len()
    }

    fn n_replies(&self) -> usize {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        self.replies.len()
    }
}

impl WriteAccumulator {
    pub fn new() -> (r: Self)
        ensures
            r.spec_n_replies() == 0,
    {
        WriteAccumulator { replies: BTreeMap::new() }
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), ()>)
        ensures
            r@.len() == self.spec_n_replies(),
    {
        self.replies
    }
}

pub struct EmptyPred;

impl InvariantPredicate<EmptyPred, GetTimestampAccumulator> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: GetTimestampAccumulator) -> bool {
        true
    }
}

impl InvariantPredicate<EmptyPred, WriteAccumulator> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: WriteAccumulator) -> bool {
        true
    }
}

} // verus!
