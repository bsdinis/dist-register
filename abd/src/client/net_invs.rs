use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestProof;
#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::GetResponse;
use crate::proto::GetTimestampResponse;
use crate::proto::Response;
use crate::proto::WriteResponse;
#[cfg(verus_only)]
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::timestamp::Timestamp;

use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
use verdist::rpc::replies::ReplyAccumulator;

#[cfg(verus_only)]
use verdist::rpc::proto::TaggedMessage;
use vstd::invariant::InvariantPredicate;
#[cfg(verus_only)]
use vstd::map_lib::lemma_values_finite;
use vstd::prelude::*;
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::std_specs::btree::increasing_seq;

verus! {

#[allow(unused_variables, dead_code)]
pub ghost struct ReadPred<C: Channel<K = ChannelInv>> {
    pub server_locs: Map<u64, Loc>,
    pub commitment_id: Loc,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub min_timestamp: Timestamp,
    pub channels: Map<C::Id, C>,
    pub get_request_id: u64,
}

impl<C: Channel<K = ChannelInv>> ReadPred<C> {
    pub open spec fn new(
        state: StatePredicate,
        channels: Map<C::Id, C>,
        old_watermark: MonotonicTimestampResource,
        get_request_id: u64,
    ) -> ReadPred<C> {
        ReadPred {
            server_locs: state.server_locs,
            commitment_id: state.commitments_ids.commitment_id,
            request_map_id: state.request_map_ids.request_auth_id,
            server_tokens_id: state.server_tokens_id,
            min_timestamp: old_watermark@.timestamp(),
            channels,
            get_request_id,
        }
    }
    // TODO: type invariant here relating the channels.dom() to the server_locs.dom()

}

#[allow(dead_code)]
pub struct ReadAccumulator<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    // EXEC state
    /// The max response from the first round
    /// This is the value that will ultimately be returned
    max_resp: Option<GetResponse>,
    /// The set of servers that we know are >= max_resp.timestamp()
    agree_with_max: BTreeSet<u64>,
    /// Received get replies
    get_replies: BTreeSet<C::Id>,
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
    /// channels of the pool this accumulator is working with
    channels: Ghost<Map<C::Id, C>>,
    /// get request proof
    get_request: Tracked<RequestProof>,
}

impl<C> InvariantPredicate<ReadPred<C>, ReadAccumulator<C>> for ReadPred<C> where
    C: Channel<K = ChannelInv, Id = (u64, u64)>,
 {
    open spec fn inv(pred: ReadPred<C>, v: ReadAccumulator<C>) -> bool {
        pred == v.constant()
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> ReadAccumulator<C> {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        get_request: Tracked<RequestProof>,
        #[allow(unused_variables)]
        read_pred: Ghost<ReadPred<C>>,
    ) -> (r: Self)
        requires
            read_pred@.server_locs == servers@.locs(),
            read_pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            get_request@.id() == read_pred@.request_map_id,
            get_request@.key().1 == read_pred@.get_request_id,
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().inv(),
            get_request@.value()->Get_0.servers().eq_timestamp(servers@),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    read_pred@.min_timestamp <= servers@.quorum_timestamp(q)
                },
            forall|c_id| #[trigger]
                read_pred@.channels.contains_key(c_id) ==> {
                    let c = read_pred@.channels[c_id];
                    &&& c_id.0 == get_request@.key().0
                    &&& c.constant().request_map_id == read_pred@.request_map_id
                    &&& c.constant().commitment_id == read_pred@.commitment_id
                    &&& c.constant().server_tokens_id == read_pred@.server_tokens_id
                    &&& c.constant().server_locs == read_pred@.server_locs
                },
        ensures
            r.constant() == read_pred@,
            r.spec_get_replies().is_empty(),
            r.spec_wb_replies().is_empty(),
            r.server_locs() == servers@.locs(),
            r.server_tokens_id() == server_tokens@.id(),
    {
        ReadAccumulator {
            max_resp: None,
            agree_with_max: BTreeSet::new(),
            get_replies: BTreeSet::new(),
            wb_replies: BTreeMap::new(),
            servers,
            server_tokens,
            min_timestamp: Ghost(read_pred@.min_timestamp),
            commitment_id: Ghost(read_pred@.commitment_id),
            channels: Ghost(read_pred@.channels),
            get_request,
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.max_resp is None <==> self.agree_with_max@.is_empty()
        &&& self.get_replies@.finite()
        &&& forall|cid| #[trigger] self.get_replies@.contains(cid) ==> cid.0 == self.client_id()
        &&& forall|cid|
            {
                &&& !#[trigger] self.get_replies@.contains(cid)
                &&& #[trigger] self.servers@.contains_key(cid.1)
                &&& cid.0 == self.client_id()
            } ==> {
                self.servers@[cid.1]@@.timestamp()
                    == self.get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
            }
        &&& self.agree_with_max@.is_empty() <==> self.get_replies@.is_empty()
        &&& self.agree_with_max@ <= self.servers@.dom()
        &&& self.agree_with_max@ <= self.get_replies@.map(|id: (u64, u64)| id.1)
        &&& self.agree_with_max@.finite()
        &&& self.servers@.inv()
        &&& self.servers@.is_lb()
        &&& self.server_tokens@@ <= self.servers@.locs()
        &&& self.get_request@.value().req_type() is Get
        &&& self.get_request@.value()->Get_0.servers().inv()
        &&& self.get_request@.value()->Get_0.servers().leq(self.servers@)
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
        &&& self.wb_replies@.dom() == self.spec_wb_replies()
        &&& forall|c_id| #[trigger]
            self.channels@.contains_key(c_id) ==> {
                let c = self.channels@[c_id];
                &&& c_id.0 == self.client_id()
                &&& c.constant().request_map_id == self.request_map_id()
                &&& c.constant().commitment_id == self.commitment_id()
                &&& c.constant().server_tokens_id == self.server_tokens_id()
                &&& c.constant().server_locs == self.server_locs()
            }
    }

    pub open spec fn constant(self) -> ReadPred<C> {
        ReadPred {
            server_locs: self.server_locs(),
            commitment_id: self.commitment_id(),
            request_map_id: self.request_map_id(),
            server_tokens_id: self.server_tokens_id(),
            min_timestamp: self.spec_min_timestamp(),
            channels: self.channels(),
            get_request_id: self.get_request_id(),
        }
    }

    pub closed spec fn client_id(self) -> u64 {
        self.get_request@.key().0
    }

    pub closed spec fn get_request_id(self) -> u64 {
        self.get_request@.key().1
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers@.locs()
    }

    pub closed spec fn request_map_id(self) -> Loc {
        self.get_request@.id()
    }

    pub closed spec fn commitment_id(self) -> Loc {
        self.commitment_id@
    }

    pub closed spec fn server_tokens_id(self) -> Loc {
        self.server_tokens@.id()
    }

    pub closed spec fn channels(self) -> Map<C::Id, C> {
        self.channels@
    }

    pub closed spec fn quorum(self) -> Quorum {
        Quorum::from_set(self.agree_with_max@)
    }

    pub closed spec fn spec_agree_with_max(self) -> Set<u64> {
        self.agree_with_max@
    }

    pub fn servers_lb(&self) -> (r: Tracked<ServerUniverse>)
        requires
            !self.spec_get_replies().is_empty(),
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
            !self.spec_get_replies().is_empty(),
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
            !self.spec_get_replies().is_empty(),
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
            !self.spec_get_replies().is_empty(),
    {
        self.max_resp->Some_0
    }

    pub open spec fn spec_max_timestamp(&self) -> Timestamp
        recommends
            !self.spec_get_replies().is_empty(),
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
            !self.spec_get_replies().is_empty(),
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

    proof fn update_servers(
        tracked servers: &mut ServerUniverse,
        req_servers: ServerUniverse,
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
            req_servers.inv(),
            req_servers.leq(*old(servers)),
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
            req_servers.leq(*servers),
            old(servers).leq(*servers),
            forall|id| #[trigger]
                servers.contains_key(id) ==> {
                    &&& id != server_id ==> servers[id]@@.timestamp() == old(
                        servers,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> servers[id]@@.timestamp() == lb@.timestamp()
                },
            servers[server_id]@@.timestamp() == lb@.timestamp(),
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
        assert(req_servers.leq(old_servers));
        assert(old_servers.leq(*servers));
        ServerUniverse::lemma_leq_trans(req_servers, old_servers, *servers);
    }

    fn update_max_resp_and_quorum(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        get_replies: &mut BTreeSet<C::Id>,
        resp: GetResponse,
        id: (u64, u64),
    )
        requires
            !old(get_replies)@.contains(id),
            !old(agree_with_max)@.contains(id.1),
            old(get_replies)@.finite(),
            forall|cid| #[trigger] old(get_replies)@.contains(cid) ==> cid.0 == id.0,
            old(agree_with_max)@.finite(),
            old(agree_with_max)@.is_empty() <==> old(get_replies)@.is_empty(),
            old(agree_with_max)@ <= old(get_replies)@.map(|id: (u64, u64)| id.1),
            *old(max_resp) is None <==> old(get_replies)@.is_empty(),
        ensures
            *max_resp is Some,
            get_replies@.finite(),
            forall|cid| #[trigger] get_replies@.contains(cid) ==> cid.0 == id.0,
            agree_with_max@.finite(),
            !agree_with_max@.is_empty(),
            get_replies@ == old(get_replies)@.insert(id),
            agree_with_max@ <= get_replies@.map(|id: (u64, u64)| id.1),
            *old(max_resp) is Some ==> {
                let old_max_ts = old(max_resp)->Some_0.spec_timestamp();
                let new_max_ts = max_resp->Some_0.spec_timestamp();
                &&& resp.spec_timestamp() > old_max_ts ==> {
                    &&& *max_resp == Some(resp)
                    &&& agree_with_max@ == set![id.1]
                }
                &&& resp.spec_timestamp() == old_max_ts ==> {
                    &&& *max_resp == *old(max_resp)
                    &&& agree_with_max@ == old(agree_with_max)@.insert(id.1)
                }
                &&& resp.spec_timestamp() < old_max_ts ==> {
                    &&& *max_resp == *old(max_resp)
                    &&& agree_with_max@ == old(agree_with_max)@
                }
                &&& old_max_ts <= new_max_ts
            },
            *old(max_resp) is None ==> {
                &&& *max_resp == Some(resp)
                &&& agree_with_max@ == set![id.1]
            },
        no_unwind
    {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());

        let mut new_val = None;
        if let Some(max_resp) = max_resp.as_ref() {
            if resp.timestamp() > max_resp.timestamp() {
                new_val = Some(resp);
            } else if resp.timestamp() == max_resp.timestamp() {
                agree_with_max.insert(id.1);
            }
        } else {
            new_val = Some(resp);
        }

        if new_val.is_some() {
            *max_resp = new_val;
            agree_with_max.clear();
            agree_with_max.insert(id.1);
        }
        get_replies.insert(id);

        assert(forall|server_id| #[trigger]
            agree_with_max@.contains(server_id) ==> get_replies@.contains((id.0, server_id)));
    }

    fn insert_get_aux(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        get_replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        servers: &mut Tracked<ServerUniverse>,
        server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>,
        #[allow(unused_variables)]
        min_timestamp: &Ghost<Timestamp>,
        #[allow(unused_variables)]
        commitment_id: &Ghost<Loc>,
        #[allow(unused_variables)]
        channels: &Ghost<Map<C::Id, C>>,
        #[allow(unused_variables)]
        get_request: &Tracked<RequestProof>,
        id: (u64, u64),
        resp: Response,
    )
        requires
            get_request@.key().0 == id.0,
            resp.server_id() == id.1,
            resp.req_type() is Get,
            resp.request() == get_request@.value(),
            resp.get().spec_commitment().id() == commitment_id@,
            *old(max_resp) is None <==> old(agree_with_max)@.is_empty(),
            old(get_replies)@.finite(),
            forall|cid| #[trigger]
                old(get_replies)@.contains(cid) ==> cid.0 == get_request@.key().0,
            forall|cid|
                {
                    &&& !#[trigger] old(get_replies)@.contains(cid)
                    &&& old(servers)@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    old(servers)@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
            old(agree_with_max)@.is_empty() <==> old(get_replies)@.is_empty(),
            old(agree_with_max)@ <= old(servers)@.dom(),
            old(agree_with_max)@ <= old(get_replies)@.map(|id: (u64, u64)| id.1),
            old(agree_with_max)@.finite(),
            old(servers)@.inv(),
            old(servers)@.is_lb(),
            old(server_tokens)@@ <= old(servers)@.locs(),
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().inv(),
            get_request@.value()->Get_0.servers().leq(old(servers)@),
            forall|q: Quorum| #[trigger]
                old(servers)@.valid_quorum(q) ==> {
                    min_timestamp@ <= old(servers)@.quorum_timestamp(q)
                },
            *old(max_resp) is Some ==> {
                let resp = old(max_resp)->Some_0;
                &&& forall|id| #[trigger]
                    old(agree_with_max)@.contains(id) ==> {
                        old(servers)@[id]@@.timestamp() == resp.spec_timestamp()
                    }
                &&& resp.spec_commitment().id() == commitment_id@
                &&& resp.server_token_id() == old(server_tokens)@.id()
            },
            forall|c_id| #[trigger]
                channels@.contains_key(c_id) ==> {
                    let c = channels@[c_id];
                    &&& c_id.0 == get_request@.key().0
                    &&& c.constant().request_map_id == get_request@.id()
                    &&& c.constant().commitment_id == commitment_id@
                    &&& c.constant().server_tokens_id == old(server_tokens)@.id()
                    &&& c.constant().server_locs == old(servers)@.locs()
                },
            old(server_tokens)@.id() == resp.get().server_token_id(),
            old(servers)@.locs().contains_key(resp.server_id()),
            old(servers)@.locs()[resp.server_id()] == resp.get().loc(),
        ensures
            servers@.locs() == old(servers)@.locs(),
            server_tokens@.id() == old(server_tokens)@.id(),
            get_replies@ == old(get_replies)@.insert(id),
            *max_resp is None <==> agree_with_max@.is_empty(),
            get_replies@.finite(),
            forall|cid| #[trigger] get_replies@.contains(cid) ==> cid.0 == get_request@.key().0,
            forall|cid|
                {
                    &&& !#[trigger] get_replies@.contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    servers@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
            agree_with_max@.is_empty() <==> get_replies@.is_empty(),
            agree_with_max@ <= servers@.dom(),
            agree_with_max@ <= get_replies@.map(|id: (u64, u64)| id.1),
            agree_with_max@.finite(),
            servers@.inv(),
            servers@.is_lb(),
            server_tokens@@ <= servers@.locs(),
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().leq(servers@),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> { min_timestamp@ <= servers@.quorum_timestamp(q) },
            *max_resp is Some ==> {
                let resp = max_resp->Some_0;
                &&& forall|id| #[trigger]
                    agree_with_max@.contains(id) ==> {
                        servers@[id]@@.timestamp() == resp.spec_timestamp()
                    }
                &&& resp.spec_commitment().id() == commitment_id@
                &&& resp.server_token_id() == server_tokens@.id()
            },
            forall|c_id| #[trigger]
                channels@.contains_key(c_id) ==> {
                    let c = channels@[c_id];
                    &&& c_id.0 == get_request@.key().0
                    &&& c.constant().request_map_id == get_request@.id()
                    &&& c.constant().commitment_id == commitment_id@
                    &&& c.constant().server_tokens_id == server_tokens@.id()
                    &&& c.constant().server_locs == servers@.locs()
                },
            server_tokens@.id() == resp.get().server_token_id(),
            servers@.locs().contains_key(resp.server_id()),
            servers@.locs()[resp.server_id()] == resp.get().loc(),
            resp.get().spec_commitment().id() == commitment_id@,
        no_unwind
    {
        proof {
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
            assume(get_request@.value()->Get_0.servers().inv());  // TODO(verus): spec type invariants
        }

        if get_replies.contains(&id) {
            return ;
        }
        let r = resp.destruct_get();

        r.lemma_get_response();
        r.lemma_token_agree(server_tokens);
        assert(r.lb()@ is LowerBound);
        let Tracked(lb) = r.duplicate_lb();
        assert(lb@ is LowerBound);

        proof {
            Self::update_servers(
                servers.borrow_mut(),
                get_request@.value()->Get_0.servers(),
                min_timestamp@,
                agree_with_max@,
                &*max_resp,
                id.1,
                lb,
            );

            assert forall|cid|
                {
                    &&& !#[trigger] get_replies@.insert(id).contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } implies servers@[cid.1]@@.timestamp()
                == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp() by {
                if cid.1 == id.1 {
                    assert(get_replies@.insert(id).contains(cid));
                } else {
                    assert(servers@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp());
                }
            }
        }

        Self::update_max_resp_and_quorum(max_resp, agree_with_max, get_replies, r, id);
    }

    fn insert_get(&mut self, id: (u64, u64), resp: Response)
        requires
            ReadPred::inv(old(self).constant(), *old(self)),
            old(self).client_id() == id.0,
            resp.req_type() is Get,
            resp.get().server_id() == id.1,
            resp.request() == old(self).get_request@.value(),
            old(self).constant().server_tokens_id == resp.get().server_token_id(),
            old(self).constant().server_locs.contains_key(resp.server_id()),
            old(self).constant().server_locs[resp.server_id()] == resp.get().loc(),
            resp.get().spec_commitment().id() == old(self).commitment_id(),
        ensures
            ReadPred::inv(self.constant(), *self),
            self.constant() == old(self).constant(),
            self.spec_get_replies() == old(self).spec_get_replies().insert(id),
            self.spec_wb_replies() == old(self).spec_wb_replies(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
        }

        Self::insert_get_aux(
            &mut self.max_resp,
            &mut self.agree_with_max,
            &mut self.get_replies,
            &mut self.servers,
            &mut self.server_tokens,
            &self.min_timestamp,
            &self.commitment_id,
            &self.channels,
            &self.get_request,
            id,
            resp,
        );
    }

    pub closed spec fn spec_get_replies(self) -> Set<C::Id> {
        self.get_replies@
    }

    pub fn get_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.spec_get_replies(),
    {
        proof {
            use_type_invariant(self);
        }
        self.get_replies.clone()
    }

    fn insert_write(&mut self, id: (u64, u64), resp: WriteResponse)
        requires
            ReadPred::inv(old(self).constant(), *old(self)),
        ensures
            ReadPred::inv(self.constant(), *self),
            self.constant() == old(self).constant(),
            self.wb_replies@ == old(self).wb_replies@.insert(id, resp),
            self.spec_get_replies() == old(self).spec_get_replies(),
            self.spec_wb_replies() == old(self).spec_wb_replies().insert(id),
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

    pub closed spec fn spec_wb_replies(self) -> Set<C::Id> {
        self.wb_replies@.dom()
    }

    pub fn wb_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.spec_wb_replies(),
    {
        proof {
            use_type_invariant(self);
        }
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        clone_domain(&self.wb_replies)
    }
}

pub struct ReadAccumGetPhase<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    inner: ReadAccumulator<C>,
}

pub struct ReadAccumWbPhase<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    request_tag: u64,
    inner: ReadAccumulator<C>,
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> InvariantPredicate<
    ReadPred<C>,
    ReadAccumGetPhase<C>,
> for ReadPred<C> {
    open spec fn inv(pred: ReadPred<C>, v: ReadAccumGetPhase<C>) -> bool {
        pred == v.constant()
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> InvariantPredicate<
    ReadPred<C>,
    ReadAccumWbPhase<C>,
> for ReadPred<C> {
    open spec fn inv(pred: ReadPred<C>, v: ReadAccumWbPhase<C>) -> bool {
        pred == v.constant()
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> ReadAccumGetPhase<C> {
    pub fn new(
        servers: Tracked<ServerUniverse>,
        server_tokens: Tracked<GhostPersistentSubmap<u64, Loc>>,
        get_request: Tracked<RequestProof>,
        read_pred: Ghost<ReadPred<C>>,
    ) -> (r: Self)
        requires
            read_pred@.server_locs == servers@.locs(),
            read_pred@.server_tokens_id == server_tokens@.id(),
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            get_request@.id() == read_pred@.request_map_id,
            get_request@.key().1 == read_pred@.get_request_id,
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().inv(),
            get_request@.value()->Get_0.servers().eq_timestamp(servers@),
            forall|q: Quorum| #[trigger]
                servers@.valid_quorum(q) ==> {
                    read_pred@.min_timestamp <= servers@.quorum_timestamp(q)
                },
            forall|c_id| #[trigger]
                read_pred@.channels.contains_key(c_id) ==> {
                    let c = read_pred@.channels[c_id];
                    &&& c_id.0 == get_request@.key().0
                    &&& c.constant().request_map_id == read_pred@.request_map_id
                    &&& c.constant().commitment_id == read_pred@.commitment_id
                    &&& c.constant().server_tokens_id == read_pred@.server_tokens_id
                    &&& c.constant().server_locs == read_pred@.server_locs
                },
        ensures
            r.spec_request_tag() == get_request@.key().1,
            r.constant() == read_pred@,
            r.replies().is_empty(),
    {
        ReadAccumGetPhase {
            inner: ReadAccumulator::new(servers, server_tokens, get_request, read_pred),
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.inner.spec_wb_replies().is_empty()
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.inner.get_request_id()
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.inner.spec_get_replies()
    }

    pub closed spec fn constant(self) -> ReadPred<C> {
        self.inner.constant()
    }

    pub fn destruct(self) -> (r: ReadAccumulator<C>)
        ensures
            r.constant() == self.constant(),
            r.spec_wb_replies().is_empty(),
            r.spec_get_replies() == self.replies(),
    {
        proof { use_type_invariant(&self) }

        self.inner
    }
}

impl<C> ReplyAccumulator<C, ReadPred<C>> for ReadAccumGetPhase<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    fn insert(
        &mut self,
        #[allow(unused_variables)]
        pred: Ghost<ReadPred<C>>,
        id: (u64, u64),
        reply: Response,
    )
        ensures
            self.constant() == old(self).constant(),
    {
        proof {
            use_type_invariant(&*self);
            use_type_invariant(&self.inner);

            // assert(ReadPred::inv(pred@, *self));
            // assert(self.constant() == pred@);
            assert(self.channels().contains_key(id));
            let chan = self.channels()[id];
            // assert(chan.constant().commitment_id == self.inner.commitment_id@);
            // assert(chan.constant().request_map_id == self.inner.request_map_id());
            // assert(chan.spec_id() == id);

            assume(C::K::recv_inv(chan.constant(), id, reply));  // TODO(verus): this is a verus problem

            // assert(self.inner.request_map_id() == reply.request_id());
        }

        reply.agree_request(&mut self.inner.get_request);
        reply.lemma_inv();

        /*
        proof {
            assert(reply.spec_tag() == pred@.get_request_id);
            assert(reply.spec_tag() == reply.request_key().1);
            assert(id.0 == reply.request_key().0);
            assert(reply.request_key().1 == self.inner.get_request@.key().1);
            assert(reply.request_key() == self.inner.get_request@.key());
            assert(reply.request() == self.inner.get_request@.value());
            assert(reply.req_type() == self.inner.get_request@.value().req_type());
            assert(reply.req_type() is Get);
        }
        */

        self.inner.insert_get(id, reply);
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        self.inner.get_replies()
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.constant().channels
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> ReadAccumWbPhase<C> {
    pub fn new(accum: ReadAccumulator<C>, request_tag: u64) -> (r: Self)
        requires
            accum.spec_wb_replies().is_empty(),
        ensures
            r.spec_request_tag() == request_tag,
            r.replies().is_empty(),
            r.constant() == accum.constant(),
    {
        ReadAccumWbPhase { inner: accum, request_tag }
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.request_tag
    }

    pub closed spec fn constant(self) -> ReadPred<C> {
        self.inner.constant()
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.inner.spec_wb_replies()
    }

    pub fn destruct(self) -> (r: ReadAccumulator<C>)
        ensures
            r.constant() == self.constant(),
    {
        self.inner
    }
}

impl<C> ReplyAccumulator<C, ReadPred<C>> for ReadAccumWbPhase<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(
        &mut self,
        #[allow(unused_variables)]
        pred: Ghost<ReadPred<C>>,
        id: (u64, u64),
        resp: Response,
    )
        ensures
            self.constant() == old(self).constant(),
    {
        assert(self.constant() == pred@);
        assert(self.channels().contains_key(id));
        let ghost chan = self.channels()[id];
        assert(chan.spec_id() == id);
        assume(C::K::recv_inv(chan.constant(), id, resp));
        assume(resp.req_type() is Write);
        let resp = resp.destruct_write();
        self.inner.insert_write(id, resp);
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        self.inner.wb_replies()
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.constant().channels
    }
}

#[allow(dead_code)]
pub struct GetTimestampAccumulator<C: Channel<K = ChannelInv>> {
    replies: BTreeMap<(u64, u64), GetTimestampResponse>,
    channels: Ghost<Map<C::Id, C>>,
    request_tag: u64,
}

#[allow(dead_code)]
pub struct WriteAccumulator<C: Channel<K = ChannelInv>> {
    replies: BTreeMap<(u64, u64), ()>,
    channels: Ghost<Map<C::Id, C>>,
    request_tag: u64,
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> GetTimestampAccumulator<C> {
    pub fn new(channels: Ghost<Map<C::Id, C>>, request_tag: u64) -> (r: Self)
        ensures
            r.spec_request_tag() == request_tag,
            r.replies().is_empty(),
            r.spec_channels() == channels@,
    {
        GetTimestampAccumulator { replies: BTreeMap::new(), channels, request_tag }
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.request_tag
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), GetTimestampResponse>)
        ensures
            r@.dom() == self.replies(),
    {
        self.replies
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@.dom()
    }

    pub closed spec fn spec_channels(self) -> Map<C::Id, C> {
        self.channels@
    }
}

impl<C> ReplyAccumulator<C, EmptyPred> for GetTimestampAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response)
        ensures
            self.channels() == old(self).channels(),
    {
        assume(resp.req_type() is GetTimestamp);
        let resp = resp.destruct_get_timestamp();
        // TODO(qed): remove later on
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, resp);
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        clone_domain(&self.replies)
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> WriteAccumulator<C> {
    pub fn new(channels: Ghost<Map<C::Id, C>>, request_tag: u64) -> (r: Self)
        ensures
            r.spec_request_tag() == request_tag,
            r.replies().is_empty(),
            r.spec_channels() == channels@,
    {
        WriteAccumulator { replies: BTreeMap::new(), channels, request_tag }
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.request_tag
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), ()>)
        ensures
            r@.dom() == self.replies(),
    {
        self.replies
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@.dom()
    }

    pub closed spec fn spec_channels(self) -> Map<C::Id, C> {
        self.channels@
    }
}

impl<C> ReplyAccumulator<C, EmptyPred> for WriteAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response)
        ensures
            self.channels() == old(self).channels(),
    {
        assume(resp.req_type() is Write);
        let resp = resp.destruct_write();
        // TODO(qed): remove later on
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, ());
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        clone_domain(&self.replies)
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

pub struct EmptyPred;

impl<C: Channel<K = ChannelInv>> InvariantPredicate<
    EmptyPred,
    GetTimestampAccumulator<C>,
> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: GetTimestampAccumulator<C>) -> bool {
        true
    }
}

impl<C: Channel<K = ChannelInv>> InvariantPredicate<EmptyPred, WriteAccumulator<C>> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: WriteAccumulator<C>) -> bool {
        true
    }
}

pub fn clone_domain<K: Ord + Clone, V>(map: &BTreeMap<K, V>) -> (dom: BTreeSet<K>)
    requires
        vstd::laws_cmp::obeys_cmp_spec::<K>(),
    ensures
        map@.dom() == dom@,
{
    proof {
        admit();  // TODO: prove domain clone
    }
    let map_keys = map.keys();
    assert(map_keys@.0 == 0);
    assert(map_keys@.1.to_set() =~= map@.dom());
    let ghost g_keys = map_keys@.1;

    let mut dom = BTreeSet::new();
    assert(dom@ =~= g_keys.take(0).to_set());

    for k in iter: map_keys
        invariant
            iter.keys == g_keys,
            g_keys == map@.dom().to_seq(),
            increasing_seq(g_keys),
            dom@ == iter@.to_set(),
    {
        assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
        dom.insert(k.clone());
        proof {
            admit();  // TODO: prove domain clone
        }
    }
    dom
}

} // verus!
