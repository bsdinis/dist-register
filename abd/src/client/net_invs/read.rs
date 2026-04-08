use std::collections::BTreeSet;

use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::requests::RequestProof;
#[cfg(verus_only)]
use crate::invariants::StatePredicate;
use crate::proto::GetResponse;
use crate::proto::Response;
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

verus! {

#[allow(unused_variables, dead_code)]
pub ghost struct ReadPred<C: Channel<K = ChannelInv>> {
    pub server_locs: Map<u64, Loc>,
    pub orig_servers: ServerUniverse,
    pub commitment_id: Loc,
    pub request_map_id: Loc,
    pub server_tokens_id: Loc,
    pub min_timestamp: Timestamp,
    pub channels: Map<C::Id, C>,
    pub client_id: u64,
    pub get_request_id: u64,
    pub wb_request_id: Option<u64>,
}

impl<C: Channel<K = ChannelInv>> ReadPred<C> {
    pub open spec fn new(
        state: StatePredicate,
        channels: Map<C::Id, C>,
        old_watermark: MonotonicTimestampResource,
        client_id: u64,
        get_request: RequestProof,
    ) -> ReadPred<C> {
        ReadPred {
            server_locs: state.server_locs,
            orig_servers: get_request.value()->Get_0.servers(),
            commitment_id: state.commitments_ids.commitment_id,
            request_map_id: state.request_map_ids.request_auth_id,
            server_tokens_id: state.server_tokens_id,
            min_timestamp: old_watermark@.timestamp(),
            channels,
            client_id,
            get_request_id: get_request.key().1,
            wb_request_id: None,
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
    /// Received write-back replies
    wb_replies: BTreeSet<C::Id>,
    // Spec state
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
    /// write-back request proof
    wb_request: Tracked<Option<RequestProof>>,
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
            read_pred@.wb_request_id is None,
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            get_request@.id() == read_pred@.request_map_id,
            get_request@.key().0 == read_pred@.client_id,
            get_request@.key().1 == read_pred@.get_request_id,
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().inv(),
            get_request@.value()->Get_0.servers().is_lb(),
            get_request@.value()->Get_0.servers().eq_timestamp(servers@),
            get_request@.value()->Get_0.servers() == read_pred@.orig_servers,
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
            wb_replies: BTreeSet::new(),
            servers,
            server_tokens,
            min_timestamp: Ghost(read_pred@.min_timestamp),
            commitment_id: Ghost(read_pred@.commitment_id),
            channels: Ghost(read_pred@.channels),
            get_request,
            wb_request: Tracked(None),
        }
    }

    closed spec fn server_invs(
        servers: ServerUniverse,
        req_servers: ServerUniverse,
        server_tokens: Map<u64, Loc>,
        min_timestamp: Timestamp,
    ) -> bool {
        &&& servers.inv()
        &&& servers.is_lb()
        &&& req_servers.inv()
        &&& req_servers.is_lb()
        &&& req_servers.leq(servers)
        &&& forall|q: Quorum| #[trigger]
            servers.valid_quorum(q) ==> servers.quorum_timestamp(q) >= min_timestamp
        &&& server_tokens <= servers.locs()
    }

    closed spec fn channel_inv(channels: Map<C::Id, C>, k: ReadPred<C>) -> bool {
        forall|c_id| #[trigger]
            channels.contains_key(c_id) ==> {
                let c = channels[c_id];
                &&& c_id.0 == k.client_id
                &&& c.constant().request_map_id == k.request_map_id
                &&& c.constant().commitment_id == k.commitment_id
                &&& c.constant().server_tokens_id == k.server_tokens_id
                &&& c.constant().server_locs == k.server_locs
            }
    }

    closed spec fn replies_inv(replies: Set<C::Id>, client_id: u64) -> bool {
        &&& replies.finite()
        &&& forall|cid| #[trigger] replies.contains(cid) ==> cid.0 == client_id
    }

    closed spec fn request_inv(
        get_request: RequestProof,
        wb_request: Option<RequestProof>,
        max_resp: Option<GetResponse>,
    ) -> bool {
        &&& get_request.value().req_type() is Get
        &&& wb_request is Some ==> {
            let req = wb_request->Some_0;
            &&& max_resp is Some
            &&& req.id() == get_request.id()
            &&& req.key().0 == get_request.key().0
            &&& req.value().req_type() is Write
            &&& req.value()->Write_0.spec_timestamp() == max_resp->Some_0.spec_timestamp()
            &&& req.value()->Write_0.servers().inv()
            &&& req.value()->Write_0.servers().eq_timestamp(get_request.value()->Get_0.servers())
        }
    }

    // TODO: take in the union
    closed spec fn unchanged_inv(
        servers: ServerUniverse,
        req_servers: ServerUniverse,
        get_replies: Set<C::Id>,
        wb_replies: Set<C::Id>,
        client_id: u64,
    ) -> bool {
        &&& forall|cid|
            {
                &&& !#[trigger] get_replies.contains(cid)
                &&& !#[trigger] wb_replies.contains(cid)
                &&& #[trigger] servers.contains_key(cid.1)
                &&& cid.0 == client_id
            } ==> { servers[cid.1]@@.timestamp() == req_servers[cid.1]@@.timestamp() }
    }

    closed spec fn agree_with_max_aux_inv(
        agree_with_max: Set<u64>,
        get_replies: Set<C::Id>,
        wb_replies: Set<C::Id>,
        max_resp: Option<GetResponse>,
    ) -> bool {
        &&& agree_with_max.finite()
        &&& agree_with_max.is_empty() <==> get_replies.is_empty()
        &&& max_resp is None <==> agree_with_max.is_empty()
        &&& agree_with_max <= get_replies.union(wb_replies).map(|id: (u64, u64)| id.1)
    }

    closed spec fn agree_with_max_inv(
        agree_with_max: Set<u64>,
        get_replies: Set<C::Id>,
        wb_replies: Set<C::Id>,
        servers: ServerUniverse,
        max_resp: Option<GetResponse>,
    ) -> bool {
        &&& Self::agree_with_max_aux_inv(agree_with_max, get_replies, wb_replies, max_resp)
        &&& agree_with_max <= servers.dom()
    }

    closed spec fn max_resp_inv(
        max_resp: GetResponse,
        servers: ServerUniverse,
        agree_with_max: Set<u64>,
        commitment_id: Loc,
        server_tokens_id: Loc,
    ) -> bool {
        &&& forall|id| #[trigger]
            agree_with_max.contains(id) ==> { servers[id]@@.timestamp() >= max_resp.spec_timestamp()
            }
        &&& max_resp.spec_commitment().id() == commitment_id
        &&& max_resp.server_token_id() == server_tokens_id
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& Self::server_invs(
            self.servers(),
            self.orig_servers(),
            self.server_tokens@@,
            self.spec_min_timestamp(),
        )
        &&& Self::channel_inv(self.channels@, self.constant())
        &&& Self::replies_inv(self.get_replies@, self.client_id())
        &&& Self::replies_inv(self.wb_replies@, self.client_id())
        &&& Self::request_inv(self.get_request@, self.wb_request@, self.max_resp)
        &&& Self::unchanged_inv(
            self.servers(),
            self.orig_servers(),
            self.get_replies@,
            self.wb_replies@,
            self.client_id(),
        )
        &&& Self::agree_with_max_inv(
            self.agree_with_max@,
            self.get_replies@,
            self.wb_replies@,
            self.servers(),
            self.max_resp@,
        )
        &&& self.max_resp is Some ==> {
            Self::max_resp_inv(
                self.max_resp->Some_0,
                self.servers(),
                self.agree_with_max@,
                self.commitment_id@,
                self.server_tokens@.id(),
            )
        }
        &&& self.wb_request@ is None ==> self.spec_wb_replies().is_empty()
        &&& forall|cid| #[trigger]
            self.wb_replies@.contains(cid) ==> {
                &&& self.servers@[cid.1]@@.timestamp() >= self.spec_max_timestamp()
                &&& self.agree_with_max@.contains(cid.1)
            }
    }

    // SPEC
    pub open spec fn constant(self) -> ReadPred<C> {
        ReadPred {
            server_locs: self.server_locs(),
            orig_servers: self.orig_servers(),
            commitment_id: self.commitment_id(),
            request_map_id: self.request_map_id(),
            server_tokens_id: self.server_tokens_id(),
            min_timestamp: self.spec_min_timestamp(),
            channels: self.channels(),
            client_id: self.client_id(),
            get_request_id: self.get_request_id(),
            wb_request_id: self.wb_request_id(),
        }
    }

    pub closed spec fn client_id(self) -> u64 {
        self.get_request@.key().0
    }

    pub closed spec fn get_request_id(self) -> u64 {
        self.get_request@.key().1
    }

    pub closed spec fn orig_servers(self) -> ServerUniverse {
        self.get_request@.value()->Get_0.servers()
    }

    pub closed spec fn wb_request_id(self) -> Option<u64> {
        match self.wb_request@ {
            Some(r) => Some(r.key().1),
            None => None,
        }
    }

    pub closed spec fn servers(self) -> ServerUniverse {
        self.servers@
    }

    pub open spec fn server_locs(self) -> Map<u64, Loc> {
        self.servers().locs()
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

    pub open spec fn quorum(self) -> Quorum {
        Quorum::from_set(self.spec_agree_with_max())
    }

    pub closed spec fn spec_agree_with_max(self) -> Set<u64> {
        self.agree_with_max@
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

    pub closed spec fn spec_get_replies(self) -> Set<C::Id> {
        self.get_replies@
    }

    pub closed spec fn spec_wb_replies(self) -> Set<C::Id> {
        self.wb_replies@
    }

    // PROOF
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
                &&& q_ts >= self.spec_max_timestamp()
                &&& q_ts >= self.spec_max_timestamp()
                &&& self.spec_max_timestamp() >= self.spec_min_timestamp()
            },
    {
        proof {
            use_type_invariant(self);
            if self.servers().valid_quorum(self.quorum()) {
                let quorum_map = self.servers().map.restrict(self.quorum()@);
                assert(quorum_map.dom() == self.quorum()@);  // XXX: load bearing
                let quorum_vals = self.servers().quorum_vals(self.quorum());
                lemma_values_finite(quorum_map);
                quorum_map.values().lemma_map_finite(
                    |r: Tracked<MonotonicTimestampResource>| r@@.timestamp(),
                );
                assume(quorum_vals.len() > 0);  // TODO(verus): this needs a verus lemma
                quorum_vals.find_unique_maximal_ensures(ServerUniverse::ts_leq());
            }
            // TODO: max >= min
            // this one is weird. things we know
            //  - this should be obvious, but is not
            //  - initially, we know that all quorums >= min
            //  - max is the max from a particular quorum, meaning it is >= min
            //  - the problem is that our structure never takes notice of when we reach the first quorum
            //  - and this is definitely not a always true fact:
            //      - when we begin the max_resp can be of some replica that never saw a write, but
            //      that does not mean it is >= min
            //  - the solution seems to be to take notice of the quorum moment
            //
            //  proof idea:
            //  s is the server universe, fq the first round quorum
            //      - ∀q ⋲ s, s.ts(q) >= min [inv]
            //      - ∀x ⋲ fq, s[x] <= MAX [need to establish, might not be true once second round begins]
            //      - fq ⋲ s ==> s.ts(fq) >= min ==> ∃ y ⋲ fq. s[y] >= min
            //          - let y be that one, min <= s[y] <= MAX

            assume(self.spec_max_timestamp() >= self.spec_min_timestamp()); // TODO(qed)
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
            Self::server_invs(*old(servers), req_servers, old(servers).locs(), min_timestamp),
            old(servers).contains_key(server_id),
            old(servers)[server_id]@.loc() == lb.loc(),
            old(servers)[server_id]@@.timestamp() <= lb@.timestamp(),
            agree_with_max <= old(servers).dom(),
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    old(servers)[id]@@.timestamp() >= max_resp->Some_0.spec_timestamp()
                },
            lb@ is LowerBound,
            !agree_with_max.contains(server_id),
        ensures
            Self::server_invs(*servers, req_servers, servers.locs(), min_timestamp),
            servers.dom() == old(servers).dom(),
            servers.locs() == old(servers).locs(),
            old(servers).leq(*servers),
            forall|id| #[trigger]
                servers.contains_key(id) ==> {
                    &&& id != server_id ==> servers[id]@@.timestamp() == old(
                        servers,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> servers[id]@@.timestamp() == lb@.timestamp()
                },
            servers[server_id]@@.timestamp() == lb@.timestamp(),
            max_resp is Some ==> forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    servers[id]@@.timestamp() >= max_resp->Some_0.spec_timestamp()
                },
    {
        let ghost old_servers = *old(servers);
        servers.tracked_update_lb(server_id, lb);
        old_servers.lemma_leq_quorums(*servers, min_timestamp);
        if max_resp is Some {
            assert forall|id| #[trigger]
                agree_with_max.contains(id) implies servers[id]@@.timestamp()
                >= max_resp->Some_0.spec_timestamp() by {
                assert(servers.contains_key(id));  // XXX: trigger
            }
        }
        ServerUniverse::lemma_leq_trans(req_servers, old_servers, *servers);
    }

    proof fn update_servers_on_wb(
        tracked servers: &mut ServerUniverse,
        req_servers: ServerUniverse,
        min_timestamp: Timestamp,
        agree_with_max: Set<u64>,
        max_resp: GetResponse,
        server_id: u64,
        tracked lb: MonotonicTimestampResource,
    )
        requires
            Self::server_invs(*old(servers), req_servers, old(servers).locs(), min_timestamp),
            old(servers).contains_key(server_id),
            old(servers)[server_id]@.loc() == lb.loc(),
            agree_with_max <= old(servers).dom(),
            forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    old(servers)[id]@@.timestamp() >= max_resp.spec_timestamp()
                },
            lb@ is LowerBound,
            !agree_with_max.contains(server_id),
        ensures
            Self::server_invs(*servers, req_servers, servers.locs(), min_timestamp),
            servers.dom() == old(servers).dom(),
            servers.locs() == old(servers).locs(),
            old(servers).leq(*servers),
            forall|id| #[trigger]
                servers.contains_key(id) ==> {
                    &&& id != server_id ==> servers[id]@@.timestamp() == old(
                        servers,
                    )[id]@@.timestamp()
                    &&& id == server_id ==> servers[id]@@.timestamp() >= lb@.timestamp()
                },
            servers[server_id]@@.timestamp() >= lb@.timestamp(),
            forall|id| #[trigger]
                agree_with_max.contains(id) ==> {
                    servers[id]@@.timestamp() >= max_resp.spec_timestamp()
                },
    {
        let ghost old_servers = *old(servers);
        if servers[server_id]@@.timestamp() < lb@.timestamp() {
            servers.tracked_update_lb(server_id, lb);
        }
        old_servers.lemma_leq_quorums(*servers, min_timestamp);
        assert forall|id| #[trigger] agree_with_max.contains(id) implies servers[id]@@.timestamp()
            >= max_resp.spec_timestamp() by {
            assert(servers.contains_key(id));  // XXX: trigger
        }
        ServerUniverse::lemma_leq_trans(req_servers, old_servers, *servers);
    }

    // EXEC
    pub fn get_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.spec_get_replies(),
    {
        proof {
            use_type_invariant(self);
        }
        self.get_replies.clone()
    }

    pub fn wb_replies(&self) -> (r: BTreeSet<C::Id>)
        ensures
            r@ == self.spec_wb_replies(),
    {
        proof {
            use_type_invariant(self);
        }
        self.wb_replies.clone()
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
                >= max_ts by {
                assert(self.servers@.contains_key(id));
                assert(lbs.contains_key(id));
            }

            lbs.lemma_eq(self.servers());
        }
        Tracked(lbs)
    }

    pub fn max_resp(&self) -> (r: &GetResponse)
        requires
            !self.spec_get_replies().is_empty(),
        ensures
            r == self.spec_max_resp(),
            r.spec_timestamp() == self.spec_max_timestamp(),
            r.spec_commitment().id() == self.commitment_id(),
    {
        proof {
            use_type_invariant(self);
        }
        self.max_resp.as_ref().unwrap()
    }

    pub fn agree_with_max(&self) -> (r: &BTreeSet<u64>)
        ensures
            r@ == self.spec_agree_with_max(),
    {
        &self.agree_with_max
    }

    fn update_quorum(
        agree_with_max: &mut BTreeSet<u64>,
        wb_replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        max_resp: &Option<GetResponse>,
        #[allow(unused_variables)]
        get_replies: &BTreeSet<C::Id>,
        id: (u64, u64),
    )
        requires
            !old(wb_replies)@.contains(id),
            !old(agree_with_max)@.contains(id.1),
            !old(agree_with_max)@.is_empty(),
            Self::replies_inv(get_replies@, id.0),
            Self::replies_inv(old(wb_replies)@, id.0),
            Self::agree_with_max_aux_inv(
                old(agree_with_max)@,
                get_replies@,
                old(wb_replies)@,
                *max_resp,
            ),
        ensures
            wb_replies@ == old(wb_replies)@.insert(id),
            agree_with_max@ == old(agree_with_max)@.insert(id.1),
            Self::replies_inv(wb_replies@, id.0),
            Self::agree_with_max_aux_inv(agree_with_max@, get_replies@, wb_replies@, *max_resp),
        no_unwind
    {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());

        agree_with_max.insert(id.1);
        wb_replies.insert(id);

        assert(forall|server_id| #[trigger]
            agree_with_max@.contains(server_id) ==> get_replies@.union(wb_replies@).contains(
                (id.0, server_id),
            ));
    }

    fn update_max_resp_and_quorum(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        get_replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        wb_replies: &BTreeSet<C::Id>,
        resp: GetResponse,
        id: (u64, u64),
    )
        requires
            !old(get_replies)@.contains(id),
            !old(agree_with_max)@.contains(id.1),
            Self::replies_inv(old(get_replies)@, id.0),
            Self::agree_with_max_aux_inv(
                old(agree_with_max)@,
                old(get_replies)@,
                wb_replies@,
                *old(max_resp),
            ),
            wb_replies@.is_empty(),
        ensures
            *max_resp is Some,
            !agree_with_max@.is_empty(),
            get_replies@ == old(get_replies)@.insert(id),
            Self::replies_inv(get_replies@, id.0),
            Self::agree_with_max_aux_inv(agree_with_max@, get_replies@, wb_replies@, *max_resp),
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
                &&& new_max_ts >= old_max_ts
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
        assert(get_replies@.union(wb_replies@) == get_replies@);
    }

    fn insert_get_aux(
        max_resp: &mut Option<GetResponse>,
        agree_with_max: &mut BTreeSet<u64>,
        get_replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        servers: &mut Tracked<ServerUniverse>,
        server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>,
        #[allow(unused_variables)]
        wb_replies: &BTreeSet<C::Id>,
        #[allow(unused_variables)]
        min_timestamp: &Ghost<Timestamp>,
        #[allow(unused_variables)]
        commitment_id: &Ghost<Loc>,
        #[allow(unused_variables)]
        get_request: &Tracked<RequestProof>,
        id: (u64, u64),
        resp: Response,
    )
        requires
            resp.server_id() == id.1,
            resp.req_type() is Get,
            resp.request() == get_request@.value(),
            resp.get().spec_commitment().id() == commitment_id@,
            resp.get().server_token_id() == old(server_tokens)@.id(),
            resp.get().loc() == old(servers)@.locs()[resp.server_id()],
            old(servers)@.locs().contains_key(id.1),
            wb_replies@.is_empty(),
            get_request@.value().req_type() is Get,
            get_request@.key().0 == id.0,
            Self::server_invs(
                old(servers)@,
                get_request@.value()->Get_0.servers(),
                old(server_tokens)@@,
                min_timestamp@,
            ),
            Self::replies_inv(old(get_replies)@, id.0),
            Self::agree_with_max_inv(
                old(agree_with_max)@,
                old(get_replies)@,
                wb_replies@,
                old(servers)@,
                *old(max_resp),
            ),
            forall|cid|
                {
                    &&& !#[trigger] old(get_replies)@.contains(cid)
                    &&& !#[trigger] wb_replies@.contains(cid)
                    &&& old(servers)@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    old(servers)@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
            *old(max_resp) is Some ==> {
                Self::max_resp_inv(
                    old(max_resp)->Some_0,
                    old(servers)@,
                    old(agree_with_max)@,
                    commitment_id@,
                    old(server_tokens)@.id(),
                )
            },
        ensures
            servers@.locs() == old(servers)@.locs(),
            server_tokens@.id() == old(server_tokens)@.id(),
            get_replies@ == old(get_replies)@.insert(id),
            resp.get().spec_commitment().id() == commitment_id@,
            Self::server_invs(
                servers@,
                get_request@.value()->Get_0.servers(),
                server_tokens@@,
                min_timestamp@,
            ),
            Self::replies_inv(get_replies@, id.0),
            Self::agree_with_max_inv(
                agree_with_max@,
                get_replies@,
                wb_replies@,
                servers@,
                *max_resp,
            ),
            *max_resp is Some ==> {
                Self::max_resp_inv(
                    max_resp->Some_0,
                    servers@,
                    agree_with_max@,
                    commitment_id@,
                    server_tokens@.id(),
                )
            },
            forall|cid|
                {
                    &&& !#[trigger] get_replies@.contains(cid)
                    &&& !#[trigger] wb_replies@.contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    servers@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
        no_unwind
    {
        proof {
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
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
            assert(!wb_replies@.contains(id));
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
                    &&& !#[trigger] wb_replies@.insert(id).contains(cid)
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

        Self::update_max_resp_and_quorum(max_resp, agree_with_max, get_replies, wb_replies, r, id);
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
            old(self).wb_request_id() is None,
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
            &self.wb_replies,
            &self.min_timestamp,
            &self.commitment_id,
            &self.get_request,
            id,
            resp,
        );
    }

    fn set_wb_request(
        &mut self,
        #[allow(unused_variables)]
        wb_request: Tracked<RequestProof>,
    )
        requires
            old(self).wb_request_id() is None,
            old(self).max_resp is Some,
            wb_request@.key().0 == old(self).client_id(),
            wb_request@.id() == old(self).constant().request_map_id,
            wb_request@.value().req_type() is Write,
            wb_request@.value()->Write_0.spec_timestamp() == old(self).spec_max_timestamp(),
            wb_request@.value()->Write_0.servers().inv(),
            wb_request@.value()->Write_0.servers().eq_timestamp(
                old(self).get_request@.value()->Get_0.servers(),
            ),
        ensures
            self.constant() == (ReadPred {
                wb_request_id: Some(wb_request@.key().1),
                ..old(self).constant()
            }),
            self.wb_request_id() == Some(wb_request@.key().1),
            self.spec_wb_replies() == old(self).spec_wb_replies(),
            self.spec_get_replies() == old(self).spec_get_replies(),
            self.spec_max_resp() == old(self).spec_max_resp(),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.wb_request = Tracked(Some(wb_request.get()));
    }

    fn insert_wb_aux(
        agree_with_max: &mut BTreeSet<u64>,
        wb_replies: &mut BTreeSet<C::Id>,
        #[allow(unused_variables)]
        servers: &mut Tracked<ServerUniverse>,
        server_tokens: &mut Tracked<GhostPersistentSubmap<u64, Loc>>,
        max_resp: &Option<GetResponse>,
        #[allow(unused_variables)]
        get_replies: &BTreeSet<C::Id>,
        #[allow(unused_variables)]
        min_timestamp: &Ghost<Timestamp>,
        #[allow(unused_variables)]
        commitment_id: &Ghost<Loc>,
        #[allow(unused_variables)]
        wb_request: &Tracked<Option<RequestProof>>,
        #[allow(unused_variables)]
        get_request: &Tracked<RequestProof>,
        id: (u64, u64),
        resp: Response,
    )
        requires
            wb_request@ is Some,
            max_resp is Some,
            get_request@.key().0 == id.0,
            resp.server_id() == id.1,
            resp.req_type() is Write,
            resp.request() == wb_request@->Some_0.value(),
            resp.write().server_token_id() == old(server_tokens)@.id(),
            resp.write().loc() == old(servers)@.locs()[resp.server_id()],
            old(servers)@.locs().contains_key(id.1),
            !get_replies@.is_empty(),
            Self::server_invs(
                old(servers)@,
                get_request@.value()->Get_0.servers(),
                old(server_tokens)@@,
                min_timestamp@,
            ),
            Self::replies_inv(get_replies@, id.0),
            Self::replies_inv(old(wb_replies)@, id.0),
            Self::request_inv(get_request@, wb_request@, *max_resp),
            Self::agree_with_max_inv(
                old(agree_with_max)@,
                get_replies@,
                old(wb_replies)@,
                old(servers)@,
                *max_resp,
            ),
            Self::max_resp_inv(
                max_resp->Some_0,
                old(servers)@,
                old(agree_with_max)@,
                commitment_id@,
                old(server_tokens)@.id(),
            ),
            forall|cid| #[trigger]
                old(wb_replies)@.contains(cid) ==> {
                    &&& old(servers)[cid.1]@@.timestamp() >= max_resp->Some_0.spec_timestamp()
                    &&& old(agree_with_max)@.contains(cid.1)
                },
            forall|cid|
                {
                    &&& !#[trigger] get_replies@.contains(cid)
                    &&& !#[trigger] old(wb_replies)@.contains(cid)
                    &&& old(servers)@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    old(servers)@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
        ensures
            servers@.locs() == old(servers)@.locs(),
            server_tokens@.id() == old(server_tokens)@.id(),
            wb_replies@ == old(wb_replies)@.insert(id),
            wb_replies@.finite(),
            Self::server_invs(
                servers@,
                get_request@.value()->Get_0.servers(),
                server_tokens@@,
                min_timestamp@,
            ),
            Self::replies_inv(get_replies@, id.0),
            Self::replies_inv(wb_replies@, id.0),
            Self::request_inv(get_request@, wb_request@, *max_resp),
            Self::agree_with_max_inv(
                agree_with_max@,
                get_replies@,
                wb_replies@,
                servers@,
                *max_resp,
            ),
            Self::max_resp_inv(
                max_resp->Some_0,
                servers@,
                agree_with_max@,
                commitment_id@,
                server_tokens@.id(),
            ),
            forall|cid| #[trigger]
                wb_replies@.contains(cid) ==> {
                    &&& servers[cid.1]@@.timestamp() >= max_resp->Some_0.spec_timestamp()
                    &&& agree_with_max@.contains(cid.1)
                },
            forall|cid|
                {
                    &&& !#[trigger] get_replies@.contains(cid)
                    &&& !#[trigger] wb_replies@.contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } ==> {
                    servers@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp()
                },
        no_unwind
    {
        proof {
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        }

        if wb_replies.contains(&id) {
            return ;
        }
        if agree_with_max.contains(&id.1) {
            wb_replies.insert(id);
            assert forall|oid: (u64, u64)| #[trigger]
                agree_with_max@.contains(oid.1) && oid.0 == id.0 implies get_replies@.union(
                wb_replies@,
            ).contains(oid) by {
                if oid == id {
                    assert(wb_replies@.contains(oid));  // TRIGGER
                }
            }
            return ;
        }
        let r = resp.destruct_write();

        r.lemma_write_response();
        r.lemma_token_agree(server_tokens);
        assert(r.lb()@ is LowerBound);
        let Tracked(lb) = r.duplicate_lb();
        assert(lb@ is LowerBound);

        proof {
            assert(!wb_replies@.contains(id));
            Self::update_servers_on_wb(
                servers.borrow_mut(),
                get_request@.value()->Get_0.servers(),
                min_timestamp@,
                agree_with_max@,
                max_resp->Some_0,
                id.1,
                lb,
            );

            assert forall|cid|
                {
                    &&& !#[trigger] get_replies@.insert(id).contains(cid)
                    &&& !#[trigger] wb_replies@.insert(id).contains(cid)
                    &&& servers@.contains_key(cid.1)
                    &&& cid.0 == get_request@.key().0
                } implies servers@[cid.1]@@.timestamp()
                == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp() by {
                if cid.1 == id.1 {
                    assert(wb_replies@.insert(id).contains(cid));
                } else {
                    assert(servers@[cid.1]@@.timestamp()
                        == get_request@.value()->Get_0.servers()[cid.1]@@.timestamp());
                }
            }
        }

        Self::update_quorum(agree_with_max, wb_replies, max_resp, get_replies, id);
    }

    fn insert_write(&mut self, id: (u64, u64), resp: Response)
        requires
            ReadPred::inv(old(self).constant(), *old(self)),
            old(self).wb_request_id() is Some,
            old(self).max_resp is Some,
            old(self).client_id() == id.0,
            resp.req_type() is Write,
            resp.write().server_id() == id.1,
            resp.request() == old(self).wb_request@->Some_0.value(),
            old(self).constant().server_tokens_id == resp.write().server_token_id(),
            old(self).constant().server_locs.contains_key(resp.server_id()),
            old(self).constant().server_locs[resp.server_id()] == resp.write().loc(),
        ensures
            ReadPred::inv(self.constant(), *self),
            self.constant() == old(self).constant(),
            self.max_resp == old(self).max_resp,
            self.spec_get_replies() == old(self).spec_get_replies(),
            self.spec_wb_replies() == old(self).spec_wb_replies().insert(id),
            self.spec_max_resp() == old(self).spec_max_resp(),
        no_unwind
    {
        proof {
            use_type_invariant(&*self);
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        }

        Self::insert_wb_aux(
            &mut self.agree_with_max,
            &mut self.wb_replies,
            &mut self.servers,
            &mut self.server_tokens,
            &self.max_resp,
            &self.get_replies,
            &self.min_timestamp,
            &self.commitment_id,
            &self.wb_request,
            &self.get_request,
            id,
            resp,
        );
    }
}

pub struct ReadAccumGetPhase<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
    inner: ReadAccumulator<C>,
}

pub struct ReadAccumWbPhase<C: Channel<K = ChannelInv, Id = (u64, u64)>> {
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
            read_pred@.wb_request_id is None,
            server_tokens@@ <= servers@.locs(),
            servers@.inv(),
            servers@.is_lb(),
            get_request@.id() == read_pred@.request_map_id,
            get_request@.key().0 == read_pred@.client_id,
            get_request@.key().1 == read_pred@.get_request_id,
            get_request@.value().req_type() is Get,
            get_request@.value()->Get_0.servers().inv(),
            get_request@.value()->Get_0.servers().is_lb(),
            get_request@.value()->Get_0.servers().eq_timestamp(servers@),
            get_request@.value()->Get_0.servers() == read_pred@.orig_servers,
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
        &&& self.inner.wb_request_id() is None
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
            r.wb_request_id() is None,
            r.spec_wb_replies().is_empty(),
            r.spec_get_replies() == self.replies(),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(&self.inner);
        }

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
    pub fn new(mut accum: ReadAccumulator<C>, wb_request: Tracked<RequestProof>) -> (r: Self)
        requires
            accum.wb_request_id() is None,
            !accum.spec_get_replies().is_empty(),
            accum.spec_wb_replies().is_empty(),
            wb_request@.key().0 == accum.client_id(),
            wb_request@.id() == accum.constant().request_map_id,
            wb_request@.value().req_type() is Write,
            wb_request@.value()->Write_0.spec_timestamp() == accum.spec_max_timestamp(),
            wb_request@.value()->Write_0.servers().inv(),
            wb_request@.value()->Write_0.servers().eq_timestamp(accum.orig_servers()),
        ensures
            r.spec_request_tag() == wb_request@.key().1,
            r.replies().is_empty(),
            r.constant() == (ReadPred {
                wb_request_id: Some(wb_request@.key().1),
                ..accum.constant()
            }),
            r.spec_max_resp() == accum.spec_max_resp(),
    {
        proof {
            use_type_invariant(&accum);
        }
        accum.set_wb_request(wb_request);
        ReadAccumWbPhase { inner: accum }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.inner.wb_request_id() is Some
        &&& !self.inner.spec_get_replies().is_empty()
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.inner.wb_request_id()->Some_0
    }

    pub closed spec fn spec_max_resp(self) -> GetResponse {
        self.inner.spec_max_resp()
    }

    pub fn agree_with_max(&self) -> (r: &BTreeSet<u64>)
        ensures
            r@ == self.spec_agree_with_max(),
    {
        self.inner.agree_with_max()
    }

    pub closed spec fn spec_agree_with_max(self) -> Set<u64> {
        self.inner.spec_agree_with_max()
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
            r.spec_wb_replies() == self.replies(),
            !r.spec_get_replies().is_empty(),
            r.spec_agree_with_max() == self.spec_agree_with_max(),
            r.spec_max_resp() == self.spec_max_resp(),
    {
        proof {
            use_type_invariant(&self);
        }
        self.inner
    }
}

pub ghost struct ReadWbPred<C: Channel<K = ChannelInv>> {
    #[allow(unused)]
    pub read_pred: ReadPred<C>,
    #[allow(unused)]
    pub max_resp: GetResponse,
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> InvariantPredicate<
    ReadWbPred<C>,
    ReadAccumWbPhase<C>,
> for ReadWbPred<C> {
    open spec fn inv(pred: ReadWbPred<C>, v: ReadAccumWbPhase<C>) -> bool {
        &&& pred.read_pred == v.constant()
        &&& pred.max_resp == v.spec_max_resp()
    }
}

impl<C> ReplyAccumulator<C, ReadWbPred<C>> for ReadAccumWbPhase<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(
        &mut self,
        #[allow(unused_variables)]
        pred: Ghost<ReadWbPred<C>>,
        id: (u64, u64),
        reply: Response,
    )
        ensures
            self.constant() == old(self).constant(),
    {
        proof {
            use_type_invariant(&*self);
            use_type_invariant(&self.inner);

            assert(ReadWbPred::inv(pred@, *self));
            assert(self.constant() == pred@.read_pred);
            assert(self.channels().contains_key(id));
            let ghost chan = self.channels()[id];
            assert(chan.constant().commitment_id == self.inner.commitment_id@);
            assert(chan.constant().request_map_id == self.inner.request_map_id());
            assert(chan.spec_id() == id);

            assume(C::K::recv_inv(chan.constant(), id, reply));  // TODO(verus): this is a verus problem

            assert(self.inner.request_map_id() == reply.request_id());
        }
        reply.agree_request_opt(&mut self.inner.wb_request);
        reply.lemma_inv();

        proof {
            assert(reply.spec_tag() == pred@.read_pred.wb_request_id->Some_0);
            assert(reply.spec_tag() == reply.request_key().1);
            assert(id.0 == reply.request_key().0);
            let ghost wb_req = self.inner.wb_request@->Some_0;
            assert(reply.request_key().1 == wb_req.key().1);
            assert(reply.request_key() == wb_req.key());
            assert(reply.request() == wb_req.value());
            assert(reply.req_type() == wb_req.value().req_type());
            assert(reply.req_type() is Write);
        }
        assert(reply.req_type() is Write);
        assert(reply.request() == self.inner.wb_request@->Some_0.value());
        self.inner.insert_write(id, reply);
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

} // verus!
