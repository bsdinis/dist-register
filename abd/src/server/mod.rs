use crate::channel::ChannelInv;
#[cfg(verus_only)]
use crate::invariants;
#[cfg(verus_only)]
use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::logatom::ReadPerm;
use crate::invariants::logatom::RegisterRead;
use crate::invariants::logatom::RegisterWrite;
use crate::invariants::logatom::WritePerm;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverse;
use crate::invariants::StateInvariant;
use crate::proto::GetRequest;
use crate::proto::GetTimestampRequest;
use crate::proto::Request;
use crate::proto::RequestInner;
use crate::proto::Response;
use crate::proto::ResponseInner;
use crate::proto::WriteRequest;
#[cfg(verus_only)]
use crate::proto::WriteResponse;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::server::register::MonotonicRegister;
#[cfg(verus_only)]
use crate::server::register::MonotonicRegisterInner;
#[cfg(verus_only)]
use crate::timestamp::Timestamp;
use verdist::network::channel::Channel;
#[cfg(verus_only)]
use verdist::network::channel::ChannelInvariant;
use verdist::network::channel::Listener;
use verdist::network::modelled::ModelledConnector;
#[cfg(verus_only)]
use verdist::network::modelled::ModelledListener;
use verdist::rpc::proto::TaggedMessage;

use std::collections::HashSet;
use std::sync::Arc;

#[cfg(verus_only)]
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;

pub mod register;

verus! {

#[allow(dead_code)]
struct LowerBoundPredicate {
    #[allow(dead_code)]
    loc: Loc,
}

impl RwLockPredicate<Tracked<MonotonicTimestampResource>> for LowerBoundPredicate {
    closed spec fn inv(self, lb: Tracked<MonotonicTimestampResource>) -> bool {
        &&& lb@@ is LowerBound
        &&& lb@.loc() == self.loc
    }
}

pub struct ServerInv {
    pub channel_inv: ChannelInv,
    pub server_id: u64,
}

impl<C> vstd::rwlock::RwLockPredicate<Vec<C>> for ServerInv where
    C: Channel<Id = (u64, u64), R = Request, S = Response, K = ChannelInv>,
 {
    open spec fn inv(self, v: Vec<C>) -> bool {
        forall|idx: int|
            0 <= idx < v@.len() ==> {
                let chan = #[trigger] v@[idx];
                &&& self.channel_inv == chan.constant()
                &&& self.server_id == chan.spec_id().0
            }
    }
}

#[verifier::reject_recursive_types(C)]
pub struct RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    /// ID of the server
    id: u64,
    /// Listener channel
    listener: L,
    /// Connected clients
    connected: RwLock<Vec<C>, ServerInv>,
    /// Register state
    register: MonotonicRegister<ML, RL>,
}

impl<L, C, ML, RL> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(listener: L, id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().server_locs.contains_key(id),
    {
        let empty = Vec::new();
        let ghost channel_inv = ChannelInv::from_state_pred(state_inv@.constant());
        let ghost server_inv = ServerInv { channel_inv, server_id: id };
        assert(server_inv.inv(empty));
        RegisterServer {
            id,
            register: MonotonicRegister::new(id, state_inv),
            connected: RwLock::new(empty, Ghost(server_inv)),
            listener,
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.register.id() == self.id
        &&& self.register.commitment_id() == self.commitment_id()
        &&& self.register.server_token_id() == self.server_token_id()
        &&& self.connected.pred().server_id == self.id
        &&& self.server_locs().contains_key(self.id)
        &&& self.server_locs()[self.id] == self.register.resource_loc()
    }

    closed spec fn commitment_id(self) -> Loc {
        self.connected.pred().channel_inv.commitment_id
    }

    closed spec fn server_token_id(self) -> Loc {
        self.connected.pred().channel_inv.server_tokens_id
    }

    closed spec fn server_locs(self) -> Map<u64, Loc> {
        self.connected.pred().channel_inv.server_locs
    }

    fn accept(&self, channel: C)
        requires
            channel.constant() == self.connected.pred().channel_inv,
    {
        proof {
            use_type_invariant(self);
        }
        let (mut guard, handle) = self.connected.acquire_write();
        assume(channel.spec_id().0 == self.id);  // TODO(connector)
        guard.push(channel);
        assert(ServerInv::inv(self.connected.pred(), guard));
        handle.release_write(guard);
    }

    fn handle_get(&self, req: GetRequest) -> (r: ResponseInner)
        requires
            req.servers().locs() == self.server_locs(),
        ensures
            r is Get,
            ({
                let resp = r->Get_0;
                &&& resp.server_id() == self.id
                &&& resp.spec_commitment().id() == self.commitment_id()
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& req.servers().contains_key(resp.server_id())
                &&& req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::Get(self.register.read(req))
    }

    fn handle_get_timestamp(&self, req: GetTimestampRequest) -> (r: ResponseInner)
        ensures
            r is GetTimestamp,
            ({
                let resp = r->GetTimestamp_0;
                &&& resp.server_id() == self.id
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::GetTimestamp(self.register.read_timestamp(req))
    }

    fn handle_write(&self, req: WriteRequest) -> (r: ResponseInner)
        ensures
            r is Write,
            ({
                let resp = r->Write_0;
                &&& resp.server_id() == self.id
            }),
    {
        proof {
            use_type_invariant(self);
        }
        ResponseInner::Write(self.register.write(req))
    }

    fn handle(&self, request: Request, client_id: u64) -> (r: Response)
        requires
            request.request_key() == (client_id, request.spec_tag()),
            request.req_type() is Get ==> {
                let get_req = request.get();
                &&& get_req.servers().locs() == self.server_locs()
            },
        ensures
            r.spec_tag() == request.spec_tag(),
            r.request_id() == request.request_id(),
            r.request_key() == request.request_key(),
            r.request().spec_eq(request.request()),
            r.server_id() == self.id,
            request.req_type() == r.req_type(),
            r.req_type() is Get ==> ({
                let get_req = request.get();
                let resp = r.get();
                &&& resp.spec_commitment().id() == self.commitment_id()
                &&& resp.server_token_id() == self.server_token_id()
                &&& self.server_locs().contains_key(resp.server_id())
                &&& self.server_locs()[resp.server_id()] == resp.loc()
                &&& get_req.servers().contains_key(resp.server_id())
                &&& get_req.servers()[resp.server_id()]@@.timestamp() <= resp.spec_timestamp()
            }),
    {
        let (request_id, request_inner, request_proof) = request.destruct();
        proof {}
        let resp_inner = match request_inner {
            RequestInner::Get(req) => self.handle_get(req),
            RequestInner::GetTimestamp(req) => self.handle_get_timestamp(req),
            RequestInner::Write(req) => self.handle_write(req),
        };

        proof {
            if request_inner is Get {
                let get_req = request_inner->Get_0;
                let proof_get_req = request_proof@.value()->Get_0;
                assume(proof_get_req.servers().inv());  // TODO(verus): type invariants on spec items
                assume(get_req.servers().inv());  // TODO(verus): type invariants on spec items
                GetRequest::lemma_spec_eq(proof_get_req, get_req);
                ServerUniverse::lemma_eq(proof_get_req.servers(), get_req.servers());
                proof_get_req.servers().lemma_locs();
            }
        }

        let r = Response::new(request_id, resp_inner, request_proof);
        proof {
            RequestInner::spec_eq_refl(r.request());
        }
        r
    }

    fn poll(&self) -> bool {
        proof {
            use_type_invariant(self);
            broadcast use vstd::seq_lib::group_filter_ensures;

        }
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            decreases i,
        {
            match self.listener.try_accept(Ghost(|l| self.connected.pred().channel_inv)) {
                Ok(channel) => {
                    assert(channel.constant() == self.connected.pred().channel_inv);
                    self.accept(channel)
                },
                Err(verdist::network::error::TryListenError::Empty) => {
                    break ;
                },
                Err(verdist::network::error::TryListenError::Disconnected) => {
                    return false;
                },
            }

            i -= 1;
        }

        let mut drop = HashSet::new();
        let (mut connected, handle) = self.connected.acquire_write();

        let ghost connected_pred = self.connected.pred();
        let iterator = connected.iter();
        #[allow(unused_variables)]
        let mut idx = 0usize;
        for channel in it: iterator
            invariant
                self.connected.pred() == connected_pred,
                connected_pred.server_id == self.id,
                idx == it.pos,
                connected@ == it.elements,
                forall|idx|
                    0 <= idx < connected@.len() ==> {
                        let chan = #[trigger] connected@[idx];
                        &&& connected_pred.channel_inv == chan.constant()
                        &&& connected_pred.server_id == chan.spec_id().0
                    },
        {
            match channel.try_recv() {
                Ok(req) => {
                    assert(C::K::recv_inv(channel.constant(), channel.spec_id(), req));
                    let response = self.handle(req, channel.id().1);
                    assert(C::K::send_inv(channel.constant(), channel.spec_id(), response));
                    if channel.send(&response).is_err() {
                        drop.insert(channel.id());
                    }
                },
                Err(verdist::network::error::TryRecvError::Empty) => {},
                Err(verdist::network::error::TryRecvError::Disconnected) => {
                    drop.insert(channel.id());
                },
            }
            assume(idx < usize::MAX);  // XXX: overflow
            idx += 1;
        }

        let ghost old_c = connected@;
        let filter_fn = |c: &C| !drop.contains(&c.id());
        connected.retain(filter_fn);
        proof {
            let ghost server_inv = self.connected.pred();
            assert forall|idx| 0 <= idx < connected@.len() implies {
                let chan = #[trigger] connected@[idx];
                &&& server_inv.channel_inv == chan.constant()
                &&& server_inv.server_id == chan.spec_id().0
            } by {
                let chan = #[trigger] connected@[idx];
                old_c.lemma_filter_contains_rev(|c| filter_fn.ensures((&c,), true), chan);
            }
        }
        handle.release_write(connected);

        true
    }
}

fn create_server<L, C, ML, RL>(server_id: u64, listener: L) -> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    // XXX: this comes from the limitation on run_modelled_server
    let ghost server_ids = arbitrary::<Set<u64>>().insert(server_id);
    let tracked state_inv;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>(server_ids);
        state_inv = s;
    }
    RegisterServer::new(listener, server_id, Tracked(state_inv))
}

} // verus!
// Why is this unverified:
// - minor: no support for tracing
// - major: verus does not support threads
pub fn run_modelled_server(server_id: u64) -> ModelledConnector<Response, Request>
// requires
    // server_ids@.contains(server_id),
{
    let (listener, connector) = verdist::network::modelled::listen_channel(server_id);
    std::thread::spawn(move || {
        let server = Arc::new(create_server::<_, _, WritePerm, ReadPerm<'_>>(
            server_id, listener,
        ));
        tracing::info!("starting server {}", server.id);

        std::thread::scope(|s| {
            for _ in 0..5 {
                let serv = server.clone();
                s.spawn(move || while serv.poll() {});
            }
        });
    });

    connector
}
