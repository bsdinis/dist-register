#![allow(unused, non_shorthand_field_patterns)]

use crate::channel::ChannelInv;
use crate::invariants;
use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::logatom::ReadPerm;
use crate::invariants::logatom::RegisterRead;
use crate::invariants::logatom::RegisterWrite;
use crate::invariants::logatom::WritePerm;
use crate::invariants::StateInvariant;
use crate::proto::GetRequest;
use crate::proto::GetTimestampRequest;
use crate::proto::Request;
use crate::proto::Response;
use crate::proto::WriteRequest;
use crate::proto::WriteResponse;
use crate::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::server::register::MonotonicRegister;
use crate::server::register::MonotonicRegisterInner;
use crate::timestamp::Timestamp;
use verdist::network::channel::Channel;
use verdist::network::channel::ChannelInvariant;
use verdist::network::channel::Listener;
use verdist::network::modelled::ModelledConnector;
use verdist::network::modelled::ModelledListener;
use verdist::rpc::proto::TaggedMessage;

use std::collections::HashMap;
use std::sync::Arc;

use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;

mod register;

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

#[verifier::reject_recursive_types(C)]
pub struct RegisterServer<L, C, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
    C: Channel<R = Request, S = Response, Id = (u64, u64), K = ChannelInv>,
 {
    id: u64,
    listener: L,
    connected: RwLock<HashMap<u64, C>, ChannelInv>,
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
    {
        let empty = HashMap::new();
        let ghost pred = ChannelInv {  };
        assert(pred.inv(empty));
        RegisterServer {
            id,
            register: MonotonicRegister::new(id, state_inv),
            connected: RwLock::new(empty, Ghost(pred)),
            listener,
        }
    }

    fn accept(&self, channel: C) {
        let (mut guard, handle) = self.connected.acquire_write();
        guard.insert(channel.id().1, channel);
        handle.release_write(guard);
    }

    fn handle_get(&self, req: GetRequest) -> (r: Response)
        ensures
            r.spec_tag() == req.spec_tag(),
            r is Get,
    {
        Response::Get(self.register.read(req))
    }

    fn handle_get_timestamp(&self, req: GetTimestampRequest) -> (r: Response)
        ensures
            r.spec_tag() == req.spec_tag(),
            r is GetTimestamp,
    {
        Response::GetTimestamp(self.register.read_timestamp(req))
    }

    fn handle_write(&self, req: WriteRequest) -> (r: Response)
        ensures
            r.spec_tag() == req.spec_tag(),
            r is Write,
    {
        Response::Write(self.register.write(req))
    }

    fn handle(&self, request: Request, _client_id: u64) -> (r: Response)
        ensures
            r.spec_tag() == request.spec_tag(),
    {
        match request {
            Request::Get(req) => self.handle_get(req),
            Request::GetTimestamp(req) => self.handle_get_timestamp(req),
            Request::Write(req) => self.handle_write(req),
        }
    }

    fn poll(&self) -> bool {
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            decreases i,
        {
            match self.listener.try_accept(|_listener| Ghost(ChannelInv {  })) {
                Ok(channel) => self.accept(channel),
                Err(verdist::network::error::TryListenError::Empty) => {
                    break ;
                },
                Err(verdist::network::error::TryListenError::Disconnected) => {
                    return false;
                },
            }

            i -= 1;
        }

        let mut drop = Vec::new();
        let (mut connected, handle) = self.connected.acquire_write();

        let it = connected.iter();
        for (id, channel) in it {
            match channel.try_recv() {
                Ok(req) => {
                    let response = self.handle(req, *id);
                    if channel.send(&response).is_err() {
                        drop.push(*id);
                    }
                },
                Err(verdist::network::error::TryRecvError::Empty) => {},
                Err(verdist::network::error::TryRecvError::Disconnected) => {
                    drop.push(*id);
                },
            }
        }

        for id in drop {
            connected.remove(&id);
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
