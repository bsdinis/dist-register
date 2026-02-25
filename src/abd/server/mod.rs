#![allow(unused, non_shorthand_field_patterns)]

use crate::abd::invariants;
use crate::abd::invariants::committed_to::WriteCommitment;
use crate::abd::invariants::logatom::ReadPerm;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::logatom::WritePerm;
use crate::abd::invariants::StateInvariant;
use crate::abd::proto::GetRequest;
use crate::abd::proto::GetTimestampRequest;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::WriteRequest;
use crate::abd::proto::WriteResponse;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::server::register::MonotonicRegister;
use crate::abd::server::register::MonotonicRegisterInner;
use crate::abd::timestamp::Timestamp;
use crate::verdist::network::channel::Channel;
use crate::verdist::network::channel::Listener;
use crate::verdist::network::modelled::ModelledConnector;
use crate::verdist::network::modelled::ModelledListener;
use crate::verdist::rpc::proto::Tagged;

use std::collections::HashMap;
use std::sync::Arc;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::RwLock;

mod register;

verus! {

struct EmptyCond;

impl<V> vstd::rwlock::RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

#[allow(dead_code)]
struct LowerBoundPredicate {
    #[allow(dead_code)]
    loc: Loc,
}

impl vstd::rwlock::RwLockPredicate<Tracked<MonotonicTimestampResource>> for LowerBoundPredicate {
    closed spec fn inv(self, lb: Tracked<MonotonicTimestampResource>) -> bool {
        &&& lb@@ is LowerBound
        &&& lb@.loc() == self.loc
    }
}

#[verifier::reject_recursive_types(C)]
pub struct RegisterServer<L, C, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    id: u64,
    listener: L,
    connected: RwLock<HashMap<u64, C>, EmptyCond>,
    register: MonotonicRegister<ML, RL>,
}

impl<L, C, ML, RL> RegisterServer<L, C, ML, RL> where
    L: Listener<C>,
    C: Channel<R = Tagged<Request>, S = Tagged<Response>, Id = (u64, u64)>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(listener: L, id: u64, state_inv: Tracked<Arc<StateInvariant<ML, RL>>>) -> (r: Self)
        requires
            state_inv@.namespace() == invariants::state_inv_id(),
    {
        RegisterServer {
            id,
            register: MonotonicRegister::new(id, state_inv),
            connected: RwLock::new(HashMap::new(), Ghost(EmptyCond)),
            listener,
        }
    }

    fn accept(&self, channel: C) {
        let (mut guard, handle) = self.connected.acquire_write();
        guard.insert(channel.id().1, channel);
        handle.release_write(guard);
    }

    fn handle_get(&self, req: GetRequest) -> Response {
        Response::Get(self.register.read(req))
    }

    fn handle_get_timestamp(&self, req: GetTimestampRequest) -> Response {
        Response::GetTimestamp(self.register.read_timestamp(req))
    }

    // TODO: must receive a lower bound here
    fn handle_write(&self, req: WriteRequest) -> Response {
        Response::Write(self.register.write(req))
    }

    fn handle(&self, request: Tagged<Request>, _client_id: u64) -> Tagged<Response> {
        let tag = request.tag;
        match request.into_inner() {
            Request::Get(req) => { Tagged { tag, inner: self.handle_get(req) } },
            Request::GetTimestamp(req) => { Tagged { tag, inner: self.handle_get_timestamp(req) } },
            Request::Write(req) => { Tagged { tag, inner: self.handle_write(req) } },
        }
    }

    fn poll(&self) -> bool {
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time
        let mut i = 10;
        while i > 0
            decreases i,
        {
            match self.listener.try_accept() {
                Ok(channel) => self.accept(channel),
                Err(crate::verdist::network::error::TryListenError::Empty) => {
                    break ;
                },
                Err(crate::verdist::network::error::TryListenError::Disconnected) => {
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
                Err(crate::verdist::network::error::TryRecvError::Empty) => {},
                Err(crate::verdist::network::error::TryRecvError::Disconnected) => {
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
    C: Channel<R = Tagged<Request>, S = Tagged<Response>, Id = (u64, u64)>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    let tracked state_inv;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>();
        state_inv = s;
    }
    RegisterServer::new(listener, server_id, Tracked(state_inv))
}

} // verus!
pub fn run_modelled_server(server_id: u64) -> ModelledConnector<Tagged<Response>, Tagged<Request>> {
    let (listener, connector) = crate::verdist::network::modelled::listen_channel(server_id);
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
