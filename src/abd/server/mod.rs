use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;
use crate::abd::server::register::MonotonicRegister;
use crate::verdist::network::channel::Channel;
use crate::verdist::network::channel::Listener;
use crate::verdist::network::modelled::ModelledConnector;
use crate::verdist::rpc::proto::Tagged;

use std::collections::HashMap;
use std::sync::Arc;

use vstd::prelude::*;
use vstd::rwlock::RwLock;

mod register;

verus! {

struct EmptyCond;

impl<V> vstd::rwlock::RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

struct LowerBoundPredicate {
    #[allow(dead_code)]
    loc: Ghost<int>
}

impl vstd::rwlock::RwLockPredicate<Tracked<MonotonicTimestampResource>> for LowerBoundPredicate {
    closed spec fn inv(self, lb: Tracked<MonotonicTimestampResource>) -> bool {
           lb@@ is LowerBound && lb@.loc() == self.loc
    }
}

#[verifier::reject_recursive_types(C)]
pub struct RegisterServer<L, C> {
    id: u64,
    register: MonotonicRegister,
    connected: RwLock<HashMap<u64, C>, EmptyCond>,
    listener: L,
    register_lower_bound: RwLock<Tracked<MonotonicTimestampResource>, LowerBoundPredicate>,
}

impl<L, C> RegisterServer<L, C>
where
    L: Listener<C>,
    C: Channel<R = Tagged<Request>, S = Tagged<Response>>,
{
    pub fn new(listener: L, id: u64) -> (r: Self)
        ensures r.inv()
    {
        let (register, register_lower_bound)= MonotonicRegister::default();
        let register_lower_bound = RwLock::new(
            register_lower_bound,
            Ghost(LowerBoundPredicate { loc: register.loc() })
        );
        RegisterServer {
            id,
            register,
            connected: RwLock::new(HashMap::new(), Ghost(EmptyCond)),
            listener,
            register_lower_bound,
        }
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.register.inv()
        &&& self.register_lower_bound.pred() == LowerBoundPredicate { loc: self.register.loc() }
    }

    fn accept(&self, channel: C)
        requires self.inv()
    {
        let (mut guard, handle) = self.connected.acquire_write();
        guard.insert(channel.id(), channel);
        handle.release_write(guard);
    }

    fn handle_get(&self) -> Response
        requires self.inv()
    {
        let (lower_bound, handle) = self.register_lower_bound.acquire_write();
        let inner_register = self.register.read(lower_bound);
        let response = Response::Get {
            val: inner_register.val(),
            timestamp: inner_register.timestamp(),
            lb: inner_register.lower_bound(),
        };
        let resource = inner_register.get_resource();
        handle.release_write(resource);
        response
    }

    fn handle_get_timestamp(&self) -> Response
        requires self.inv()
    {
        let (lower_bound, handle) = self.register_lower_bound.acquire_write();
        let inner_register = self.register.read(lower_bound);
        let response = Response::GetTimestamp {
            timestamp: inner_register.timestamp(),
            lb: inner_register.lower_bound(),
        };
        let resource = inner_register.get_resource();
        handle.release_write(resource);
        response
    }

    fn handle_write(&self, val: Option<u64>, timestamp: Timestamp) -> Response
        requires self.inv()
    {
        let (_lower_bound, handle) = self.register_lower_bound.acquire_write();
        let lower_bound = self.register.write(val, timestamp);
        let tracked new_lb = lower_bound.borrow().extract_lower_bound();
        let response = Response::Write {
            lb: Tracked(new_lb)
        };
        handle.release_write(lower_bound);
        response
    }

    fn handle(&self, request: Tagged<Request>, _client_id: u64) -> Tagged<Response>
        requires self.inv()
    {
        match request.into_inner() {
            Request::Get => {
                let inner = self.handle_get();

                Tagged {
                    tag: request.tag,
                    inner
                }
            }
            Request::GetTimestamp => {
                let inner = self.handle_get_timestamp();
                Tagged {
                    tag: request.tag,
                    inner
                }
            }
            Request::Write { val, timestamp } => {
                let inner = self.handle_write(val, timestamp);
                Tagged {
                    tag: request.tag,
                    inner
                }
            }
        }
    }

    fn poll(&self) -> bool
        requires self.inv()
    {
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time

        let mut i = 10;
        while i > 0
            invariant self.inv(),
            decreases i
        {
            match self.listener.try_accept() {
                Ok(channel) => self.accept(channel),
                Err(crate::verdist::network::error::TryListenError::Empty) => {
                    break;
                }
                Err(crate::verdist::network::error::TryListenError::Disconnected) => {
                    return false;
                }
            }

            i -= 1;
        }

        let mut drop = Vec::new();
        let (mut connected, handle) = self.connected.acquire_write();

        let it = connected.iter();
        for (id, channel) in it
            invariant self.inv()
        {
            match channel.try_recv() {
                    Ok(req) => {
                        let response = self.handle(req, *id);
                        if channel.send(&response).is_err() {
                            drop.push(*id);
                        }
                    }
                    Err(crate::verdist::network::error::TryRecvError::Empty) => {}
                    Err(crate::verdist::network::error::TryRecvError::Disconnected) => {
                        drop.push(*id);
                    }
                }
        }

        for id in drop {
            connected.remove(&id);
        }

        handle.release_write(connected);

        true
    }
}

}

pub fn run_modelled_server(id: u64) -> ModelledConnector<Tagged<Response>, Tagged<Request>> {
    let (listener, connector) = crate::verdist::network::modelled::listen_channel(id);
    std::thread::spawn(move || {
        let server = RegisterServer::new(listener, id);
        let server = Arc::new(server);
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
