use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::network::modelled::ModelledConnector;
use crate::network::Channel;
use crate::network::Listener;
use crate::proto::Tagged;

use std::collections::HashMap;
use std::sync::Arc;

use super::proto::Timestamp;

use vstd::prelude::*;
use vstd::rwlock::RwLock;

verus! {

struct EmptyCond;

impl<V> vstd::rwlock::RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

#[verifier::reject_recursive_types(C)]
struct RegisterServer<L, C> {
    id: u64,
    register: RwLock<(Option<u64>, Timestamp), EmptyCond>,
    connected: RwLock<HashMap<u64, C>, EmptyCond>,
    listener: L,
}

impl<L, C> RegisterServer<L, C>
where
    L: Listener<C>,
    C: Channel<R = Tagged<Request>, S = Tagged<Response>>,
{
    pub fn new(listener: L, id: u64) -> Self {
        RegisterServer {
            id,
            register: RwLock::new((None, Timestamp::default()), Ghost(EmptyCond)),
            connected: RwLock::new(HashMap::new(), Ghost(EmptyCond)),
            listener,
        }
    }

    fn accept(&self, channel: C) {
        let (mut guard, handle) = self.connected.acquire_write();
        guard.insert(channel.id(), channel);
        handle.release_write(guard);
    }

    fn handle(&self, request: Tagged<Request>, _client_id: u64) -> Tagged<Response> {
        match request.into_inner() {
            Request::Get => {
                let handle = self.register.acquire_read();
                let (val, timestamp) = handle.borrow();
                let val = *val;
                let timestamp = *timestamp;
                handle.release_read();

                Tagged {
                    tag: request.tag,
                    inner: Response::Get {
                        val,
                        timestamp
                    },
                }
            }
            Request::GetTimestamp => {
                let handle = self.register.acquire_read();
                let (_val, timestamp) = handle.borrow();
                let timestamp = *timestamp;
                handle.release_read();

                Tagged {
                    tag: request.tag,
                    inner: Response::GetTimestamp { timestamp },
                }
            }
            Request::Write { val, timestamp } => {
                let (mut guard, handle) = self.register.acquire_write();

                if guard.1.seqno < timestamp.seqno ||
                    (guard.1.seqno == timestamp.seqno && guard.1.client_id < timestamp.client_id) {
                    guard = (val, timestamp);
                }

                handle.release_write(guard);

                Tagged {
                    tag: request.tag,
                    inner: Response::Write,
                }
            }
        }
    }

    fn poll(&self) -> bool {
        // verus does not support unbounded loops + streams probably don't/can't have specs
        // so we do this up to 10 times every time

        let mut i = 10;
        while i > 0
            decreases i
        {
            match self.listener.try_accept() {
                Ok(channel) => self.accept(channel),
                Err(crate::network::error::TryListenError::Empty) => {
                    break;
                }
                Err(crate::network::error::TryListenError::Disconnected) => {
                    return false;
                }
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
                        if channel.send(response).is_err() {
                            drop.push(*id);
                        }
                    }
                    Err(crate::network::error::TryRecvError::Empty) => {}
                    Err(crate::network::error::TryRecvError::Disconnected) => {
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
    let (listener, connector) = crate::network::modelled::listen_channel(id);
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
