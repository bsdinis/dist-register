use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::network::Channel;
use crate::network::Listener;
use crate::network::modelled::ModelledConnector;
use crate::proto::Tagged;

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::RwLock;

use super::proto::Timestamp;

struct RegisterServer<L, C> {
    id: u64,
    register: RwLock<(Option<u64>, Timestamp)>,
    connected: Mutex<HashMap<u64, C>>,
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
            register: RwLock::new((None, Timestamp::default())),
            connected: Mutex::new(HashMap::new()),
            listener,
        }
    }

    fn accept(&self, channel: C) {
        tracing::debug!(client_id = channel.id(), "accepting new client");
        self.connected.lock().unwrap().insert(channel.id(), channel);
    }

    fn handle(&self, request: Tagged<Request>, client_id: u64) -> Tagged<Response> {
        tracing::info!(?request, client_id, "handle@{}", self.id);
        match *request {
            Request::Get => {
                let guard = self.register.read().unwrap();

                Tagged {
                    tag: request.tag,
                    inner: Response::Get {
                        val: guard.0,
                        timestamp: guard.1,
                    },
                }
            }
            Request::GetTimestamp => {
                let guard = self.register.read().unwrap();

                Tagged {
                    tag: request.tag,
                    inner: Response::GetTimestamp { timestamp: guard.1 },
                }
            }
            Request::Write { val, timestamp } => {
                let mut guard = self.register.write().unwrap();

                if guard.1 < timestamp {
                    *guard = (val, timestamp);
                }

                Tagged {
                    tag: request.tag,
                    inner: Response::Write,
                }
            }
        }
    }

    fn poll(&self) -> bool {
        loop {
            match self.listener.try_accept() {
                Ok(channel) => self.accept(channel),
                Err(crate::network::error::TryListenError::Empty) => {
                    break;
                }
                Err(crate::network::error::TryListenError::Disconnected) => {
                    return false;
                }
            }
        }

        let mut drop = Vec::new();
        let mut connected = self.connected.lock().unwrap();
        for (id, channel) in connected.iter() {
            match channel.try_recv() {
                Ok(req) => {
                    tracing::debug!(
                        client_id = channel.id(),
                        request_tag = req.tag,
                        "received request"
                    );
                    let response = self.handle(req, *id);
                    if channel.send(response).is_err() {
                        tracing::debug!("client {id} disconnected on send");
                        drop.push(*id);
                    }
                    break;
                }
                Err(crate::network::error::TryRecvError::Empty) => {}
                Err(crate::network::error::TryRecvError::Disconnected) => {
                    tracing::debug!("client {id} disconnected on receive");
                    drop.push(*id);
                    break;
                }
            }
        }

        for id in drop {
            tracing::debug!(client_id = id, "dropping client");
            connected.remove(&id);
        }

        true
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
