use std::sync::atomic::AtomicBool;

use crossbeam_channel::unbounded;
use crossbeam_channel::Receiver;
use crossbeam_channel::Sender;

use crate::verdist::network::channel::Channel;
use crate::verdist::network::channel::Connector;
use crate::verdist::network::channel::Listener;
use crate::verdist::network::error::ConnectError;
use crate::verdist::network::error::SendError;
use crate::verdist::network::error::TryListenError;
use crate::verdist::network::error::TryRecvError;

pub struct ModelledListener<R, S> {
    id: u64,
    registering_rx: Receiver<u64>,
    connection_tx: Sender<(u64, Sender<R>, Receiver<S>)>,
}

pub struct ModelledConnector<R, S> {
    registering_tx: Sender<u64>,
    connection_rx: Receiver<(u64, Sender<S>, Receiver<R>)>,
}

pub struct ClientChannel<R, S> {
    tx: Sender<S>,
    rx: Receiver<R>,
    client_id: u64,
    faulty: AtomicBool,
    avg_latency: std::time::Duration,
    stddev_latency: std::time::Duration,
}

pub struct ServerChannel<R, S> {
    tx: Sender<S>,
    rx: Receiver<R>,
    server_id: u64,
    faulty: AtomicBool,
    avg_latency: std::time::Duration,
    stddev_latency: std::time::Duration,
}

impl<R, S> Channel for ClientChannel<R, S> {
    type R = R;
    type S = S;

    fn try_recv(&self) -> Result<R, crate::verdist::network::error::TryRecvError> {
        if !self.faulty.load(std::sync::atomic::Ordering::SeqCst) {
            self.wait();
            self.rx.try_recv().map_err(|e| e.into())
        } else {
            Err(crate::verdist::network::error::TryRecvError::Empty)
        }
    }

    fn send(&self, v: S) -> Result<(), crate::verdist::network::error::SendError<S>> {
        if !self.faulty.load(std::sync::atomic::Ordering::SeqCst) {
            self.wait();
            self.tx.send(v)?;
        }

        Ok(())
    }

    fn id(&self) -> u64 {
        self.client_id
    }

    fn add_latency(&mut self, avg: std::time::Duration, stddev: std::time::Duration) {
        self.avg_latency = avg;
        self.stddev_latency = stddev;
    }

    fn delay(&self) -> (std::time::Duration, std::time::Duration) {
        (self.avg_latency, self.stddev_latency)
    }
}

impl<R, S> Channel for ServerChannel<R, S> {
    type R = R;
    type S = S;

    fn try_recv(&self) -> Result<R, crate::verdist::network::error::TryRecvError> {
        if !self.faulty.load(std::sync::atomic::Ordering::SeqCst) {
            self.wait();
            self.rx.try_recv().map_err(|e| e.into())
        } else {
            Err(crate::verdist::network::error::TryRecvError::Empty)
        }
    }

    fn send(&self, v: S) -> Result<(), crate::verdist::network::error::SendError<S>> {
        if !self.faulty.load(std::sync::atomic::Ordering::SeqCst) {
            self.wait();
            self.tx.send(v)?;
        }

        Ok(())
    }

    fn id(&self) -> u64 {
        self.server_id
    }

    fn add_latency(&mut self, avg: std::time::Duration, stddev: std::time::Duration) {
        self.avg_latency = avg;
        self.stddev_latency = stddev;
    }

    fn delay(&self) -> (std::time::Duration, std::time::Duration) {
        (self.avg_latency, self.stddev_latency)
    }
}

impl<R, S> ClientChannel<R, S> {
    pub fn new(client_id: u64, tx: Sender<S>, rx: Receiver<R>) -> Self {
        ClientChannel {
            tx,
            rx,
            client_id,
            faulty: AtomicBool::new(false),
            avg_latency: Default::default(),
            stddev_latency: Default::default(),
        }
    }
}

impl<R, S> ServerChannel<R, S> {
    pub fn new(server_id: u64, tx: Sender<S>, rx: Receiver<R>) -> Self {
        ServerChannel {
            tx,
            rx,
            server_id,
            faulty: AtomicBool::new(false),
            avg_latency: Default::default(),
            stddev_latency: Default::default(),
        }
    }
}

impl<R, S> Listener<ClientChannel<R, S>> for ModelledListener<R, S> {
    fn try_accept(
        &self,
    ) -> Result<ClientChannel<R, S>, crate::verdist::network::error::TryListenError> {
        let client_id = self.registering_rx.try_recv()?;
        eprintln!(
            "[server|{:>3}]: accepting a connection from client {client_id}",
            self.id
        );

        let (resp_tx, resp_rx) = unbounded();
        let (req_tx, req_rx) = unbounded();

        self.connection_tx
            .send((self.id, req_tx, resp_rx))
            .map_err(|_| TryListenError::Disconnected)?;

        Ok(ClientChannel::new(client_id, resp_tx, req_rx))
    }
}

impl<R, S> Connector<ServerChannel<R, S>> for ModelledConnector<R, S> {
    fn connect(&self, id: u64) -> Result<ServerChannel<R, S>, ConnectError> {
        eprintln!("[client|{id:>3}]: connecting from client");
        self.registering_tx.send(id).map_err(|_| ConnectError)?;
        let (server_id, tx, rx) = self.connection_rx.recv().map_err(|_| ConnectError)?;
        Ok(ServerChannel::new(server_id, tx, rx))
    }
}

pub fn listen_channel<R, S>(server_id: u64) -> (ModelledListener<R, S>, ModelledConnector<S, R>) {
    let (registering_tx, registering_rx) = unbounded();
    let (connection_tx, connection_rx) = unbounded();
    let listener = ModelledListener {
        id: server_id,
        registering_rx,
        connection_tx,
    };

    let connector = ModelledConnector {
        registering_tx,
        connection_rx,
    };

    (listener, connector)
}

impl From<crossbeam_channel::TryRecvError> for TryListenError {
    fn from(value: crossbeam_channel::TryRecvError) -> Self {
        match value {
            crossbeam_channel::TryRecvError::Empty => TryListenError::Empty,
            crossbeam_channel::TryRecvError::Disconnected => TryListenError::Disconnected,
        }
    }
}

impl From<crossbeam_channel::TryRecvError> for TryRecvError {
    fn from(value: crossbeam_channel::TryRecvError) -> Self {
        match value {
            crossbeam_channel::TryRecvError::Empty => TryRecvError::Empty,
            crossbeam_channel::TryRecvError::Disconnected => TryRecvError::Disconnected,
        }
    }
}

impl<S> From<crossbeam_channel::SendError<S>> for SendError<S> {
    fn from(value: crossbeam_channel::SendError<S>) -> Self {
        SendError(value.0)
    }
}
