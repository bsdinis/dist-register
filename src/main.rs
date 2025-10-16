use clap::Parser;

#[allow(unused_imports)]
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

use std::collections::BTreeSet;
use std::collections::HashMap;
#[allow(unused_imports)]
use std::sync::Arc;
#[allow(unused_imports)]
use std::sync::Condvar;
#[allow(unused_imports)]
use std::sync::Mutex;

mod abd;
mod verdist;

use abd::client::AbdPool;
use abd::client::AbdRegisterClient;
use abd::invariants::logatom::ReadPerm;
use abd::invariants::logatom::RegisterRead;
use abd::invariants::logatom::WritePerm;
use abd::proto::Timestamp;
use abd::server::run_modelled_server;
use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
use verdist::pool::FlawlessPool;
use verdist::rpc::proto::Tagged;

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
struct Args {
    #[arg(short, long, default_value_t = 5)]
    n_servers: u64,

    #[arg(long, default_value_t = 3)]
    n_reads: u64,

    #[arg(long, default_value_t = 2)]
    n_writes: u64,

    #[arg(long)]
    no_delay: bool,

    #[arg(long, default_value_t = 1)]
    client_id: u64,
}

impl From<ConnectError> for Error {
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl From<abd::client::error::ReadError<ReadPerm<'_>>> for Error {
    fn from(value: abd::client::error::ReadError<ReadPerm<'_>>) -> Self {
        Error::AbdRead(format!("{:?}", value))
    }
}

impl From<abd::client::error::WriteError> for Error {
    fn from(value: abd::client::error::WriteError) -> Self {
        Error::AbdWrite(value)
    }
}

impl std::error::Error for Error {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match self {
            Error::Connection(e) => Some(e),
            Error::AbdRead(e) => None,
            Error::AbdWrite(e) => Some(e),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
        }
    }
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
        }
    }
}

verus! {

enum Error {
    Connection(ConnectError),
    AbdRead(String),
    AbdWrite(abd::client::error::WriteError),
}

#[verifier::external_trait_specification]
pub trait ExError: std::fmt::Debug + std::fmt::Display {
    type ExternalTraitSpecificationFor: std::error::Error;
}

pub assume_specification[std::time::Duration::from_millis](millis: u64) -> std::time::Duration;

/*
const REQUEST_LATENCY_DEFAULT: std::time::Duration = std::time::Duration::from_millis(1000);
const REQUEST_STDDEV_DEFAULT: std::time::Duration = std::time::Duration::from_millis(2000);
*/
const REQUEST_LATENCY_DEFAULT_MS: u64 = 1000;
const REQUEST_STDDEV_DEFAULT_MS: u64 = 2000;

#[verifier::external_type_specification]
struct ExArgs(Args);

#[verifier::external_body]
fn report_quorum_size(quorum_size: usize) {
    println!("quorum size: {quorum_size}");
}

#[verifier::external_body]
fn report_read(client_id: u64, r: (Option<u64>, Timestamp)) {
    eprintln!(
        "client {client_id:3} read finished: {:20}",
        format!("{r:?}")
    );
}

#[verifier::external_body]
fn report_err<E: std::error::Error>(client_id: u64, e: &E) {
    eprintln!("client {client_id:3} failed: {e:20?}");
}

#[verifier::external_body]
fn report_write(client_id: u64, val: Option<u64>) {
    eprintln!(
        "client {client_id:3} write finished: {:20}",
        format!("{val:?}")
    );
}


fn connect<C, Conn>(
    args: &Args,
    connector: &Conn,
    client_id: u64,
) -> Result<BufChannel<C>, ConnectError>
where
    Conn: Connector<C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
{
    let mut channel = connector.connect(client_id)?;
    if !args.no_delay {
        channel.add_latency(std::time::Duration::from_millis(REQUEST_LATENCY_DEFAULT_MS), std::time::Duration::from_millis(REQUEST_STDDEV_DEFAULT_MS));
    }
    Ok(BufChannel::new(channel))
}

fn connect_all<C, Conn>(
    args: &Args,
    connectors: &[Conn],
    client_id: u64,
) -> Result<Vec<BufChannel<C>>, ConnectError>
where
    Conn: Connector<C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
{
    let mut v = Vec::with_capacity(connectors.len());
    for connector in connectors.iter() {
        let conn = connect(args, connector, client_id)?;
        v.push(conn)
    }

    Ok(v)
}

#[derive(Debug)]
enum Operation {
    Read(Option<u64>),
    Write(Option<u64>),
}

struct Event {
    event_id: u64,
    begin_ms: u64,
    end_ms: u64,
    op: Operation,
}


type Trace = Vec<Event>;

/*
fn run_client<C, Conn>(args: Args, connectors: &[Conn]) -> Result<Trace, Error>
where
    Conn: Connector<C> + Send + Sync,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    C: Sync + Send,
{
    let mut n_reads = args.n_reads.saturating_sub(1);
    let mut n_writes = args.n_writes;
    let unconnected_clients = Arc::new((Mutex::new(n_reads + n_writes), Condvar::new()));
    let trace = Arc::new(Mutex::new(Vec::new()));
    let total_begin = std::time::Instant::now();

    let client_fn = |id: u64, cv: Arc<(Mutex<u64>, Condvar)>| {
        let pool = connect_all(&args, connectors, id)?;
        let (client, view) = AbdPool::new(FlawlessPool::new(pool, id));
        println!("quorum size: {}", client.quorum_size());

        let (lock, var) = &*cv;
        let mut unconnected = lock.lock().unwrap();
        *unconnected = unconnected.saturating_sub(1);

        while *unconnected > 0 {
            unconnected = var.wait(unconnected).unwrap();
        }

        var.notify_all();

        Ok::<_, Error>(client)
    };

    std::thread::scope(|s| {
        let mut handles = Vec::new();

        let mut idx = 0;
        while n_writes > 0 {
            let cv = unconnected_clients.clone();
            let t = trace.clone();
            handles.push(s.spawn(move || {
                let client = client_fn(idx, cv)?;

                if !args.no_delay {
                    std::thread::sleep((REQUEST_LATENCY_DEFAULT * (2 * idx as u32)) / 1);
                }
                let begin = std::time::Instant::now();
                client.write(Some(idx))?;
                let end = std::time::Instant::now();
                eprintln!(
                    "client {idx:3} finished: {:20} completed | begin = {:15} | end = {:15}",
                    format!("write({idx:2})"),
                    (begin - total_begin).as_nanos(),
                    (end - total_begin).as_nanos(),
                );
                t.lock().unwrap().push(Event {
                    event_id: idx,
                    begin,
                    end,
                    op: Operation::Write(Some(idx)),
                });
                Ok::<_, Error>(())
            }));
            n_writes -= 1;
            idx += 1;
        }
        while n_reads > 0 {
            let cv = unconnected_clients.clone();
            let t = trace.clone();

            handles.push(s.spawn(move || {
                let client = client_fn(idx, cv)?;
                if !args.no_delay {
                    std::thread::sleep((REQUEST_LATENCY_DEFAULT * (2 * idx as u32)) / 1);
                }

                let begin = std::time::Instant::now();
                let res = client.read()?;
                let end = std::time::Instant::now();
                eprintln!(
                    "client {idx:3} finished: {:20} completed | begin = {:15} | end = {:15}",
                    format!("{res:?}"),
                    (begin - total_begin).as_nanos(),
                    (end - total_begin).as_nanos(),
                );
                t.lock().unwrap().push(Event {
                    event_id: idx,
                    begin,
                    end,
                    op: Operation::Read(res.0),
                });
                Ok::<_, Error>(())
            }));
            n_reads -= 1;
            idx += 1;
        }

        for handle in handles {
            match handle.join() {
                Ok(r) => r?,
                Err(e) => {
                    tracing::warn!("failed to join thread: {e:?}");
                }
            }
        }

        let client = client_fn(idx, unconnected_clients)?;
        let begin = std::time::Instant::now();
        let res = client.read()?;
        let end = std::time::Instant::now();
        eprintln!(
            "client {idx:3} finished: {:20} completed | begin = {:15} | end = {:15}",
            format!("{res:?}"),
            (begin - total_begin).as_nanos(),
            (end - total_begin).as_nanos(),
        );
        trace.lock().unwrap().push(Event {
            event_id: idx,
            begin,
            end,
            op: Operation::Read(res.0),
        });

        Ok::<_, Error>(())
    })?;

    Ok(Arc::into_inner(trace).unwrap().into_inner().unwrap())
}
*/


fn run_client<C, Conn>(args: Args, connectors: &[Conn]) -> Result<Trace, Error>
where
    Conn: Connector<C> + Send + Sync,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    C: Sync + Send,
{
    let pool = connect_all(&args, connectors, 0)?;
    let (mut client, view) = AbdPool::<_, _, WritePerm>::new(FlawlessPool::new(pool, 0));
    let tracked view = view.get();
    report_quorum_size(client.quorum_size());

    let tracked read_perm = ReadPerm { register: &view };
    assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    match client.read::<ReadPerm>(Tracked(read_perm)) {
        Ok((v, ts, _comp)) => {
            report_read(0, (v, ts));
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        }
    };

    let tracked write_perm = WritePerm { register: view, val: Some(42u64) };
    let view = match client.write(Some(42), Tracked(write_perm)) {
        Ok(comp) => {
            report_write(0, Some(42));
            comp
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        }
    };
    let tracked view = view.get();
    assert(view@@ == Some(42u64));

    let tracked read_perm = ReadPerm { register: &view };
    assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    match client.read::<ReadPerm>(Tracked(read_perm)) {
        Ok((v, ts, _comp)) => {
            report_read(0, (v, ts));
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        }
    };

    Ok(Trace::new())
}

}

struct PartialOrder(HashMap<(u64, u64), bool>);
impl std::ops::Deref for PartialOrder {
    type Target = HashMap<(u64, u64), bool>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
struct ConcisePartialOrder(HashMap<u64, BTreeSet<u64>>);
impl std::ops::Deref for ConcisePartialOrder {
    type Target = HashMap<u64, BTreeSet<u64>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<&PartialOrder> for ConcisePartialOrder {
    fn from(value: &PartialOrder) -> Self {
        let mut lt_order: HashMap<u64, BTreeSet<u64>> = HashMap::new();
        for ((k, v), lt) in &**value {
            if *lt {
                lt_order.entry(*k).or_default().insert(*v);
            }
        }

        // remove transitives
        loop {
            let mut removed = false;

            let mut removals = vec![];
            for (k, greaters) in &lt_order {
                let rem: Vec<_> = greaters
                    .iter()
                    .filter(|a| {
                        greaters
                            .iter()
                            .any(|b| lt_order.get(b).map(|v| v.contains(a)).unwrap_or(false))
                    })
                    .copied()
                    .collect();

                if !rem.is_empty() {
                    removals.push((*k, rem));
                    removed = true;
                }
            }

            for (k, rems) in removals {
                for r in rems {
                    lt_order.entry(k).and_modify(|x| {
                        x.remove(&r);
                    });
                }
            }

            if !removed {
                break;
            }
        }

        ConcisePartialOrder(lt_order)
    }
}

impl std::fmt::Debug for ConcisePartialOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in &**self {
            writeln!(f, "{k:3} < {v:3?}")?;
        }

        Ok(())
    }
}

impl std::fmt::Debug for PartialOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let concise: ConcisePartialOrder = self.into();
        concise.fmt(f)
    }
}

fn realtime(trace: &[Event]) -> PartialOrder {
    let mut order = HashMap::new();
    for op1 in trace {
        assert!(op1.begin_ms < op1.end_ms, "invalid event");
        for op2 in trace {
            if op1.end_ms < op2.begin_ms {
                order.insert((op1.event_id, op2.event_id), true);
            } else if op2.end_ms < op1.begin_ms {
                order.insert((op1.event_id, op2.event_id), false);
            }
        }
    }

    PartialOrder(order)
}

fn partial(trace: &[Event]) -> PartialOrder {
    let mut order = HashMap::new();

    for op1 in trace {
        assert!(op1.begin_ms < op1.end_ms, "invalid event");
        for op2 in trace {
            if let (Operation::Read(read_v), Operation::Write(write_v)) = (&op1.op, &op2.op) {
                if read_v == write_v {
                    order.insert((op1.event_id, op2.event_id), false);
                    order.insert((op2.event_id, op1.event_id), true);
                }
            }
        }
    }

    PartialOrder(order)
}

fn orders_agree(o1: &PartialOrder, o2: &PartialOrder) -> bool {
    for (k, lt1) in &**o1 {
        if o2.get(k) == Some(&!lt1) {
            return false;
        }
    }

    for (k, lt2) in &**o2 {
        if o1.get(k) == Some(&!lt2) {
            return false;
        }
    }

    true
}

fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    let connectors: Vec<_> = (0..args.n_servers).map(run_modelled_server).collect();

    let trace = run_client(args, &connectors)?;

    let realtime_order = realtime(&trace);
    println!("realtime ordering:\n{realtime_order:?}");
    let part_order = partial(&trace);
    println!("implied partial ordering:\n{part_order:?}");

    if orders_agree(&realtime_order, &part_order) {
        println!("partial orderings agree");
    } else {
        println!("partial orderings do not agree");
    }

    Ok(())
}
