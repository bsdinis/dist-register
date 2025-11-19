use clap::Parser;

use std::collections::BTreeSet;
use std::collections::HashMap;

mod abd;
mod verdist;

use abd::client::AbdPool;
use abd::client::AbdRegisterClient;
use abd::invariants;
use abd::invariants::logatom::ReadPerm;
#[allow(unused_imports)]
use abd::invariants::logatom::RegisterRead;
use abd::invariants::logatom::RegisterWrite;
use abd::invariants::logatom::WritePerm;
use abd::invariants::ClientToken;
use abd::invariants::RegisterView;
use abd::invariants::StateInvariant;
use abd::proto::Timestamp;
use abd::server::run_modelled_server;
use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
use verdist::pool::connection_pool::lemma_pool_len;
use verdist::pool::ConnectionPool;
use verdist::pool::FlawlessPool;
use verdist::rpc::proto::Tagged;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;

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

impl<ML, RL> From<ConnectError> for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl<ML, RL> From<abd::client::error::ReadError<RL, RL::Completion>>
    for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: abd::client::error::ReadError<RL, RL::Completion>) -> Self {
        Error::AbdRead(value)
    }
}

impl<ML, RL> From<abd::client::error::WriteError<ML, ML::Completion>>
    for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn from(value: abd::client::error::WriteError<ML, ML::Completion>) -> Self {
        Error::AbdWrite(value)
    }
}

impl<ML, RL> std::error::Error for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match self {
            Error::Connection(e) => Some(e),
            Error::AbdRead(e) => Some(e),
            Error::AbdWrite(e) => Some(e),
        }
    }
}

impl<ML, RL> std::fmt::Display for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
        }
    }
}

impl<ML, RL> std::fmt::Debug for Error<ML, ML::Completion, RL, RL::Completion>
where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::AbdRead(e) => e.fmt(f),
            Error::AbdWrite(e) => e.fmt(f),
        }
    }
}

verus! {

enum Error<ML, MC, RL, RC> {
    Connection(ConnectError),
    AbdRead(abd::client::error::ReadError<RL, RC>),
    AbdWrite(abd::client::error::WriteError<ML, MC>),
}

#[verifier::external_trait_specification]
pub trait ExError: std::fmt::Debug + std::fmt::Display {
    type ExternalTraitSpecificationFor: std::error::Error;
}

pub assume_specification[ std::time::Duration::from_millis ](millis: u64) -> std::time::Duration
;

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

fn connect<C, Conn>(args: &Args, connector: &Conn, client_id: u64) -> Result<
    BufChannel<C>,
    ConnectError,
> where
    Conn: Connector<C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
 {
    let mut channel = connector.connect(client_id)?;
    if !args.no_delay {
        channel.add_latency(
            std::time::Duration::from_millis(REQUEST_LATENCY_DEFAULT_MS),
            std::time::Duration::from_millis(REQUEST_STDDEV_DEFAULT_MS),
        );
    }
    Ok(BufChannel::new(channel))
}

fn connect_all<C, Conn>(args: &Args, connectors: &[Conn], client_id: u64) -> (r: Result<
    Vec<BufChannel<C>>,
    ConnectError,
>) where
    Conn: Connector<C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,

    ensures
        r is Ok ==> connectors.len() == r->Ok_0.len(),
{
    let mut v = Vec::with_capacity(connectors.len());
    for connector in connectors.iter() {
        let conn = connect(args, connector, client_id)?;
        v.push(conn)
    }

    // XXX(assume): this is trivial but seems like something should be able to get
    assume(v.len() == connectors.len());
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
    use std::sync::Arc;
    use std::sync::Condvar;
    use std::sync::Mutex;

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

fn get_invariant_state<Pool, C, ML, RL>(pool: &Pool) -> (r: (
    Tracked<ClientToken>,
    Tracked<StateInvariant<ML, RL, ML::Completion, RL::Completion>>,
    Tracked<RegisterView>,
)) where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    ensures
        r.0@@ == pool.pool_id(),
        r.1@.constant().client_token_auth_id == r.0@.id(),
        r.1@.namespace() == invariants::state_inv_id(),
{
    let tracked state_inv;
    let tracked view;
    proof {
        let tracked (s, v) = invariants::get_system_state::<ML, RL>();
        state_inv = s;
        view = v;
    }
    // XXX: we could derive this with a sign-in procedure to create ids
    let tracked client_token;
    vstd::open_atomic_invariant!(&state_inv => state => {
        proof {
            assume(!state.client_token_auth@.contains(pool.pool_id()));
            client_token = state.client_token_auth.insert(pool.pool_id());
        }
    });

    (Tracked(client_token), Tracked(state_inv), Tracked(view))
}

fn run_client<C, Conn>(args: Args, connectors: &[Conn]) -> Result<
    Trace,
    Error<WritePerm, GhostVar<Option<u64>>, ReadPerm, &'_ GhostVar<Option<u64>>>,
> where
    Conn: Connector<C> + Send + Sync,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    C: Sync + Send,

    requires
        connectors.len() > 0,
{
    let pool = connect_all(&args, connectors, 0)?;
    let pool = FlawlessPool::new(pool, 0);
    assert(pool.n() == connectors.len()) by {
        lemma_pool_len(pool);
    }

    let (client_token, state_inv, view) = get_invariant_state::<_, _, WritePerm, ReadPerm<'_>>(
        &pool,
    );
    let mut client = AbdPool::<
        _,
        WritePerm,
        ReadPerm<'_>,
        GhostVar<Option<u64>>,
        &'_ GhostVar<Option<u64>>,
    >::new(pool, client_token, state_inv);
    assert(client.inv()) by { abd::client::lemma_inv(client) };
    assert(client.weak_inv()) by { client.lemma_weak_inv() };
    let tracked view = view.get();
    report_quorum_size(client.quorum_size());

    // let tracked read_perm = ReadPerm { register: &view };
    // assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    // match client.read(Tracked(read_perm)) {
    //     Ok((v, ts, _comp)) => {
    //         report_read(0, (v, ts));
    //     },
    //     Err(e) => {
    //         report_err(0, &e);
    //         return Err(e)?;
    //     }
    // };
    //
    // let tracked write_perm = WritePerm { register: view, val: Some(42u64) };
    // let view = match client.write(Some(42), Tracked(write_perm)) {
    //     Ok(comp) => {
    //         report_write(0, Some(42));
    //         comp
    //     },
    //     Err(e) => {
    //         report_err(0, &e);
    //         return Err(e)?;
    //     }
    // };
    // let tracked view = view.get();
    // assert(view@@ == Some(42u64));
    //
    // let tracked read_perm = ReadPerm { register: &view };
    // assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    // match client.read(Tracked(read_perm)) {
    //     Ok((v, ts, _comp)) => {
    //         report_read(0, (v, ts));
    //     },
    //     Err(e) => {
    //         report_err(0, &e);
    //         return Err(e)?;
    //     }
    // };

    Ok(Trace::new())
}

} // verus!
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

fn main() {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    if args.n_servers == 0 {
        eprintln!("need at least one server");
        return;
    }

    let connectors: Vec<_> = (0..args.n_servers).map(run_modelled_server).collect();

    let trace = run_client(args, &connectors).expect("error");

    let realtime_order = realtime(&trace);
    println!("realtime ordering:\n{realtime_order:?}");
    let part_order = partial(&trace);
    println!("implied partial ordering:\n{part_order:?}");

    if orders_agree(&realtime_order, &part_order) {
        println!("partial orderings agree");
    } else {
        println!("partial orderings do not agree");
    }
}
