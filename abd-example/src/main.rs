use clap::Parser;
use vstd::atomic::PAtomicU64;
use vstd::prelude::*;
use vstd::resource::ghost_var::GhostVar;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
#[cfg(verus_only)]
use verdist::pool::ConnectionPool;
use verdist::pool::FlawlessPool;

use abd::channel::ChannelInv;
use abd::client::AbdPool;
use abd::client::AbdRegisterClient;
use abd::invariants::logatom::ReadPerm;
use abd::invariants::logatom::WritePerm;
use abd::server::run_modelled_server;

mod cli;
mod error;
mod invariant;
mod print;
mod trace;

use cli::Args;
use error::Error;
use invariant::get_invariant_state;
use print::*;

verus! {

pub assume_specification[ std::time::Duration::from_millis ](millis: u64) -> std::time::Duration
;

const REQUEST_LATENCY_DEFAULT_MS: u64 = 1000;

const REQUEST_STDDEV_DEFAULT_MS: u64 = 2000;

fn connect<C, Conn>(args: &Args, connector: &Conn, client_id: u64) -> Result<
    BufChannel<C>,
    ConnectError,
> where
    Conn: Connector<C>,
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,
 {
    let mut channel = connector.connect(
        client_id,
        |_connector, _client_id| Ghost(ChannelInv {  }),
    )?;
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
    C: Channel<Id = (u64, u64), K = ChannelInv, R = abd::proto::Response, S = abd::proto::Request>,

    ensures
        r is Ok ==> {
            let v = r->Ok_0;
            &&& connectors.len() == v.len()
            &&& forall|idx| 0 <= idx < v@.len() ==> #[trigger] v@[idx].spec_id().0 == client_id
            &&& forall|i, j|
                0 <= i < j < v@.len() ==> #[trigger] v@[i].spec_id() != #[trigger] v@[j].spec_id()
        },
{
    let mut v = Vec::with_capacity(connectors.len());
    for connector in connectors.iter() {
        let conn = connect(args, connector, client_id)?;
        v.push(conn);
    }

    proof {
        admit();  // XXX(assume): this is trivial but seems like something should be able to get
    }
    Ok(v)
}

fn run_client<C, Conn, 'a>(args: Args, connectors: &[Conn]) -> Result<
    (),
    Error<WritePerm, GhostVar<Option<u64>>, ReadPerm<'a>, &'a GhostVar<Option<u64>>>,
> where
    Conn: Connector<C> + Send + Sync,
    C: Channel<
        K = abd::channel::ChannelInv,
        R = abd::proto::Response,
        S = abd::proto::Request,
        Id = (u64, u64),
    >,
    C: Sync + Send,

    requires
        connectors.len() > 0,
{
    let pool = connect_all(&args, connectors, args.client_id)?;
    let pool = FlawlessPool::new(pool);
    assert(pool.spec_len() == connectors.len());

    let (client_ctr, client_ctr_perm) = PAtomicU64::new(0);
    let (request_ctr, request_ctr_perm) = PAtomicU64::new(0);

    #[allow(unused)]
    let (client_ctr_token, request_ctr_token, state_inv, view) = get_invariant_state::<
        _,
        _,
        WritePerm,
        ReadPerm<'_>,
    >(&pool, args.client_id, client_ctr_perm, request_ctr_perm);
    let mut client = AbdPool::<_, WritePerm, ReadPerm<'_>>::new(
        pool,
        args.client_id,
        client_ctr,
        client_ctr_token,
        request_ctr,
        request_ctr_token,
        state_inv,
    );
    assert(client.inv()) by { abd::client::lemma_inv(client) };
    let tracked view = view.get();
    report_quorum_size(client.quorum_size());

    let tracked read_perm = ReadPerm { register: &view };
    assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    match client.read(Tracked(read_perm)) {
        Ok((v, ts, _comp)) => {
            report_read(0, (v, ts));
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        },
    };

    let tracked write_perm = WritePerm { register: view, val: Some(42u64) };
    #[allow(unused_variables)]
    let view = match client.write(Some(42), Tracked(write_perm)) {
        Ok(comp) => {
            report_write(0, Some(42));
            comp
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        },
    };
    let tracked view = view.get();
    assert(view@@ == Some(42u64));

    let tracked read_perm = ReadPerm { register: &view };
    assume(read_perm.pre(RegisterRead { id: Ghost(client.register_loc()) }));
    match client.read(Tracked(read_perm)) {
        Ok((v, ts, _comp)) => {
            report_read(0, (v, ts));
        },
        Err(e) => {
            report_err(0, &e);
            return Err(e)?;
        },
    };

    Ok(())
}

} // verus!
fn main() {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    if args.n_servers == 0 {
        eprintln!("need at least one server");
        return;
    }

    let connectors: Vec<_> = (0..args.n_servers).map(run_modelled_server).collect();

    run_client(args, &connectors).expect("error");

    // let realtime_order = realtime(&trace);
    // println!("realtime ordering:\n{realtime_order:?}");
    // let part_order = partial(&trace);
    // println!("implied partial ordering:\n{part_order:?}");

    // if orders_agree(&realtime_order, &part_order) {
    // println!("partial orderings agree");
    // } else {
    // println!("partial orderings do not agree");
    // }
}
