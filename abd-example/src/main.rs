use clap::Parser;
use vstd::atomic::PAtomicU64;
#[cfg(verus_only)]
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::resource::ghost_var::GhostVar;

use verdist::network::channel::BufChannel;
use verdist::network::channel::Channel;
use verdist::network::channel::Connector;
use verdist::network::error::ConnectError;
#[cfg(verus_only)]
use verdist::pool::ConnectionPool;
use verdist::pool::FlawlessPool;

use specs::abd::AbdRegisterClient;
use specs::abd::ReadPerm;
#[cfg(verus_only)]
use specs::abd::RegisterRead;
#[cfg(verus_only)]
use specs::abd::RegisterWrite;
use specs::abd::WritePerm;

use abd::channel::ChannelInv;
use abd::client::AbdPool;
use abd::server::run_modelled_server;

mod cli;
mod error;
mod invariant;
mod trace;

use cli::Args;
use error::Error;
use invariant::get_invariant_state;

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
        |_connector, _client_id|
            Ghost(
                ChannelInv {
                    commitment_id: arbitrary(),
                    request_map_id: arbitrary(),
                    server_locs: arbitrary(),
                    server_tokens_id: arbitrary(),
                },
            ),
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
    assume(forall|cid| #[trigger]
        pool.spec_channels().dom().contains(cid) ==> {
            let c = pool.spec_channels()[cid];
            &&& cid.0 == args.client_id
            &&& state_inv.constant().server_locs.contains_key(cid.1)
            &&& state_inv.constant().request_map_ids.request_auth_id == c.constant().request_map_id
            &&& state_inv.constant().commitments_ids.commitment_id == c.constant().commitment_id
            &&& state_inv.constant().server_tokens_id == c.constant().server_tokens_id
            &&& state_inv.constant().server_locs == c.constant().server_locs
        });
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

    #[allow(unused)]
    let r_view = view.clone();
    let tracked read_perm = ReadPerm { register: r_view.borrow() };
    #[allow(unused)]
    let (v, ts, comp) = match client.read(Tracked(read_perm)) {
        Ok((v, ts, comp)) => {
            vlib::veprintln!("[client|{:>3}]: read completed: {:?} @ {:?}", args.client_id, v, ts);
            (v, ts, comp)
        },
        Err(e) => {
            vlib::veprintln!("[client|{:>3}]: read error: {}", args.client_id, e);
            return Err(Error::Empty);
        },
    };
    assert(comp@@ == v);

    /*
    #[allow(unused)]
    let w_view = view.clone();
    let value = Some(42u64);
    let tracked write_perm = WritePerm { register: w_view, value: Some(42u64) };
    #[allow(unused_variables)]
    let new_view = match client.write(Some(42), Tracked(write_perm)) {
        Ok(comp) => {
            vlib::veprintln!("[client|{:>3}]: write completed: {:?}", args.client_id, value);
            comp
        },
        Err(e) => {
            vlib::veprintln!("[client|{:>3}]: write error: {}", args.client_id, e);
            return Err(Error::Empty);
        },
    };
    assert(new_view@@ == Some(42u64));
    */

    #[allow(unused)]
    let r_view = view.clone();
    let tracked read_perm = ReadPerm { register: r_view.borrow() };
    #[allow(unused)]
    let (v, ts, comp) = match client.read(Tracked(read_perm)) {
        Ok((v, ts, comp)) => {
            vlib::veprintln!("[client|{:>3}]: read completed: {:?} @ {:?}", args.client_id, v, ts);
            (v, ts, comp)
        },
        Err(e) => {
            vlib::veprintln!("[client|{:>3}]: read error: {}", args.client_id, e);
            return Err(Error::Empty);
        },
    };
    assert(comp@@ == v);

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
