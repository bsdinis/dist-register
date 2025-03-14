use clap::Parser;

use std::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;

mod abd;
mod network;
mod proto;

use abd::client::AbdRegisterClient;
use abd::server::run_modelled_server;
use network::BufChannel;
use network::Channel;
use network::ChannelExt;
use network::Connector;
use network::connection_pool::FlawlessPool;
use network::connection_pool::LossyPool;
use network::error::ConnectError;
use proto::Tagged;

const REQUEST_LATENCY_DEFAULT: std::time::Duration = std::time::Duration::from_millis(1000);
const REQUEST_STDDEV_DEFAULT: std::time::Duration = std::time::Duration::from_millis(2000);

#[derive(clap::ValueEnum, Clone, Default, Debug)]
enum Mode {
    #[default]
    Flawless,
    Lossy,
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self, f)
    }
}

#[derive(Parser)]
#[command(author, version, about, long_about=None)]
struct Args {
    #[arg(short, long, default_value = "flawless")]
    mode: Mode,

    #[arg(short, long)]
    faults: Option<u64>,

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

#[derive(Debug)]
enum Error {
    Connection(ConnectError),
    Abd(abd::error::Error),
}

impl From<ConnectError> for Error {
    fn from(value: ConnectError) -> Self {
        Error::Connection(value)
    }
}

impl From<abd::error::Error> for Error {
    fn from(value: abd::error::Error) -> Self {
        Error::Abd(value)
    }
}

impl std::error::Error for Error {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match self {
            Error::Connection(e) => Some(e),
            Error::Abd(e) => Some(e),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Connection(e) => e.fmt(f),
            Error::Abd(e) => e.fmt(f),
        }
    }
}

fn connect<C, Conn>(
    args: &Args,
    connector: &Conn,
    client_id: u64,
) -> Result<BufChannel<C>, ConnectError>
where
    Conn: Connector<C>,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    C: ChannelExt,
{
    let mut channel = connector.connect(client_id)?;
    if !args.no_delay {
        channel.add_latency(REQUEST_LATENCY_DEFAULT / 2, REQUEST_STDDEV_DEFAULT / 2);
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
    C: ChannelExt,
{
    connectors
        .iter()
        .map(|connector| connect(args, connector, client_id))
        .collect()
}

fn run_client<C, Conn>(args: Args, connectors: &[Conn]) -> Result<(), Error>
where
    Conn: Connector<C> + Send + Sync,
    C: Channel<R = Tagged<abd::proto::Response>, S = Tagged<abd::proto::Request>>,
    C: ChannelExt,
    C: Sync + Send,
{
    let mut n_reads = args.n_reads.saturating_sub(1);
    let mut n_writes = args.n_writes;
    let unconnected_clients = Arc::new((Mutex::new(n_reads + n_writes), Condvar::new()));

    let client_fn = |id: u64, cv: Arc<(Mutex<u64>, Condvar)>| {
        let pool = connect_all(&args, connectors, id)?;
        let client: Arc<dyn AbdRegisterClient<BufChannel<C>> + Sync + Send> = match args.mode {
            Mode::Flawless => Arc::new(FlawlessPool::new(pool, id)),
            Mode::Lossy => {
                let faults = args.faults.unwrap_or((pool.len() as u64 - 1) / 2) as usize;
                Arc::new(LossyPool::new(pool, faults, id))
            }
        };

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
            handles.push(s.spawn(move || {
                let client = client_fn(idx, cv)?;

                if !args.no_delay {
                    std::thread::sleep(REQUEST_LATENCY_DEFAULT / 2);
                }
                client.write(Some(idx))?;
                eprintln!("client {idx} finished: write completed");
                Ok::<_, Error>(())
            }));
            n_writes -= 1;
            idx += 1;
        }
        while n_reads > 0 {
            let cv = unconnected_clients.clone();

            handles.push(s.spawn(move || {
                let client = client_fn(idx, cv)?;
                if !args.no_delay {
                    std::thread::sleep(REQUEST_LATENCY_DEFAULT / 2);
                }

                let res = client.read()?;
                eprintln!("client {idx} finished: {res:?}");
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
        let res = client.read()?;
        eprintln!("client {idx} finished: {res:?}");

        Ok::<_, Error>(())
    })?;

    Ok(())
}

fn main() -> Result<(), Error> {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    let connectors: Vec<_> = (0..args.n_servers).map(run_modelled_server).collect();

    run_client(args, &connectors)
}
