#[cfg(false)]
mod ignore {
    fn run_client<C, Conn>(args: Args, connectors: &[Conn]) -> Result<Trace, Error>
    where
        Conn: Connector<C> + Send + Sync,
        C: Channel<R = abd::proto::Response, S = abd::proto::Request>,
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
}
