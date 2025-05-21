use std::collections::HashMap;
use std::collections::HashSet;
use std::ops::Deref;

use crate::abd::error;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;
use crate::network::broadcast_pool::BroadcastPool;
use crate::network::connection_pool::ConnectionPool;
use crate::network::Channel;
use crate::proto::Tagged;

pub trait AbdRegisterClient<C> {
    fn read(&self) -> Result<(Option<u64>, Timestamp), error::Error>;
    fn write(&self, val: Option<u64>) -> Result<(), error::Error>;
}

impl<Pool, C> AbdRegisterClient<C> for Pool
where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
{
    fn read(&self) -> Result<(Option<u64>, Timestamp), error::Error> {
        self.shuffle_faults();
        tracing::info!(client_id = self.id(), "reading: first round");

        let bpool = BroadcastPool::new(self);
        let quorum = bpool
            .broadcast(Request::Get)
            // bellow is error handling and type agreement
            .wait_for(
                |s| s.replies().len() >= s.quorum_size(),
                |r| match r.into_inner() {
                    Response::Get { timestamp, val } => Ok((timestamp, val)),
                    _ => Err(r),
                },
            )
            .map_err(|e| error::Error::FailedFirstQuorum {
                obtained: e.replies().len(),
                required: self.quorum_size(),
            })?;

        // logging
        let received: HashMap<_, _> = quorum
            .replies()
            .iter()
            .map(|(idx, (ts, _val))| (idx, ts))
            .collect();

        tracing::info!(
            client_id = self.id(),
            quorum = ?received,
            quorum_size = self.quorum_size(),
            "reading: received quorum for round one"
        );

        // check early return
        let (max_ts, max_val) = quorum
            .replies()
            .iter()
            .map(|(_idx, (ts, val))| (*ts, *val))
            .max()
            .expect("there should be at least one reply");
        let n_max_ts = quorum
            .replies()
            .iter()
            .filter(|(_idx, (ts, _val))| *ts == max_ts)
            .count();

        if n_max_ts >= self.quorum_size() {
            tracing::info!(client_id = self.id(), "reading: early return");
            return Ok((max_val, max_ts));
        }

        // non-unanimous read: write-back

        tracing::info!(
            client_id = self.id(),
            quorum_size = self.quorum_size(),
            n_max_ts,
            received_replies = received.len(),
            "reading: writing back"
        );

        let bpool = BroadcastPool::new(self);
        let new_quorum: HashSet<_> = bpool
            .broadcast_filter(
                Request::Write {
                    val: max_val,
                    timestamp: max_ts,
                },
                // writeback to replicas that did not have the maximum timestamp
                |idx| {
                    quorum
                        .replies()
                        .iter()
                        .filter(|(_idx, (ts, _val))| *ts != max_ts)
                        .any(|(nidx, _)| *nidx == idx)
                },
            )
            // bellow is error handling + type handling + logging stuff
            .wait_for(
                |s| s.replies().len() + n_max_ts >= s.quorum_size(),
                |r| match r.deref() {
                    Response::Write => Ok(()),
                    _ => Err(r),
                },
            )
            .map_err(|e| error::Error::FailedSecondQuorum {
                obtained: e.replies().len() + n_max_ts,
                required: self.quorum_size(),
            })?
            .into_replies()
            .map(|(idx, _)| idx)
            .collect();

        tracing::info!(
            client_id = self.id(),
            min_quorum_size = self.quorum_size(),
            quorum = ?new_quorum,
            "writing: received replies for write phase"
        );

        Ok((max_val, max_ts))
    }

    fn write(&self, val: Option<u64>) -> Result<(), error::Error> {
        self.shuffle_faults();
        tracing::info!(client_id = self.id(), ?val, "writing: read timestamp phase");

        let max_ts = {
            let bpool = BroadcastPool::new(self);

            let quorum = bpool
                .broadcast(Request::GetTimestamp)
                // bellow is error handling and type agreement
                .wait_for(
                    |s| s.replies().len() >= s.quorum_size(),
                    |r| match r.deref() {
                        Response::GetTimestamp { timestamp } => Ok(*timestamp),
                        _ => Err(r),
                    },
                )
                .map_err(|e| error::Error::FailedFirstQuorum {
                    obtained: e.replies().len(),
                    required: self.quorum_size(),
                })?;

            let max_ts = quorum
                .replies()
                .iter()
                .map(|(_idx, ts)| *ts)
                .max()
                .expect("the quorum should never be empty");

            // logging
            let quorum: HashMap<_, _> = quorum.into_replies().collect();

            tracing::info!(
                client_id = self.id(),
                quorum_size = self.quorum_size(),
                ?quorum,
                ?max_ts,
                "writing: received quorum for read phase, going into writing"
            );

            Ok(max_ts)
        }?;

        {
            let bpool = BroadcastPool::new(self);
            let quorum: HashSet<_> = bpool
                .broadcast(Request::Write {
                    val,
                    timestamp: Timestamp {
                        seqno: max_ts.seqno + 1,
                        client_id: self.id(),
                    },
                })
                // bellow is error handling + type handling + logging stuff
                .wait_for(
                    |s| s.replies().len() >= s.quorum_size(),
                    |r| match r.deref() {
                        Response::Write => Ok(()),
                        _ => Err(r),
                    },
                )
                .map_err(|e| error::Error::FailedSecondQuorum {
                    obtained: e.replies().len(),
                    required: self.quorum_size(),
                })?
                .into_replies()
                .map(|(idx, _)| idx)
                .collect();

            tracing::info!(
                client_id = self.id(),
                min_quorum_size = self.quorum_size(),
                ?quorum,
                "writing: received quorum for write phase"
            );
            Ok(())
        }
    }
}
