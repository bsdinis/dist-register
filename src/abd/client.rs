use crate::abd::error;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;
use crate::network::broadcast_pool::BroadcastPool;
use crate::network::connection_pool::ConnectionPool;
use crate::network::replies::Replies;
use crate::network::Channel;
use crate::proto::Tagged;

use builtin::*;
use vstd::prelude::*;

verus! {

fn max_from_replies(v: Vec<(Timestamp, Option<u64>)>) -> Option<(Timestamp, Option<u64>)> {
    let mut max_ts = Timestamp::default();
    let vals = v.as_slice();
    let mut max_idx = vals.len();
    for idx in 0..(vals.len()) {
        if vals[idx].0.seqno > max_ts.seqno ||
            (
        vals[idx].0.seqno == max_ts.seqno &&
        vals[idx].0.client_id > max_ts.client_id
            )
        {
            max_ts = vals[idx].0;
            max_idx = idx;
        }
    }

    if max_idx < vals.len() {
        Some(vals[max_idx])
    } else {
        None
    }
}

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
        // tracing::info!(client_id = self.id(), "reading: first round");

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
        /*
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
        */


        // check early return
        let mut replies = Vec::new();
        let iter = quorum.replies().iter();
        for reply in iter {
            replies.push(reply.1);
        }
        /*
        let replies = quorum
            .replies()
            .iter()
            // .map(|(_idx, (ts, val))| (*ts, *val))
            .map(|tup| tup.1)
            .collect();
        */

        let opt = max_from_replies(replies);
        assume(opt.is_Some());
        let (max_ts, max_val) = opt.expect("there should be at least one reply");
        let mut n_max_ts = 0usize;
        let q_iter = quorum.replies().iter();
        for (_idx, (ts, _val)) in q_iter {
            if ts.seqno == max_ts.seqno && ts.client_id == max_ts.client_id {
                assume(n_max_ts + 1 < usize::MAX);
                n_max_ts = n_max_ts + 1;
            }
        }
        /*
        let n_max_ts = quorum
            .replies()
            .iter()
            //.filter(|(_idx, (ts, _val))| *ts == max_ts)
            .filter(|tup| {
                let ts = tup.1.0;
                ts.seqno == max_ts.seqno &&
                ts.client_id == max_ts.client_id
            })
            .count();
        */

        if n_max_ts >= self.quorum_size() {
            // tracing::info!(client_id = self.id(), "reading: early return");
            return Ok((max_val, max_ts));
        }

        // non-unanimous read: write-back

        /*
        tracing::info!(
            client_id = self.id(),
            quorum_size = self.quorum_size(),
            n_max_ts,
            received_replies = received.len(),
            "reading: writing back"
        );
        */

        let bpool = BroadcastPool::new(self);
        let result = bpool
            .broadcast_filter(
                Request::Write {
                    val: max_val,
                    timestamp: max_ts,
                },
                // writeback to replicas that did not have the maximum timestamp
                |idx| {
                    let mut did_not_have_max_ts = false;
                    let q_iter = quorum.replies().iter();
                    for (nidx, (ts, _val)) in q_iter {
                        if idx == *nidx && (ts.seqno != max_ts.seqno || ts.client_id != max_ts.client_id) {
                            did_not_have_max_ts = true;
                        }
                    }

                    did_not_have_max_ts

                        /*
                    quorum
                        .replies()
                        .iter()
                        //.filter(|(_idx, (ts, _val))| *ts != max_ts)
                        .filter(|tup| {
                            let ts = tup.1.0;
                            ts.seqno != max_ts.seqno ||
                            ts.client_id != max_ts.client_id
                        })
                        //.any(|(nidx, _)| *nidx == idx)
                        .any(|tup| tup.0 == idx)
                        */
                },
            )
            // bellow is error handling + type handling + logging stuff
            .wait_for(
                (|s|
                 requires s.replies.len() + n_max_ts < usize::MAX,
                {
                    s.replies.len() + n_max_ts >= s.quorum_size()
                }),
                |r| match r.deref() {
                    Response::Write => Ok(()),
                    _ => Err(r),
                },
            );


        let err_mapper = |e: Replies<_, _>|
                 requires e.replies.len() + n_max_ts < usize::MAX,
                    {
                error::Error::FailedSecondQuorum {
                obtained: e.replies.len() + n_max_ts,
                required: self.quorum_size(),
            }
        };
        assume(result.is_err() ==> err_mapper.requires((result.get_Err_0(),)));
        result.map_err(err_mapper)?;
            // .into_iter().map(|(idx, _)| idx).collect();

        /*
        tracing::info!(
            client_id = self.id(),
            min_quorum_size = self.quorum_size(),
            quorum = ?new_quorum,
            "writing: received replies for write phase"
        );
        */

        Ok((max_val, max_ts))
    }

    fn write(&self, val: Option<u64>) -> Result<(), error::Error> {
        self.shuffle_faults();
        // tracing::info!(client_id = self.id(), ?val, "writing: read timestamp phase");

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

            let mut max_ts = None;
            let q_iter = quorum.replies().iter();
            for (_idx, ts) in q_iter {
                max_ts = match max_ts {
                    Some(Timestamp { seqno, client_id }) => {
                        if seqno < ts.seqno || (seqno == ts.seqno && client_id < ts.client_id) {
                            Some(*ts)
                        } else {
                            max_ts
                        }
                    },
                    None => Some(*ts)
                }
            }
            assume(max_ts.is_Some());
            let max_ts = max_ts.expect("the quorum should never be empty");

            /*
                let max_ts = quorum.replies().iter()
                //.map(|(_idx, ts)| *ts)
                .map(|tup| tup.1)
                .max()
                .expect("the quorum should never be empty");
            */

            // logging
            // let quorum: HashMap<_, _> = quorum.into_replies().collect();

            /*
            tracing::info!(
                client_id = self.id(),
                quorum_size = self.quorum_size(),
                ?quorum,
                ?max_ts,
                "writing: received quorum for read phase, going into writing"
            );
            */

            Ok(max_ts)
        }?;

        {
            assume(max_ts.seqno + 1 < u64::MAX);
            let bpool = BroadcastPool::new(self);
            let _quorum = bpool
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
                })?;

            /*
            let quorum_logging = quorum.into_replies()
                .map(|(idx, _)| idx)
                .collect();

            tracing::info!(
                client_id = self.id(),
                min_quorum_size = self.quorum_size(),
                quorum = ?quorum_logging,
                "writing: received quorum for write phase"
            );
            */
            Ok(())
        }
    }
}

}
