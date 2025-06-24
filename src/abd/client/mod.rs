use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::BroadcastPool;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::proto::Tagged;
use crate::verdist::request::Replies;

pub mod error;
mod utils;

use utils::*;

#[allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

verus! {

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
        let bpool = BroadcastPool::new(self);
        let quorum = bpool
            .broadcast(Request::Get)
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

        // check early return
        let replies = quorum.replies();
        assume(replies.len() > 0);
        let opt = max_from_get_replies(replies);
        assert(opt is Some);
        let (max_ts, max_val) = opt.expect("there should be at least one reply");
        let mut n_max_ts = 0usize;
        let q_iter = quorum.replies().iter();
        for (_idx, (ts, _val)) in q_iter {
            if ts.seqno == max_ts.seqno && ts.client_id == max_ts.client_id {
                assume(n_max_ts + 1 < usize::MAX);
                n_max_ts += 1;
            }
        }

        if n_max_ts >= self.quorum_size() {
            return Ok((max_val, max_ts));
        }

        // non-unanimous read: write-back
        let bpool = BroadcastPool::new(self);
        #[allow(unused_parens)]
        let result = bpool
            .broadcast_filter(
                Request::Write {
                    val: max_val,
                    timestamp: max_ts,
                },
                // writeback to replicas that did not have the maximum timestamp
                |idx| {
                    let q_iter = quorum.replies().iter();
                    for (nidx, (ts, _val)) in q_iter {
                        if idx == *nidx && (ts.seqno != max_ts.seqno || ts.client_id != max_ts.client_id) {
                            return true;
                        }
                    }

                    false
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
        assume(result.is_err() ==> err_mapper.requires((result->Err_0,)));
        result.map_err(err_mapper)?;

        Ok((max_val, max_ts))
    }

    fn write(&self, val: Option<u64>) -> Result<(), error::Error> {
        let max_ts = {
            let bpool = BroadcastPool::new(self);

            let quorum = bpool
                .broadcast(Request::GetTimestamp)
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

            let replies = quorum.replies();
            assume(replies.len() > 0);
            let max_ts = max_from_get_ts_replies(replies);
            assert(max_ts is Some);
            let max_ts = max_ts.expect("the quorum should never be empty");

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

            Ok(())
        }
    }
}

}
