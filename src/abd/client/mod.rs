use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::BroadcastPool;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::proto::Tagged;
use crate::verdist::rpc::Replies;

pub mod error;
mod history;
pub mod logatom;
mod utils;

use utils::*;

#[allow(unused_imports)]
use builtin::*;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;

use logatom::*;

verus! {

// TODO: write weaker spec of history of values
pub trait AbdRegisterClient<C> {
    spec fn loc(&self) -> int;

    fn read<RL: ReadLinearizer<RegisterRead>>(&self, lin: Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), (error::Error, Tracked<RL>)>)
        requires
            lin@.pre(RegisterRead { id: self.loc() })
        ensures
            r is Ok ==> ({
                let (val, ts, compl) = r->Ok_0;
                lin@.post(RegisterRead { id: self.loc() }, val, compl@)
            }),
            r is Err ==> ({
                r->Err_0.1 == lin
            })
        ;

    // TODO: help -- this should be able to be done with a shared reference: all the mutable
    // accesses are in ghost state, and the register should be able to linearize against a local
    // value.
    fn write<ML: MutLinearizer<RegisterWrite>>(&mut self, val: Option<u64>, lin: Tracked<ML>) -> (r: Result<Tracked<ML::Completion>, (error::Error, Tracked<ML>)>)
        requires
            lin@.pre(RegisterWrite { id: old(self).loc(), new_value: val })
        ensures
            r is Ok ==> ({
                let compl = r->Ok_0;
                lin@.post(RegisterWrite { id: old(self).loc(), new_value: val }, (), compl@)
            }),
            r is Err ==> ({
                r->Err_0.1 == lin
            })
        ;
}

pub struct AbdPool<Pool> {
    pub pool: Pool,
    pub register: Tracked<GhostVarAuth<Option<u64>>>,
}

type RegisterView = Tracked<GhostVar<Option<u64>>>;

impl<Pool, C> AbdPool<Pool>
where
    Pool: ConnectionPool<C = C>,
{
    pub fn new(pool: Pool) -> (Self, RegisterView) {
        // TODO: this is not known (maybe this has to be Option<Option<u64>>?)
        let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
        let register = Tracked(register);
        let view = Tracked(view);
        let pool = AbdPool {
            pool,
            register
        };

        (pool, view)
    }

    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }
}


impl<Pool, C> AbdRegisterClient<C> for AbdPool<Pool>
where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
{
    open spec fn loc(&self) -> int {
        self.register@.id()
    }

    fn read<RL: ReadLinearizer<RegisterRead>>(&self, Tracked(lin): Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), (error::Error, Tracked<RL>)>) {
        let bpool = BroadcastPool::new(&self.pool);
        let quorum_res = bpool
            .broadcast(Request::Get)
            .wait_for(
                |s| s.replies().len() >= s.quorum_size(),
                |r| match r.clone().into_inner() {
                    Response::Get { timestamp, val, .. } => Ok((timestamp, val)),
                    _ => Err(r),
                },
            );

        let quorum = match quorum_res {
            Ok(q) => q,
            Err(e) => {
                return Err((
                    error::Error::FailedFirstQuorum {
                        obtained: e.replies().len(),
                        required: self.pool.quorum_size(),
                    },
                    Tracked(lin)
                ));
            }
        };

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

        if n_max_ts >= self.pool.quorum_size() {
            let comp = Tracked({
                let op = RegisterRead { id: self.loc() };
                lin.apply(op, self.register.borrow(), &max_val)
            });
            return Ok((max_val, max_ts, comp));
        }

        // non-unanimous read: write-back
        let bpool = BroadcastPool::new(&self.pool);
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
                    Response::Write { .. } => Ok(()),
                    _ => Err(r),
                },
            );


        let err_mapper = |e: Replies<_, _>|
                 requires e.replies.len() + n_max_ts < usize::MAX,
                    {
                 error::Error::FailedSecondQuorum {
                obtained: e.replies.len() + n_max_ts,
                required: self.pool.quorum_size(),
                 }
        };
        assume(result.is_err() ==> err_mapper.requires((result->Err_0,)));
        if let Err(e) = result {
            let e = err_mapper(e);
            return Err((e, Tracked(lin)));
        }

        let comp = Tracked({
            let op = RegisterRead { id: self.loc() };
            lin.apply(op, self.register.borrow(), &max_val)
        });
        Ok((max_val, max_ts, comp))
    }

    fn write<ML: MutLinearizer<RegisterWrite>>(&mut self, val: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<Tracked<ML::Completion>, (error::Error, Tracked<ML>)>) {
        let max_ts = {
            let bpool = BroadcastPool::new(&self.pool);

            let quorum_res = bpool
                .broadcast(Request::GetTimestamp)
                .wait_for(
                    |s| s.replies().len() >= s.quorum_size(),
                    |r| match r.deref() {
                        Response::GetTimestamp { timestamp, .. } => Ok(*timestamp),
                        _ => Err(r),
                    },
                );

            let quorum = match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    return Err((
                        error::Error::FailedFirstQuorum {
                            obtained: e.replies().len(),
                            required: self.pool.quorum_size(),
                        },
                        Tracked(lin)
                    ));
                }
            };

            let replies = quorum.replies();
            assume(replies.len() > 0);
            let max_ts = max_from_get_ts_replies(replies);
            assert(max_ts is Some);
            let max_ts = max_ts.expect("the quorum should never be empty");

            Ok(max_ts)
        }?;

        {
            assume(max_ts.seqno + 1 < u64::MAX);
            let bpool = BroadcastPool::new(&self.pool);
            let quorum_res = bpool
                .broadcast(Request::Write {
                    val,
                    timestamp: Timestamp {
                        seqno: max_ts.seqno + 1,
                        client_id: self.pool.id(),
                    },
                })
                .wait_for(
                    |s| s.replies().len() >= s.quorum_size(),
                    |r| match r.deref() {
                        Response::Write { .. } => Ok(()),
                        _ => Err(r),
                    },
                );

            let _quorum = match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    return Err((
                        error::Error::FailedSecondQuorum {
                            obtained: e.replies().len(),
                            required: self.pool.quorum_size(),
                        },
                        Tracked(lin)
                    ));
                }
            };

            let comp = Tracked({
                let op = RegisterWrite { id: self.loc(), new_value: val };
                lin.apply(op, self.register.borrow_mut(), (), &())
            });

            Ok(comp)
        }
    }
}

}
