use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::BroadcastPool;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::proto::Tagged;

mod client_id_map;
pub mod error;
mod history;
mod linearization;
pub mod linearizers;
pub mod logatom;
mod timestamp;
mod utils;

use std::sync::Arc;

#[allow(unused_imports)]
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::proph::Prophecy;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;

use client_id_map::ClientMap;
use client_id_map::ClientOwns;
use linearization::*;
use logatom::*;
use utils::*;

verus! {

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
pub trait AbdRegisterClient<C, ML: MutLinearizer<RegisterWrite>> {
    spec fn loc(&self) -> int;

    // TODO: read is &mut self because it needs access to the linearization queue
    // This should be fixable with an atomic invariant
    fn read<RL: ReadLinearizer<RegisterRead>>(&mut self, lin: Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), error::ReadError<RL>>)
        requires
            lin@.pre(RegisterRead { id: Ghost(old(self).loc()) })
        ensures
            old(self).loc() == self.loc(),
            r is Ok ==> ({
                let (val, ts, compl) = r->Ok_0;
                lin@.post(RegisterRead { id: Ghost(self.loc()) }, val, compl@)
            }),
            r is Err ==> ({
                r->Err_0.lin() == lin
            })
        ;

    // TODO: help -- this should be able to be done with a shared reference: all the mutable
    // accesses are in ghost state, and the register should be able to linearize against a local
    // value.
    //
    // NOTE: to make it shared we need to restructure the timestamp
    // The timestamp requires a field for a per-client seqno that orders the writes on the same
    // client
    //
    // Consider the following counterexample:
    // - Two writes come through the same client
    // - They both observe a read at (seqno, c_id')
    // - They both write to (seqno + 1, c_id) -- but with different values
    //
    // To solve it, we add an extra (atomic) client seqno to break ties between concurrent writes
    // in the same client:
    // - Two writes come through the same client
    // - They both observe a read at (seqno, c_id', c_seqno')
    // - They race to increment an atomic internal c_seqno (one gets c_seqno1 and the other c_seqno2)
    // - They write to (seqno + 1, c_id, c_seqno1) and (seqno + 1, c_id, c_seqno2) respectively
    fn write(&mut self, val: Option<u64>, lin: Tracked<ML>) -> (r: Result<Tracked<ML::Completion>, error::WriteError>)
        requires
            lin@.pre(RegisterWrite { id: Ghost(old(self).loc()), new_value: val })
        ensures
            old(self).loc() == self.loc(),
            r is Ok ==> ({
                let compl = r->Ok_0;
                lin@.post(RegisterWrite { id: Ghost(self.loc()), new_value: val }, (), compl@)
            }),
        ;
}

pub struct AbdPool<Pool, ML: MutLinearizer<RegisterWrite>> {
    pub pool: Pool,

    pub max_seqno: u64,

    // map from pool.id() -> max seqno allocated
    pub tracked singleton: GhostSubmap<u64, u64>,

    // Local view of the register
    pub register: Tracked<GhostVarAuth<Option<u64>>>,

    // TODO: make this an atomic invariant
    pub linearization_queue: Tracked<LinearizationQueue<ML>>,
}

type RegisterView = Arc<Tracked<GhostVar<Option<u64>>>>;

pub proof fn initialize_system() -> AtomicInvariant<_> {
}

pub proof fn get_system_invariants() -> AtomicInvariant<(), LinearizationQueue, ()>;

impl<Pool, C, ML> AbdPool<Pool, ML>
where
    Pool: ConnectionPool<C = C>,
    ML: MutLinearizer<RegisterWrite>
{
    pub fn new(pool: Pool) -> (Self, RegisterView) {
        // TODO: this is not known (maybe this has to be Option<Option<u64>>?)
        let tracked (register, view) = GhostVarAuth::<Option<u64>>::new(None);
        let tracked lin_queue = LinearizationQueue::dummy();

        let register = Tracked(register);
        let view = Arc::new(Tracked(view));
        let linearization_queue = Tracked(lin_queue);

        let pool = AbdPool {
            pool,
            register,
            linearization_queue,
        };

        (pool, view)
    }

    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }
}


impl<Pool, C, ML> AbdRegisterClient<C, ML> for AbdPool<Pool, ML>
where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
    ML: MutLinearizer<RegisterWrite>
{
    open spec fn loc(&self) -> int {
        self.register@.id()
    }

    fn read<RL: ReadLinearizer<RegisterRead>>(&mut self, Tracked(lin): Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), error::ReadError<RL>>)
    {
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
                return Err(error::ReadError::FailedFirstQuorum {
                    obtained: e.replies().len(),
                    required: self.pool.quorum_size(),
                    linearizer: Tracked(lin),
                });
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
            proof {
                let tracked (register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                let register = Tracked(register);
                vstd::modes::tracked_swap(&mut register, &mut self.register);
                self.linearization_queue.borrow_mut().apply_linearizer(register@, &max_ts);
                vstd::modes::tracked_swap(&mut register, &mut self.register);
            }
            let comp = Tracked({
                let op = RegisterRead { id: Ghost(self.loc()) };
                lin.apply(op, self.register.borrow(), &max_val)
            });
            return Ok((max_val, max_ts, comp));
        }

        // non-unanimous read: write-back
        let bpool = BroadcastPool::new(&self.pool);
        #[allow(unused_parens)]
        let replies_result = bpool
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


        if let Err(replies) = replies_result {
            return Err(error::ReadError::FailedSecondQuorum {
                obtained: replies.replies().len(),
                required: self.pool.quorum_size(),
                linearizer: Tracked(lin),
            });
        }

        proof {
            let tracked (register, _view) = GhostVarAuth::<Option<u64>>::new(None);
            vstd::modes::tracked_swap(&mut Tracked(register), &mut self.register);
            self.linearization_queue.borrow_mut().apply_linearizer(register, &max_ts);
            vstd::modes::tracked_swap(&mut Tracked(register), &mut self.register);
        }
        let comp = Tracked({
            let op = RegisterRead { id: Ghost(self.loc()) };
            lin.apply(op, self.register.borrow(), &max_val)
        });
        Ok((max_val, max_ts, comp))
    }

    fn write(&mut self, val: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<Tracked<ML::Completion>, error::WriteError>)
    {
        // NOTE: IMPORTANT: We need to add the linearizer to the queue at this point
        //
        // Imagine if we added this after the read quorum is achieved
        // and we know which timestamp we are writing to.
        //
        // A concurrent write can read the same timestamp but write to a posterior one
        // (by having a greater client id)
        //
        // This means that secondary write can actually go ahead and finish before the first phase
        // of our write finishes
        //
        // Consequently, when they apply all the linearizers up to their watermark, our linearizer
        // is not there. This breaks the invariant on the linearization queue: all possible
        // linearizers refering to timestamps not greater than the watermark (increased when the
        // linearizers are applied) have been applied
        //
        // The way we go about this is by prophecizing the timestamp a write will get and put it in
        // the queue immediately. Once we figure out the timestamp, we resolve the prophecy
        // variable.
        let proph_ts = Prophecy::<Timestamp>::new();
        let token_res = Tracked(self.linearization_queue.borrow_mut().insert_linearizer(
            lin,
            RegisterWrite { id: Ghost(self.loc()), new_value: val },
            proph_ts@
        ));

        // TODO: if the token_res is a Watermark contradiction
        // open global invariant and check that there exists a quorum of lower bounds
        // that corroborates the watermark value

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
                    return Err(error::WriteError::FailedFirstQuorum {
                        obtained: e.replies().len(),
                        required: self.pool.quorum_size(),
                    });
                }
            };

            let replies = quorum.replies();
            assume(replies.len() > 0);
            // TODO: construct an upper bound on the watermark from the quorum of lower bounds
            let max_ts = max_from_get_ts_replies(replies);
            assert(max_ts is Some);
            let max_ts = max_ts.expect("the quorum should never be empty");

            Ok(max_ts)
        }?;

        // TODO: if the token_res is a Watermark contradiction
        // get another (overlapping) quorum that also corroborates the watermark (via exec state)
        //
        // contradition:
        // \exists global inv quorum
        // proph_ts <= old(watermark) <= min(global inv quorum) <= max(exec quorum) < chosen ts == proph_ts

        // TODO: prove timestamp uniqueness
        let exec_ts = Timestamp { seqno: max_ts.seqno + 1, client_id: self.pool.id(), };
        proph_ts.resolve(&exec_ts);

        // TODO: with the timestamp uniqueness and the upper bound on the watermark
        // we can prove contradictions to unwrap the token to extract the completion
        assume(token_res@.is_ok());
        let tracked Tracked(token) = token_res@.unwrap();

        {
            assume(max_ts.seqno + 1 < u64::MAX);
            let bpool = BroadcastPool::new(&self.pool);
            let quorum_res = bpool
                .broadcast(Request::Write {
                    val,
                    timestamp: exec_ts,
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
                    return Err(error::WriteError::FailedSecondQuorum {
                        obtained: e.replies().len(),
                        required: self.pool.quorum_size(),
                    });
                }
            };

            let tracked (register, _view) = GhostVarAuth::<Option<u64>>::new(None);
            proof {
            vstd::modes::tracked_swap(&mut Tracked(register), &mut self.register);
            }
            let tracked (resource, register) = self.linearization_queue.borrow_mut().apply_linearizer(register, &exec_ts);
            proof {
            vstd::modes::tracked_swap(&mut Tracked(register), &mut self.register);
            }

            let comp = Tracked(self.linearization_queue.borrow_mut().extract_completion(token, resource));


            Ok(comp)
        }
    }
}

}
