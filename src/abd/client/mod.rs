use crate::abd::invariants;
use crate::abd::invariants::client_id_map::ClientOwns;
use crate::abd::invariants::lin_queue::*;
use crate::abd::invariants::logatom::*;
use crate::abd::invariants::ClientIdInvariant;
use crate::abd::invariants::RegisterView;
use crate::abd::invariants::StateInvariant;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::BroadcastPool;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::proto::Tagged;

pub mod error;
mod utils;

use std::sync::Arc;

use vstd::invariant::InvariantPredicate;
#[allow(unused_imports)]
use vstd::logatom::*;
use vstd::modes::tracked_swap;
use vstd::prelude::*;
use vstd::proph::Prophecy;
use vstd::tokens::frac::GhostVar;
use vstd::tokens::frac::GhostVarAuth;
use vstd::tokens::map::GhostSubmap;

use utils::*;

verus! {

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
pub trait AbdRegisterClient<C, ML: MutLinearizer<RegisterWrite>> {
    spec fn register_loc(&self) -> int;
    spec fn named_locs(&self) -> Map<&'static str, int>;

    // TODO: read is &mut self because it needs access to the linearization queue
    // This should be fixable with an atomic invariant
    fn read<RL: ReadLinearizer<RegisterRead>>(&self, lin: Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), error::ReadError<RL>>)
        requires
            lin@.pre(RegisterRead { id: Ghost(self.register_loc()) }),
            !lin@.namespaces().contains(1)
        ensures
            r is Ok ==> ({
                let (val, ts, compl) = r->Ok_0;
                lin@.post(RegisterRead { id: Ghost(self.register_loc()) }, val, compl@)
            }),
            r is Err ==> ({
                r->Err_0.lin() == lin
            })
        ;

    // NOTE: to make writes behind a shared ref we need to restructure the timestamp
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
            lin@.pre(RegisterWrite { id: Ghost(old(self).register_loc()), new_value: val })
        ensures
            old(self).named_locs() == self.named_locs(),
            // TODO: does this condition make sense???
            //
            // r is Ok ==> ({
            //     let compl = r->Ok_0;
            //     lin@.post(RegisterWrite { id: Ghost(self.register_loc()), new_value: val }, (), compl@)
            // }),
        ;
}

#[verifier::reject_recursive_types(C)]
pub struct AbdPool<Pool: ConnectionPool<C = C>, C, ML: MutLinearizer<RegisterWrite>> {
    pool: Pool,

    max_seqno: u64,

    register_id: Ghost<int>,

    // map from pool.id() -> max seqno allocated
    client_owns: Tracked<ClientOwns>,

    state_inv: Tracked<StateInvariant<ML>>,

    client_map: Tracked<ClientIdInvariant>,
}



impl<Pool, C, ML> AbdPool<Pool, C, ML>
where
    Pool: ConnectionPool<C = C>,
    ML: MutLinearizer<RegisterWrite>
{
    #[verifier::external_body]
    pub fn new(pool: Pool) -> (Self, Arc<Tracked<RegisterView>>) {
        let tracked state_inv;
        let tracked view;
        proof {
            let tracked (s, v) = invariants::get_system_state();
            state_inv = s;
            view = v;
        }


        let Tracked(client_map) = Tracked(invariants::get_client_map());

        // XXX: we could derive this with a sign-in procedure to create ids
        let tracked client_owns;
        let ghost register_id = state_inv.constant().register_id;

        vstd::open_atomic_invariant!(&client_map => map => {
            proof {
                // XXX(assume): removing this invariant requires an ID service
                assume(!map@.contains_key(pool.id()));
                client_owns = map.reserve(pool.id());
            }
        });

        let pool = AbdPool {
            pool,
            max_seqno: 0,
            client_owns: Tracked(client_owns),
            state_inv: Tracked(state_inv),
            client_map: Tracked(client_map),
            register_id: Ghost(register_id),
        };

        (pool, Arc::new(Tracked(view)))
    }

    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.max_seqno == self.client_owns@@.1
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.client_map@.namespace() == invariants::client_map_inv_id()
        &&& self.state_inv@.constant().register_id == self.register_id
    }

    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }
}


impl<Pool, C, ML> AbdRegisterClient<C, ML> for AbdPool<Pool, C, ML>
where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
    ML: MutLinearizer<RegisterWrite>
{
    closed spec fn register_loc(&self) -> int {
        self.register_id@
    }

    closed spec fn named_locs(&self) -> Map<&'static str, int> {
        map![
            "register" => self.register_id@,
            "state_inv" => self.state_inv@.namespace(),
            "client_map" => self.client_map@.namespace(),
        ]
    }

    fn read<RL: ReadLinearizer<RegisterRead>>(&self, Tracked(lin): Tracked<RL>) -> (r: Result<(Option<u64>, Timestamp, Tracked<RL::Completion>), error::ReadError<RL>>)
    {
        proof {
            use_type_invariant(self);
        }
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
        // TODO(assume): network axiomatization invariant -- comes from spec'ing network layer
        assume(replies.len() > 0);
        let opt = max_from_get_replies(replies);
        assert(opt is Some);
        let (max_ts, max_val) = opt.expect("there should be at least one reply");
        let mut n_max_ts = 0usize;
        let q_iter = quorum.replies().iter();
        for (_idx, (ts, _val)) in q_iter {
            if ts.seqno == max_ts.seqno && ts.client_id == max_ts.client_id {
                // XXX(assume): integer overflow assume
                assume(n_max_ts + 1 < usize::MAX);
                n_max_ts += 1;
            }
        }

        if n_max_ts >= self.pool.quorum_size() {
            let comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                    let tracked (_watermark, mut register) = state.linearization_queue.apply_linearizer(register, max_ts);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                }

                let op = RegisterRead { id: Ghost(self.register_loc()) };
                // TODO(assume): read linearizer requirements
                // probably comes from state invariant tied to the linearization queue
                assume(op.requires(state.register, max_val));
                comp = Tracked(lin.apply(op, &state.register, &max_val));

                // TODO(assume): min quorum invariant
                assume(state.linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts());
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

        let comp;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                vstd::modes::tracked_swap(&mut register, &mut state.register);
                let tracked (_watermark, mut register) = state.linearization_queue.apply_linearizer(register, max_ts);
                vstd::modes::tracked_swap(&mut register, &mut state.register);
            }

            let op = RegisterRead { id: Ghost(self.register_loc()) };
            // TODO(assume): read linearizer requirements
            // probably comes from state invariant tied to the linearization queue
            assume(op.requires(state.register, max_val));
            comp = Tracked(lin.apply(op, &state.register, &max_val));

            // TODO(assume): min quorum invariant
            assume(state.linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts());
        });
        Ok((max_val, max_ts, comp))
    }

    fn write(&mut self, val: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<Tracked<ML::Completion>, error::WriteError>)
    {
        // XXX(assume): this is required because of mut restrictions
        assume(self.inv());
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
        let tracked token_res;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                token_res = state.linearization_queue.insert_linearizer(
                    lin,
                    RegisterWrite { id: Ghost(self.register_loc()), new_value: val },
                    proph_ts@
                );
            }
            // TODO(nickolai): this is a load-bearing assert
            assert(token_res is Ok ==> token_res.unwrap().id() == self.state_inv@.constant().lin_queue_named_ids["token_map"]);
            // TODO(assume): min quorum invariant
            assume(state.linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts());
        });

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
            // TODO(assume): network axiomatization invariant -- comes from spec'ing network layer
            assume(replies.len() > 0);
            let max_ts = max_from_get_ts_replies(replies);
            assert(max_ts is Some);
            let max_ts = max_ts.expect("the quorum should never be empty");

            Ok(max_ts)
        }?;

        // TODO(contradiction): if the token_res is a Watermark contradiction
        //
        // this implies: proph_ts <= old(watermark)
        // watermark invariant implies: old(watermark) <= min(quorum)
        // min definition: min(quorum) <= exec quorum
        // construction: exec quorum < exec_ts
        // resolution: exec_ts == proph_ts

        // XXX(assume): integer overflow
        // XXX: timestamp recycling would be interesting
        assume(max_ts.seqno < u64::MAX - 1);
        let exec_ts = Timestamp { seqno: max_ts.seqno + 1, client_id: self.pool.id(), };
        proph_ts.resolve(&exec_ts);

        // TODO(assume): comes from contradiction above
        assume(token_res is Ok);
        let tracked token;
        proof { token = token_res.tracked_unwrap() };
        assert(token.timestamp() == exec_ts);

        {
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

            let comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                assert(token.id() == state.linearization_queue.token_map.id());
                let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                proof {
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                }
                let tracked (resource, mut register) = state.linearization_queue.apply_linearizer(register, exec_ts);
                proof {
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                }

                assert(resource@.timestamp() >= exec_ts);

                comp = Tracked(state.linearization_queue.extract_completion(token, resource));
                // TODO(assume): min quorum invariant
                assume(state.linearization_queue.watermark@.timestamp() <= state.server_map.min_quorum_ts());
            });


            Ok(comp)
        }
    }
}

}
