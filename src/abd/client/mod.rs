#[allow(unused_imports)]
use crate::abd::invariants;
use crate::abd::invariants::lin_queue::InsertError;
use crate::abd::invariants::lin_queue::LinReadToken;
use crate::abd::invariants::lin_queue::LinWriteToken;
use crate::abd::invariants::lin_queue::MaybeReadLinearized;
use crate::abd::invariants::lin_queue::MaybeWriteLinearized;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::quorum::Quorum;
use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::invariants::ClientToken;
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
mod net_axioms;
mod utils;

use vstd::invariant::InvariantPredicate;
#[allow(unused_imports)]
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::proph::Prophecy;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

use net_axioms::*;
use utils::*;
use vstd::tokens::set::GhostSubset;

verus! {

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
pub trait AbdRegisterClient<C, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    spec fn register_loc(self) -> int;

    spec fn client_id(self) -> u64;

    spec fn named_locs(self) -> Map<&'static str, int>;

    spec fn inv(self) -> bool;

    spec fn weak_inv(self) -> bool;

    proof fn lemma_weak_inv(self)
        requires
            self.inv(),
        ensures
            self.weak_inv(),
    ;

    fn read(&self, lin: Tracked<RL>) -> (r: Result<
        (Option<u64>, Timestamp, Tracked<RL::Completion>),
        error::ReadError<RL, RL::Completion>,
    >)
        requires
            lin@.pre(RegisterRead { id: Ghost(self.register_loc()) }),
            !lin@.namespaces().contains(invariants::state_inv_id()),
            lin@.namespaces().finite(),
            self.weak_inv(),
        ensures
            self.weak_inv(),
            r is Ok ==> ({
                let (val, ts, compl) = r->Ok_0;
                lin@.post(RegisterRead { id: Ghost(self.register_loc()) }, val, compl@)
            }),
            r is Err ==> ({
                let err = r->Err_0;
                let op = RegisterRead { id: Ghost(self.register_loc()) };
                &&& err is FailedFirstQuorum ==> ({
                    &&& err->FailedFirstQuorum_lincomp@.lin() == lin
                    &&& err->FailedFirstQuorum_lincomp@.op() == op
                })
                &&& err is FailedSecondQuorum ==> ({
                    &&& err->FailedSecondQuorum_lincomp@.lin() == lin
                    &&& err->FailedSecondQuorum_lincomp@.op() == op
                })
            }),
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
    fn write(&mut self, val: Option<u64>, lin: Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >)
        requires
            old(self).inv(),
            lin@.pre(RegisterWrite { id: Ghost(old(self).register_loc()), new_value: val }),
            !lin@.namespaces().contains(invariants::state_inv_id()),
            lin@.namespaces().finite(),
        ensures
            old(self).named_locs() == self.named_locs(),
            self.weak_inv(),
            r is Ok ==> ({
                let comp = r->Ok_0;
                &&& self.inv()
                &&& lin@.post(
                    RegisterWrite { id: Ghost(self.register_loc()), new_value: val },
                    (),
                    comp@,
                )
            }),
            r is Err ==> ({
                let err = r->Err_0;
                &&& err is FailedFirstQuorum ==> ({
                    &&& self.inv()
                    &&& err->lincomp@.lin() == lin
                    &&& err->lincomp@.op() == RegisterWrite {
                        id: Ghost(self.register_loc()),
                        new_value: val,
                    }
                })
                &&& err is FailedSecondQuorum ==> ({
                    let op = RegisterWrite { id: Ghost(self.register_loc()), new_value: val };
                    &&& err->token@.value() == (lin@, op)
                    &&& err->token@.key() == err->timestamp
                })
            }),
    ;

    // Wait for register to move past the value written, so we can recover the token and linearizer
    // in the queue and restore invariants on the client.
    //
    // Note that since this is only called when the second phase happens, at least one server has
    // received the write. This means that recover_client, by reading the register on a loop can
    // finish its own previous write.
    fn recover_client(&mut self, error: error::WriteError<ML, ML::Completion>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >)
        requires
            old(self).weak_inv(),
            error is FailedSecondQuorum,
            error->token@.key() == error->timestamp,
        ensures
            r is Ok ==> ({
                let (lin, op) = error->token@.value();
                let comp = r->Ok_0;
                &&& self.inv()
                &&& lin.post(op, (), comp@)
            }),
            r is Err ==> ({
                &&& self.weak_inv()
                &&& r->Err_0 == error
            }),
    ;
}

pub struct AbdPool<Pool, ML, RL, WC, RC> {
    pool: Pool,
    register_id: Ghost<int>,
    // assert ownership on timestamps with a particular client_id
    client_tok_subset: Tracked<GhostSubset<u64>>,
    state_inv: Tracked<StateInvariant<ML, RL, WC, RC>>,
}

impl<Pool, C, ML, RL> AbdPool<Pool, ML, RL, ML::Completion, RL::Completion> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(
        pool: Pool,
        Tracked(client_token): Tracked<ClientToken>,
        state_inv: Tracked<StateInvariant<ML, RL, ML::Completion, RL::Completion>>,
    ) -> (r: Self)
        requires
            pool.n() > 0,
            pool.pool_id() == client_token@,
            state_inv@.constant().client_token_auth_id == client_token.id(),
            state_inv@.namespace() == invariants::state_inv_id(),
        ensures
            r._inv(),
    {
        AbdPool {
            pool,
            client_tok_subset: Tracked(client_token.subset()),
            state_inv,
            register_id: Ghost(state_inv@.constant().register_id),
        }
    }

    closed spec fn id(self) -> u64 {
        self.pool.pool_id()
    }

    pub closed spec fn _inv(self) -> bool {
        &&& self._weak_inv()
        &&& self.client_tok_subset@@ == set![self.id()]
        &&& self.client_tok_subset@.is_singleton()
    }

    pub closed spec fn _weak_inv(self) -> bool {
        &&& self.pool.n() > 0
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.state_inv@.constant().register_id == self.register_id
        &&& self.state_inv@.constant().client_token_auth_id == self.client_tok_subset@.id()
    }

    pub fn quorum_size(&self) -> usize {
        self.pool.quorum_size()
    }

    spec fn qsize(self) -> nat {
        self.pool.qsize()
    }

    proof fn lemma_qsize_nonempty(self)
        requires
            self.pool.n() > 0,
        ensures
            self.qsize() > 0,
    {
        self.pool.lemma_quorum_nonzero();
    }
}

impl<Pool, C, ML, RL> AbdRegisterClient<C, ML, RL> for AbdPool<
    Pool,
    ML,
    RL,
    ML::Completion,
    RL::Completion,
> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    closed spec fn client_id(self) -> u64 {
        self.id()
    }

    closed spec fn register_loc(self) -> int {
        self.register_id@
    }

    closed spec fn named_locs(self) -> Map<&'static str, int> {
        map![
            "register" => self.register_id@,
            "state_inv" => self.state_inv@.namespace(),
        ]
    }

    closed spec fn inv(self) -> bool {
        self._inv()
    }

    closed spec fn weak_inv(self) -> bool {
        self._weak_inv()
    }

    proof fn lemma_weak_inv(self) {
    }

    fn read(&self, Tracked(lin): Tracked<RL>) -> (r: Result<
        (Option<u64>, Timestamp, Tracked<RL::Completion>),
        error::ReadError<RL, RL::Completion>,
    >) {
        let op = RegisterRead { id: Ghost(self.register_loc()) };
        // NOTE: IMPORTANT: We need to add the linearizer to the queue at this point -- see
        // discussion on `write`
        let proph_val = Prophecy::<Option<u64>>::new();
        let tracked token;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                token = state.linearization_queue.insert_read_linearizer(lin, op, proph_val@, &state.register);
            }
        });

        let bpool = BroadcastPool::new(&self.pool);
        let quorum_res = bpool.broadcast(Request::Get).wait_for(
            |s| s.replies().len() >= s.quorum_size(),
            |r|
                match r.clone().into_inner() {
                    Response::Get { timestamp, val, .. } => Ok((timestamp, val)),
                    _ => Err(r),
                },
        );

        let quorum = match quorum_res {
            Ok(q) => q,
            Err(e) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                });
                return Err(
                    error::ReadError::FailedFirstQuorum {
                        obtained: e.replies().len(),
                        required: self.pool.quorum_size(),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };

        // check early return
        let replies = quorum.replies();
        // TODO(assume): network axiomatization invariant -- comes from spec'ing network layer
        assume(replies.len() == self.qsize());
        proof {
            self.lemma_qsize_nonempty();
        }
        let opt = max_from_get_replies(replies);
        let (max_ts, max_val) = opt.expect("there should be at least one reply");
        let mut n_max_ts = 0usize;
        let q_iter = replies.iter();
        for (_idx, (ts, _val)) in q_iter {
            if ts.seqno == max_ts.seqno && ts.client_id == max_ts.client_id {
                // XXX(assume): integer overflow assume
                assume(n_max_ts + 1 < usize::MAX);
                n_max_ts += 1;
            }
        }

        proph_val.resolve(&max_val);

        if n_max_ts >= self.pool.quorum_size() {
            let tracked comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let ghost old_watermark = state.linearization_queue.watermark;

                    let tracked mut servers = ServerUniverse::dummy();
                    vstd::modes::tracked_swap(&mut servers, &mut state.servers);
                    let tracked (mut new_servers, quorum) = axiom_get_unanimous_replies(replies, servers, max_ts, token.value().min_ts@.timestamp());
                    servers.lemma_leq_quorums(new_servers, state.linearization_queue.watermark@.timestamp());
                    vstd::modes::tracked_swap(&mut new_servers, &mut state.servers);


                    // TODO(assume/read_lin): need to show that *at this point* the existence of a
                    // read token implies the existence of the corresponding write token or that it
                    // is over?
                    assume(state.linearization_queue.write_token_map@.contains_key(max_ts));

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                    let tracked (watermark, mut register) = state.linearization_queue.apply_linearizers_up_to(register, max_ts);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);

                    if max_ts > old_watermark@.timestamp() {
                        state.servers.lemma_quorum_lb(quorum, max_ts);
                        assert(state.linearization_queue.watermark@.timestamp() == max_ts);
                    } else {
                        assert(old_watermark@.timestamp() == state.linearization_queue.watermark@.timestamp());
                    }

                    comp = state.linearization_queue.extract_read_completion(token, max_ts, watermark);
                }

                // XXX: not load bearing but good for debugging
                assert(<invariants::StatePredicate as vstd::invariant::InvariantPredicate<_, _>>::inv(self.state_inv@.constant(), state));
            });
            return Ok((max_val, max_ts, Tracked(comp)));
        }
        // non-unanimous read: write-back

        let bpool = BroadcastPool::new(&self.pool);
        #[allow(unused_parens)]
        let replies_result = bpool.broadcast_filter(
            Request::Write { val: max_val, timestamp: max_ts },
            // writeback to replicas that did not have the maximum timestamp
            |idx|
                {
                    let q_iter = quorum.replies().iter();
                    for (nidx, (ts, _val)) in q_iter {
                        if idx == *nidx && (ts.seqno != max_ts.seqno || ts.client_id
                            != max_ts.client_id) {
                            return true;
                        }
                    }

                    false
                },
        )
        // bellow is error handling + type handling + logging stuff
        .wait_for(
            (|s|
                requires
                    s.replies.len() + n_max_ts < usize::MAX,
                { s.replies.len() + n_max_ts >= s.quorum_size() }),
            |r|
                match r.deref() {
                    Response::Write { .. } => Ok(()),
                    _ => Err(r),
                },
        );

        let wb_rep = match replies_result {
            Ok(r) => r,
            Err(replies) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                });
                return Err(
                    error::ReadError::FailedSecondQuorum {
                        obtained: replies.replies().len(),
                        required: self.pool.quorum_size(),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };
        let wb_replies = wb_rep.replies();

        let tracked comp;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let ghost old_watermark = state.linearization_queue.watermark;

                let tracked mut servers = ServerUniverse::dummy();
                vstd::modes::tracked_swap(&mut servers, &mut state.servers);
                let tracked (mut new_servers, quorum) = axiom_writeback_unanimous_replies(replies, wb_replies, servers, max_ts, token.value().min_ts@.timestamp());
                servers.lemma_leq_quorums(new_servers, state.linearization_queue.watermark@.timestamp());
                vstd::modes::tracked_swap(&mut new_servers, &mut state.servers);

                // TODO(assume/read_lin): need to show that *at this point* the existence of a
                // read token implies the existence of the corresponding write token or that it is
                // over?
                assume(state.linearization_queue.write_token_map@.contains_key(max_ts));

                let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                vstd::modes::tracked_swap(&mut register, &mut state.register);
                let tracked (watermark, mut register) = state.linearization_queue.apply_linearizers_up_to(register, max_ts);
                vstd::modes::tracked_swap(&mut register, &mut state.register);

                if max_ts > old_watermark@.timestamp() {
                    state.servers.lemma_quorum_lb(quorum, max_ts);
                    assert(state.linearization_queue.watermark@.timestamp() == max_ts);
                } else {
                    assert(old_watermark@.timestamp() == state.linearization_queue.watermark@.timestamp());
                }

                comp = state.linearization_queue.extract_read_completion(token, max_ts, watermark);
            }

            // XXX: not load bearing but good for debugging
            assert(<invariants::StatePredicate as vstd::invariant::InvariantPredicate<_, _>>::inv(self.state_inv@.constant(), state));
        });
        Ok((max_val, max_ts, Tracked(comp)))
    }

    fn write(&mut self, val: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >) {
        let op = RegisterWrite { id: Ghost(self.register_loc()), new_value: val };
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
        let proph_seqno = Prophecy::<u64>::new();
        let ghost proph_ts = Timestamp { seqno: proph_seqno@, client_id: self.client_id() };
        let tracked token_res;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let tracked tok = self.client_tok_subset.borrow_mut().take().singleton();
                token_res = state.linearization_queue.insert_write_linearizer(lin, op, proph_ts, tok);
            }
        });

        let quorum = {
            let bpool = BroadcastPool::new(&self.pool);

            let quorum_res = bpool.broadcast(Request::GetTimestamp).wait_for(
                |s| s.replies().len() >= s.quorum_size(),
                |r|
                    match r.deref() {
                        Response::GetTimestamp { timestamp, .. } => Ok(*timestamp),
                        _ => Err(r),
                    },
            );

            match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    let tracked lincomp;
                    vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                        proof {
                            let tracked client_token;
                            if &token_res is Ok {
                                let tracked token = token_res.tracked_unwrap();
                                let tracked x = state.linearization_queue.remove_write_lin(token);
                                lincomp = x.0;
                                client_token = x.1;
                            } else {
                                let tracked err = token_res.tracked_unwrap_err();
                                let tracked (err_lin, tok) = err.tracked_write_destruct();
                                lincomp = MaybeWriteLinearized::linearizer(err_lin, op, proph_ts);
                                client_token = tok;
                            }

                            let tracked mut client_tok_subset = client_token.subset();
                            vstd::modes::tracked_swap(&mut client_tok_subset, self.client_tok_subset.borrow_mut());
                        }
                    });

                    return Err(
                        error::WriteError::FailedFirstQuorum {
                            obtained: e.replies().len(),
                            required: self.pool.quorum_size(),
                            lincomp: Tracked(lincomp),
                        },
                    );
                },
            }
        };

        let replies = quorum.replies();
        // TODO(assume): network axiomatization invariant -- comes from spec'ing network layer
        assume(replies.len() == self.qsize());
        proof {
            self.lemma_qsize_nonempty();
        }
        let max_ts = max_from_get_ts_replies(replies);
        assert(max_ts is Some);
        let max_ts = max_ts.expect("the quorum should never be empty");

        // XXX(assume): integer overflow
        // XXX: timestamp recycling would be interesting
        assume(max_ts.seqno < u64::MAX - 1);
        let exec_seqno = max_ts.seqno + 1;
        let exec_ts = Timestamp { seqno: exec_seqno, client_id: self.pool.id() };
        proph_seqno.resolve(&exec_seqno);
        assert(proph_ts == exec_ts);

        let tracked token;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let tracked mut servers = ServerUniverse::dummy();
                vstd::modes::tracked_swap(&mut servers, &mut state.servers);
                let tracked (mut new_servers, quorum) = axiom_get_ts_replies(replies, servers, max_ts);
                servers.lemma_leq_quorums(new_servers, state.linearization_queue.watermark@.timestamp());
                vstd::modes::tracked_swap(&mut new_servers, &mut state.servers);

                token = lemma_watermark_contradiction(
                    token_res,
                    proph_ts,
                    lin,
                    op,
                    self.state_inv@.constant(),
                    &state,
                    quorum
                );
            }
        });

        {
            let bpool = BroadcastPool::new(&self.pool);
            let quorum_res = bpool.broadcast(Request::Write { val, timestamp: exec_ts }).wait_for(
                |s| s.replies().len() >= s.quorum_size(),
                |r|
                    match r.deref() {
                        Response::Write { .. } => Ok(()),
                        _ => Err(r),
                    },
            );

            let quorum = match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    return Err(
                        error::WriteError::FailedSecondQuorum {
                            obtained: e.replies().len(),
                            required: self.pool.quorum_size(),
                            timestamp: exec_ts,
                            token: Tracked(token),
                        },
                    );
                },
            };
            let replies = quorum.replies();

            let exec_comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                let tracked comp;
                proof {
                    token.agree(&state.linearization_queue.write_token_map);
                    state.linearization_queue.lemma_write_token_is_in_queue(&token);

                    let ghost old_watermark = state.linearization_queue.watermark;

                    let tracked mut servers = ServerUniverse::dummy();
                    vstd::modes::tracked_swap(&mut servers, &mut state.servers);
                    let tracked (mut new_servers, quorum) = axiom_write_replies(replies, servers, exec_ts);
                    servers.lemma_leq_quorums(new_servers, state.linearization_queue.watermark@.timestamp());
                    vstd::modes::tracked_swap(&mut new_servers, &mut state.servers);

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);
                    let tracked (resource, mut register) = state.linearization_queue.apply_linearizers_up_to(register, exec_ts);
                    vstd::modes::tracked_swap(&mut register, &mut state.register);

                    if exec_ts > old_watermark@.timestamp() {
                        state.servers.lemma_quorum_lb(quorum, exec_ts);
                        assert(state.linearization_queue.watermark@.timestamp() == exec_ts);
                    } else {
                        assert(old_watermark@.timestamp() == state.linearization_queue.watermark@.timestamp());
                    }

                    let tracked (c, tok) = state.linearization_queue.extract_write_completion(token, resource);
                    let tracked mut subset = tok.subset();
                    vstd::modes::tracked_swap(&mut subset, self.client_tok_subset.borrow_mut());


                    comp = c;
                }

                exec_comp = Tracked(comp);

                // XXX: not load bearing but good for debugging
                assert(<invariants::StatePredicate as vstd::invariant::InvariantPredicate<_, _>>::inv(self.state_inv@.constant(), state));
            });

            Ok(exec_comp)
        }
    }

    fn recover_client(&mut self, error: error::WriteError<ML, ML::Completion>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >) {
        // TODO(recover): issue a read and if the timestamp is >= error.timestamp we can return the
        // completion and restore the invariant
        Err(error)
    }
}

pub proof fn lemma_inv<Pool, C, ML, RL>(
    c: AbdPool<Pool, ML, RL, ML::Completion, RL::Completion>,
) where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    ensures
        c._inv() <==> c.inv(),
        c._weak_inv() <==> c.weak_inv(),
{
}

pub proof fn lemma_watermark_contradiction<ML, RL>(
    tracked token_res: Result<LinWriteToken<ML>, InsertError<ML, RL>>,
    timestamp: Timestamp,
    lin: ML,
    op: RegisterWrite,
    pred: invariants::StatePredicate,
    tracked state: &invariants::State<ML, RL, ML::Completion, RL::Completion>,
    tracked quorum: Quorum,
) -> (tracked tok: LinWriteToken<ML>) where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        <invariants::StatePredicate as InvariantPredicate<_, _>>::inv(pred, *state),
        state.servers.valid_quorum(quorum),
        state.servers.quorum_timestamp(quorum) < timestamp,
        token_res is Ok ==> {
            let tok = token_res->Ok_0;
            &&& tok.key() == timestamp
            &&& tok.value() == (lin, op)
            &&& tok.id() == state.linearization_queue.write_token_map.id()
        },
        token_res is Err ==> ({
            let err = token_res->Err_0;
            let watermark_lb = token_res->Err_0->w_watermark_lb;
            &&& err is WriteWatermarkContradiction
            &&& timestamp <= watermark_lb@.timestamp()
            &&& watermark_lb.loc() == state.linearization_queue.watermark.loc()
            &&& watermark_lb@ is LowerBound
        }),
    ensures
        tok == token_res->Ok_0,
        tok.key() == timestamp,
        tok.value() == (lin, op),
        tok.id() == state.linearization_queue.write_token_map.id(),
{
    if &token_res is Err {
        let tracked err = token_res.tracked_unwrap_err();
        assert(err is WriteWatermarkContradiction);
        let tracked mut watermark_lb = err.lower_bound();

        // derive the contradiction
        // NOTE: only the lemma invocation is needed but this is key part of the proof
        // leaving the asserts helps document it
        //
        // proph_ts <= watermark_old
        assert(timestamp <= watermark_lb@.timestamp());
        // watermark_old <= curr_watermark
        watermark_lb.lemma_lower_bound(&state.linearization_queue.watermark);
        assert(watermark_lb@.timestamp() <= state.linearization_queue.watermark@.timestamp());
        // curr_watermark <= quorum.timestamp() (forall valid quorums)
        assert(state.linearization_queue.watermark@.timestamp() <= state.servers.quorum_timestamp(
            quorum,
        ));
        // quorum.timestamp() < proph_ts (by construction)
        assert(state.servers.quorum_timestamp(quorum) < timestamp);
        // CONTRADICTION
        assert(timestamp < timestamp);
        proof_from_false()
    } else {
        let tracked token = token_res.tracked_unwrap();
        token
    }
}

} // verus!
