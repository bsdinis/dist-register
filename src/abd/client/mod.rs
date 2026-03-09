#[allow(unused_imports)]
use crate::abd::invariants;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::InsertError;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::LinWriteToken;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeWriteLinearized;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
#[allow(unused_imports)]
use crate::abd::invariants::quorum::Quorum;
#[allow(unused_imports)]
use crate::abd::invariants::quorum::ServerUniverse;
#[allow(unused_imports)]
use crate::abd::invariants::RegisterView;
use crate::abd::invariants::StateInvariant;
use crate::abd::proto::GetRequest;
use crate::abd::proto::GetTimestampRequest;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::WriteRequest;
use crate::abd::timestamp::Timestamp;

use crate::verdist::network::channel::Channel;
use crate::verdist::pool::BroadcastPool;
use crate::verdist::pool::ConnectionPool;
use crate::verdist::rpc::replies::ReplyAccumulator;

pub mod error;
mod net_axioms;
mod net_invs;
mod utils;

use net_invs::*;

use vstd::atomic::PAtomicU64;
#[allow(unused_imports)]
use vstd::invariant::InvariantPredicate;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::proph::Prophecy;
#[allow(unused_imports)]
use vstd::resource::ghost_var::GhostVarAuth;
use vstd::resource::Loc;

use std::hash::Hash;
use std::sync::Arc;

#[allow(unused_imports)]
use net_axioms::*;
use utils::*;

use super::invariants::committed_to::ClientCtrToken;

verus! {

// NOTE: LIMITATION
// - The MutLinearizer should be specified in the method
// - Type problem: the linearization queue is parametrized by the linearizer type
// - Polymorphism is hard
#[allow(unused)]
pub trait AbdRegisterClient<C, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    type Locs;

    spec fn register_loc(self) -> Loc;

    spec fn client_id(self) -> u64;

    spec fn named_locs(self) -> Self::Locs;

    spec fn inv(self) -> bool;

    fn read(&self, lin: Tracked<RL>) -> (r: Result<
        (Option<u64>, Timestamp, Tracked<RL::Completion>),
        error::ReadError<RL, RL::Completion>,
    >)
        requires
            lin@.pre(RegisterRead { id: Ghost(self.register_loc()) }),
            !lin@.namespaces().contains(invariants::state_inv_id()),
            lin@.namespaces().finite(),
            self.inv(),
        ensures
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

    // TODO(writes): make writes behind a shared ref.
    // Problem: there is only a single tracked ClientCtrToken which cannot be shared between
    // threads
    fn write(&mut self, value: Option<u64>, lin: Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >)
        requires
            old(self).inv(),
            lin@.pre(RegisterWrite { id: Ghost(old(self).register_loc()), new_value: value }),
            !lin@.namespaces().contains(invariants::state_inv_id()),
            lin@.namespaces().finite(),
        ensures
            self.inv(),
            self.named_locs() == old(self).named_locs(),
            r is Ok ==> ({
                let comp = r->Ok_0;
                &&& lin@.post(
                    RegisterWrite { id: Ghost(self.register_loc()), new_value: value },
                    (),
                    comp@,
                )
            }),
            r is Err ==> ({
                let err = r->Err_0;
                &&& err is FailedFirstQuorum ==> ({
                    &&& err.inv()
                    &&& err->lincomp@.lin() == lin
                    &&& err->lincomp@.op() == RegisterWrite {
                        id: Ghost(self.register_loc()),
                        new_value: value,
                    }
                })
                &&& err is FailedSecondQuorum ==> ({
                    let op = RegisterWrite { id: Ghost(self.register_loc()), new_value: value };
                    &&& err.inv()
                    &&& err->token@.value().lin == lin@
                    &&& err->token@.value().op == op
                })
            }),
    ;
}

#[allow(dead_code)]
pub struct AbdPool<Pool, ML, RL> where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pool: Pool,
    register_id: Ghost<Loc>,
    state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    client_ctr_token: Tracked<ClientCtrToken>,
    client_ctr: PAtomicU64,
}

impl<Pool, C, ML, RL> AbdPool<Pool, ML, RL> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    pub fn new(
        pool: Pool,
        client_ctr: PAtomicU64,
        client_ctr_token: Tracked<ClientCtrToken>,
        state_inv: Tracked<Arc<StateInvariant<ML, RL>>>,
    ) -> (r: Self)
        requires
            pool.spec_len() > 0,
            state_inv@.namespace() == invariants::state_inv_id(),
            state_inv@.constant().commitments_ids.client_ctr_id == client_ctr_token@.id(),
            client_ctr_token@.key() == pool.spec_id(),
            client_ctr_token@.value().0 == 0,
            client_ctr_token@.value().1 == client_ctr.id(),
        ensures
            r._inv(),
    {
        AbdPool {
            pool,
            state_inv,
            register_id: Ghost(state_inv@.constant().register_id),
            client_ctr_token,
            client_ctr,
        }
    }

    closed spec fn spec_len(self) -> nat {
        self.pool.spec_len()
    }

    closed spec fn id(self) -> u64 {
        self.pool.spec_id()
    }

    pub closed spec fn _inv(self) -> bool {
        &&& self.pool.spec_len() > 0
        &&& self.state_inv@.namespace() == invariants::state_inv_id()
        &&& self.state_inv@.constant().register_id == self.register_id
        &&& self.state_inv@.constant().commitments_ids.client_ctr_id == self.client_ctr_token@.id()
        &&& self.client_ctr_token@.key() == self.id()
        &&& self.client_ctr_token@.value().1 == self.client_ctr.id()
    }

    pub fn quorum_size(&self) -> (r: usize)
        ensures
            r == self.spec_quorum_size(),
    {
        self.pool.quorum_size()
    }

    pub closed spec fn spec_quorum_size(self) -> nat {
        self.pool.spec_quorum_size()
    }

    proof fn lemma_quorum_nonzero(self)
        requires
            self.spec_len() > 0,
        ensures
            self.spec_quorum_size() > 0,
    {
        self.pool.lemma_quorum_nonzero();
    }
}

#[allow(dead_code)]
pub struct AbdRegisterLocs {
    pub register_id: Loc,
    pub state_inv_namespace: int,
    pub client_ctr_perm: int,
    pub client_ctr_token_id: Loc,
}

impl<Pool, C, ML, RL> AbdRegisterClient<C, ML, RL> for AbdPool<Pool, ML, RL> where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request, Id = (u64, u64)>,
    C::Id: Eq + Hash,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,
 {
    type Locs = AbdRegisterLocs;

    closed spec fn client_id(self) -> u64 {
        self.id()
    }

    closed spec fn register_loc(self) -> Loc {
        self.register_id@
    }

    closed spec fn named_locs(self) -> AbdRegisterLocs {
        AbdRegisterLocs {
            register_id: self.register_id@,
            state_inv_namespace: self.state_inv@.namespace(),
            client_ctr_perm: self.client_ctr_token@.value().1,
            client_ctr_token_id: self.client_ctr_token@.id(),
        }
    }

    closed spec fn inv(self) -> bool {
        self._inv()
    }

    fn read(&self, Tracked(lin): Tracked<RL>) -> (r: Result<
        (Option<u64>, Timestamp, Tracked<RL::Completion>),
        error::ReadError<RL, RL::Completion>,
    >) {
        let tracked op = RegisterRead { id: Ghost(self.register_loc()) };
        // NOTE: IMPORTANT: We need to add the linearizer to the queue at this point -- see
        // discussion on `write`
        let proph_val = Prophecy::<Option<u64>>::new();
        let tracked token;
        let tracked server_lbs;
        let read_pred = Ghost(ReadPred::from_state(self.state_inv@.constant()));
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                token = state.linearization_queue.insert_read_linearizer(lin, op, proph_val@, &state.register);
                server_lbs = state.servers.extract_lbs();
                assume(forall|q: Quorum|  #[trigger] server_lbs.valid_quorum(q) ==> {
                    token.value().min_ts@.timestamp() <= server_lbs.quorum_timestamp(q)
                });
            }
            // XXX: debug assert
            assert(state.inv());
        });

        let req = Request::Get(GetRequest::new(Tracked(server_lbs.extract_lbs())));

        let ghost qsize = self.spec_quorum_size();
        let bpool = BroadcastPool::new(&self.pool);
        // TODO(obeys_cmp_spec): add this to verus
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        #[allow(unused_parens)]
        let accum = ReadAccumGetPhase::new(
            Tracked(server_lbs),
            Ghost(token.value().min_ts),
            read_pred,
        );
        let quorum_res = bpool.broadcast(req, read_pred, accum).wait_for(
            (|s| -> (r: bool)
                ensures
                    r ==> s.spec_len() >= qsize,
                { s.len() >= self.quorum_size() }),
            |r|
                match r {
                    Response::Get(get) => { Ok(get.clone()) },
                    _ => Err(r),
                },
        );

        let replies = match quorum_res {
            Ok(replies) => replies.into_accumulator().destruct(),
            Err(e) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                    // XXX: debug assert
                    assert(state.inv());
                });
                return Err(
                    error::ReadError::FailedFirstQuorum {
                        obtained: e.into_accumulator().n_replies(),
                        required: self.pool.quorum_size(),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };

        // check early return
        proof {
            self.lemma_quorum_nonzero();
        }
        // TODO(assume/wait_for_post)
        assume(replies.spec_n_get_replies() >= qsize);
        let agree_with_max = replies.agree_with_max().clone();
        let max_resp = replies.max_resp();
        let max_ts = max_resp.timestamp();
        let value = max_resp.value().clone();
        let Tracked(commitment) = max_resp.commitment();
        proph_val.resolve(&value);

        if replies.agree_with_max().len() >= self.pool.quorum_size() {
            let tracked comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                proof {
                    let ghost old_watermark = state.linearization_queue.watermark();
                    let ghost old_known = state.linearization_queue.known_timestamps();
                    let ghost old_servers = state.servers;
                    let ghost old_unclaimed = state.unclaimed_servers();
                    let ghost old_server_tokens = state.server_tokens@;

                    // TODO(assume/chan_k): commitment agreement
                    assume(commitment.id() == state.commitments.commitment_id());
                    state.commitments.agree_commitment(&commitment);

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    let tracked watermark = state.linearization_queue.apply_linearizers_up_to(
                            &mut state.register,
                            max_ts,
                    );

                    if max_ts > old_watermark {
                        // TODO(assume/quorum): valid quorum
                        assume(state.servers.valid_quorum(replies.quorum()));
                        // TODO(assume/quorum): unanimous quorum
                        assume(state.servers.unanimous_quorum(replies.quorum(), max_ts));
                        state.servers.lemma_quorum_lb(replies.quorum(), max_ts);
                        assert(state.linearization_queue.watermark() == max_ts);
                    } else {
                        assert(state.linearization_queue.watermark() == old_watermark);
                    }

                    // TODO(assume/replies): relate max_resp with min_ts
                    assume(max_ts >= token.value().min_ts@.timestamp());
                    comp = state.linearization_queue.extract_read_completion(
                        token,
                        max_ts,
                        watermark,
                        commitment.duplicate(),
                    );

                    // XXX: load bearing
                    assert(state.linearization_queue.known_timestamps() == old_known);
                    admit();
                }

                // XXX: debug assert
                assert(state.inv());
            });
            let (max_val, max_ts) = replies.max_resp().clone().into_inner();
            return Ok((max_val, max_ts, Tracked(comp)));
        }
        // non-unanimous read: write-back

        let ghost qsize = self.spec_quorum_size();
        let bpool = BroadcastPool::new(&self.pool);
        #[allow(unused_parens)]
        let replies_result = bpool.broadcast_filter(
            Request::Write(WriteRequest::new(value, max_ts, Tracked(commitment.duplicate()))),
            read_pred,
            ReadAccumWbPhase::new(replies),
            |id: (u64, u64)| !agree_with_max.contains(&id.1),
        ).wait_for(
            (|s| -> (r: bool)
                ensures
                    r ==> s.spec_len() + agree_with_max@.len() >= qsize,
                {
                    assume(s.spec_len() + agree_with_max.len() < usize::MAX);  // XXX: integer overflow
                    s.len() + agree_with_max.len() >= self.quorum_size()
                }),
            |r|
                match r {
                    Response::Write(write) => Ok(write.clone()),
                    _ => Err(r),
                },
        );

        let wb_replies = match replies_result {
            Ok(r) => r.into_accumulator().destruct(),
            Err(replies) => {
                let tracked lincomp;
                vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                    proof {
                        lincomp = state.linearization_queue.remove_read_lin(token);
                    }
                    // XXX: debug assert
                    assert(state.inv());
                });
                let accum = replies.into_accumulator().destruct();
                return Err(
                    error::ReadError::FailedSecondQuorum {
                        obtained: accum.n_wb_replies(),
                        required: self.pool.quorum_size().saturating_sub(
                            accum.agree_with_max().len(),
                        ),
                        lincomp: Tracked(lincomp),
                    },
                );
            },
        };

        let tracked comp;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let ghost old_watermark = state.linearization_queue.watermark();
                let ghost old_known = state.linearization_queue.known_timestamps();
                let ghost old_servers = state.servers;
                let ghost old_unclaimed = state.unclaimed_servers();
                let ghost old_server_tokens = state.server_tokens@;
                assert(old_servers.locs().dom() == old_servers.dom());


                /*
                old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());

                state.commitments.agree_commitment(&commitment);

                let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                let tracked watermark = state.linearization_queue.apply_linearizers_up_to(&mut state.register, max_ts);

                if max_ts > old_watermark {
                    state.servers.lemma_quorum_lb(quorum, max_ts);
                    assert(state.linearization_queue.watermark() == max_ts);
                } else {
                    assert(old_watermark == state.linearization_queue.watermark());
                }

                comp = state.linearization_queue.extract_read_completion(token, max_ts, watermark, commitment);
                */

                admit();
                comp = proof_from_false();

                // XXX: load bearing
                assert(state.linearization_queue.known_timestamps() == old_known);
            }

            // XXX: debug assert
            assert(state.inv());
        });
        let (max_val, max_ts) = wb_replies.max_resp().clone().into_inner();
        return Ok((max_val, max_ts, Tracked(comp)));
    }

    fn write(&mut self, value: Option<u64>, Tracked(lin): Tracked<ML>) -> (r: Result<
        Tracked<ML::Completion>,
        error::WriteError<ML, ML::Completion>,
    >) {
        let tracked op = RegisterWrite { id: Ghost(self.register_loc()), new_value: value };
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
        let tracked token_res;
        let client_ctr;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            let tracked mut perm;
            proof {
                perm = state.commitments.take_permission(self.client_ctr_token.borrow());
            }

            assume(perm.value() < u64::MAX); // XXX: integer overflow
            client_ctr = self.client_ctr.fetch_add(Tracked(&mut perm), 1);
            let ghost proph_ts = Timestamp { seqno: proph_seqno@, client_id: self.client_id(), client_ctr };

            proof {
                let ghost old_known = state.linearization_queue.known_timestamps();

                let tracked allocation_opt = if proph_ts > state.linearization_queue.watermark() {
                    let tracked mut allocation = state.commitments.alloc_value(self.client_ctr_token.borrow_mut(), proph_ts, op.new_value, perm);
                    state.commitments.agree_allocation(&allocation);

                    // XXX: load bearing
                    assert(!state.linearization_queue.known_timestamps().contains(proph_ts));
                    state.linearization_queue.lemma_known_timestamps();

                    Some(allocation)
                } else {
                    state.commitments.return_permission(self.client_ctr_token.borrow_mut(), perm);
                    None
                };

                token_res = state.linearization_queue.insert_write_linearizer(lin, op, proph_ts, allocation_opt);

                // XXX: load bearing
                assert(token_res is Ok ==> state.linearization_queue.known_timestamps() == old_known.insert(proph_ts));
            }
            // XXX: debug assert
            assert(state.inv());
        });
        let ghost proph_ts = Timestamp {
            seqno: proph_seqno@,
            client_id: self.client_id(),
            client_ctr,
        };

        let tracked server_lbs;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                server_lbs = state.servers.extract_lbs();
            }
        });
        let req = Request::GetTimestamp(GetTimestampRequest::new(Tracked(server_lbs)));
        let quorum = {
            let ghost qsize = self.spec_quorum_size();
            let bpool = BroadcastPool::new(&self.pool);
            // TODO(obeys_cmp_spec): add this to verus
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
            #[allow(unused_parens)]
            let quorum_res = bpool.broadcast::<EmptyPred, _>(
                req,
                Ghost(EmptyPred),
                BadAccumulator::new(),
            ).wait_for(
                (|s| -> (r: bool)
                    ensures
                        r ==> s.spec_len() >= qsize,
                    { s.len() >= self.quorum_size() }),
                |r|
                    match r {
                        Response::GetTimestamp(get_ts) => Ok(get_ts.clone()),
                        _ => Err(r),
                    },
            );

            match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    let tracked lincomp;
                    vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                        proof {
                            if &token_res is Ok {
                                let tracked token = token_res.tracked_unwrap();

                                let tracked (lc, allocation_opt) = state.linearization_queue.remove_write_lin(token);

                                // if this write had not been committed we need to remove it from
                                // the commitment map
                                if &allocation_opt is Some {
                                    let tracked allocation = allocation_opt.tracked_unwrap();
                                    state.commitments.remove_allocation(allocation, self.client_ctr_token.borrow());
                                    // XXX: load bearing
                                    assert(state.linearization_queue.known_timestamps() == state.commitments.allocated().dom());
                                }
                                lincomp = lc;
                            } else {
                                let tracked err = token_res.tracked_unwrap_err();
                                let tracked err_lin = err.tracked_write_destruct();
                                lincomp = MaybeWriteLinearized::linearizer(err_lin, op, proph_ts);
                            }
                        }
                        // XXX: debug assert
                        assert(state.inv());
                    });

                    return Err(
                        error::WriteError::FailedFirstQuorum {
                            obtained: e.into_accumulator().into().len(),
                            required: self.pool.quorum_size(),
                            lincomp: Tracked(lincomp),
                        },
                    );
                },
            }
        };

        let replies = quorum.into_accumulator().into();
        proof {
            self.lemma_quorum_nonzero();
        }
        let opt = max_from_get_ts_replies(&replies);
        assert(opt is Some);
        let max_resp = opt.expect("the quorum should never be empty");
        let max_ts = max_resp.timestamp();

        // XXX: timestamp recycling would be interesting
        assume(max_ts.seqno < u64::MAX - 1);  // XXX: integer overflow
        let exec_seqno = max_ts.seqno + 1;
        let exec_ts = Timestamp { seqno: exec_seqno, client_id: self.pool.id(), client_ctr };
        proph_seqno.resolve(&exec_seqno);
        assert(proph_ts == exec_ts);

        let tracked token;
        let tracked mut commitment;
        vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
            proof {
                let ghost old_servers = state.servers;
                let ghost old_unclaimed = state.unclaimed_servers();
                let ghost old_server_tokens = state.server_tokens@;
                assert(old_servers.locs().dom() == old_servers.dom());

                let tracked quorum = axiom_get_ts_replies(&replies, &mut state.servers, max_ts);
                assert(state.unclaimed_servers() == old_unclaimed);
                assert(state.server_tokens@ == old_server_tokens);
                assert forall |id: u64| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                    assert(old_servers.contains_key(id));
                }
                assert forall |id: u64| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                    assert(old_servers.contains_key(id));
                }
                old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());

                let tracked mut tk = lemma_watermark_contradiction(
                    token_res,
                    proph_ts,
                    lin,
                    op,
                    &state,
                    quorum
                );

                commitment = state.linearization_queue.commit_value(&mut tk);
                token = tk;
            }

            // XXX: debug assert
            assert(state.inv());
        });

        {
            let bpool = BroadcastPool::new(&self.pool);
            let ghost qsize = self.spec_quorum_size();
            // TODO(obeys_cmp_spec): add this to verus
            assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
            #[allow(unused_parens)]
            let quorum_res = bpool.broadcast::<EmptyPred, _>(
                Request::Write(WriteRequest::new(value, exec_ts, Tracked(commitment.duplicate()))),
                Ghost(EmptyPred),
                BadAccumulator::new(),
            ).wait_for(
                (|s| -> (r: bool)
                    ensures
                        r ==> s.spec_len() >= qsize,
                    { s.len() >= self.quorum_size() }),
                |r|
                    match r {
                        Response::Write(_) => Ok(()),
                        _ => Err(r),
                    },
            );

            let quorum = match quorum_res {
                Ok(q) => q,
                Err(e) => {
                    return Err(
                        error::WriteError::FailedSecondQuorum {
                            obtained: e.into_accumulator().into().len(),
                            required: self.pool.quorum_size(),
                            timestamp: exec_ts,
                            token: Tracked(token),
                            commitment: Tracked(commitment),
                        },
                    );
                },
            };
            #[allow(unused)]
            let replies = quorum.into_accumulator().into();

            let exec_comp;
            vstd::open_atomic_invariant!(&self.state_inv.borrow() => state => {
                let tracked comp;
                proof {
                    let ghost old_known = state.linearization_queue.known_timestamps();
                    let ghost old_watermark = state.linearization_queue.watermark();
                    let ghost old_servers = state.servers;
                    let ghost old_unclaimed = state.unclaimed_servers();
                    let ghost old_server_tokens = state.server_tokens@;
                    assert(old_servers.locs().dom() == old_servers.dom());

                    state.linearization_queue.lemma_write_token(&token);

                    let tracked quorum = axiom_write_replies(&replies, &mut state.servers, exec_ts);
                    assert(state.unclaimed_servers() == old_unclaimed);
                    assert(state.server_tokens@ == old_server_tokens);
                    assert forall |id: u64| #[trigger] state.unclaimed_servers().contains(id) implies state.servers[id]@@ is FullRightToAdvance by {
                        assert(old_servers.contains_key(id));
                    }
                    assert forall |id: u64| #[trigger] state.server_tokens@.contains_key(id) implies state.servers[id]@@ is HalfRightToAdvance by {
                        assert(old_servers.contains_key(id));
                    }
                    old_servers.lemma_leq_quorums(state.servers, state.linearization_queue.watermark());

                    state.commitments.agree_commitment(&commitment);

                    let tracked (mut register, _view) = GhostVarAuth::<Option<u64>>::new(None);
                    let tracked resource = state.linearization_queue.apply_linearizers_up_to(&mut state.register, exec_ts);

                    if exec_ts > old_watermark {
                        state.servers.lemma_quorum_lb(quorum, exec_ts);
                        assert(state.linearization_queue.watermark() == exec_ts);
                    } else {
                        assert(old_watermark == state.linearization_queue.watermark());
                    }

                    comp = state.linearization_queue.extract_write_completion(token, resource);

                    // XXX: load bearing
                    assert(state.linearization_queue.known_timestamps() == old_known);
                }

                exec_comp = Tracked(comp);

                // XXX: debug assert
                assert(state.inv());
            });

            Ok(exec_comp)
        }
    }
}

pub proof fn lemma_inv<Pool, C, ML, RL>(c: AbdPool<Pool, ML, RL>) where
    Pool: ConnectionPool<C = C>,
    C: Channel<R = Response, S = Request, Id = (u64, u64)>,
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    ensures
        c._inv() <==> c.inv(),
{
}

pub proof fn lemma_watermark_contradiction<ML, RL>(
    tracked token_res: Result<LinWriteToken<ML>, InsertError<ML, RL>>,
    timestamp: Timestamp,
    lin: ML,
    op: RegisterWrite,
    tracked state: &invariants::State<ML, RL>,
    tracked quorum: Quorum,
) -> (tracked tok: LinWriteToken<ML>) where
    ML: MutLinearizer<RegisterWrite>,
    RL: ReadLinearizer<RegisterRead>,

    requires
        state.inv(),
        state.servers.valid_quorum(quorum),
        state.servers.quorum_timestamp(quorum) < timestamp,
        token_res is Ok ==> {
            let tok = token_res->Ok_0;
            &&& tok.key() == timestamp
            &&& tok.value().lin == lin
            &&& tok.value().op == op
            &&& tok.id() == state.linearization_queue.write_token_id()
        },
        token_res is Err ==> ({
            let err = token_res->Err_0;
            let watermark_lb = token_res->Err_0->w_watermark_lb;
            &&& err is WriteWatermarkContradiction
            &&& timestamp <= watermark_lb@.timestamp()
            &&& watermark_lb.loc() == state.linearization_queue.watermark_id()
            &&& watermark_lb@ is LowerBound
        }),
    ensures
        tok == token_res->Ok_0,
        tok.key() == timestamp,
        tok.value().lin == lin,
        tok.value().op == op,
        tok.id() == state.linearization_queue.write_token_id(),
        token_res is Ok,
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
        state.linearization_queue.lemma_watermark_lb(&mut watermark_lb);
        assert(watermark_lb@.timestamp() <= state.linearization_queue.watermark());
        // curr_watermark <= quorum.timestamp() (forall valid quorums)
        assert(state.linearization_queue.watermark() <= state.servers.quorum_timestamp(quorum));
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
