#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::maybe_lin::MaybeLinearized;
use crate::abd::invariants::lin_queue::maybe_lin::MaybeWriteLinearized;
use crate::abd::invariants::logatom::{RegisterRead, RegisterWrite};
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Completed<L, C, E, Op, Tok> {
    // is GhostVar<Option<u64>>
    pub completion: C,
    pub token: Tok,
    pub op: Op,
    pub ghost exec_res: E,
    pub ghost lin: L,
    pub ghost timestamp: Timestamp,
}

pub type CompletedWrite<ML, MC> = Completed<ML, MC, (), RegisterWrite, ClientToken>;

pub type CompletedRead<RL, RC> = Completed<RL, RC, Option<u64>, RegisterRead, ()>;

impl<ML: MutLinearizer<RegisterWrite>> Completed<
    ML,
    ML::Completion,
    (),
    RegisterWrite,
    ClientToken,
> {
    pub proof fn new(
        tracked completion: ML::Completion,
        tracked token: ClientToken,
        lin: ML,
        tracked op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, (), completion),
            timestamp.client_id == token@,
        ensures
            r.inv(),
            r == (Completed { completion, token, exec_res: (), lin, op, timestamp }),
    {
        Completed { completion, token, exec_res: (), lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, self.exec_res, self.completion)
        &&& self.timestamp.client_id == self.token@
    }

    pub proof fn maybe(tracked self) -> (tracked r: (
        MaybeLinearized<ML, ML::Completion, (), RegisterWrite>,
        ClientToken,
    ))
        requires
            self.inv(),
        ensures
            r.0.inv(),
            r.0.timestamp().client_id == r.1@,
            r.0 == (MaybeWriteLinearized::Completion {
                completion: self.completion,
                exec_res: (),
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 == self.token,
    {
        (
            MaybeWriteLinearized::Completion {
                completion: self.completion,
                exec_res: (),
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            },
            self.token,
        )
    }
}

impl<RL: ReadLinearizer<RegisterRead>> Completed<
    RL,
    RL::Completion,
    Option<u64>,
    RegisterRead,
    (),
> {
    pub proof fn new(
        tracked completion: RL::Completion,
        exec_res: Option<u64>,
        lin: RL,
        tracked op: RegisterRead,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, exec_res, completion),
        ensures
            r.inv(),
            r == (Completed { completion, exec_res, token: (), lin, op, timestamp }),
    {
        Completed { completion, exec_res, token: (), lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, self.exec_res, self.completion)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeLinearized<
        RL,
        RL::Completion,
        Option<u64>,
        RegisterRead,
    >)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeLinearized::<RL, RL::Completion, Option<u64>, RegisterRead>::Completion {
                completion: self.completion,
                exec_res: self.exec_res,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeLinearized::Completion {
            completion: self.completion,
            exec_res: self.exec_res,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }
}

} // verus!
