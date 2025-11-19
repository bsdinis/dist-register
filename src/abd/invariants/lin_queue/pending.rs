#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::Completed;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::CompletedRead;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::CompletedWrite;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeLinearized;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeReadLinearized;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeWriteLinearized;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;

use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Pending<ML, Op, Tok> {
    pub lin: ML,
    pub token: Tok,
    pub op: Op,
    pub ghost timestamp: Timestamp,
}

pub type PendingWrite<ML> = Pending<ML, RegisterWrite, ClientToken>;

pub type PendingRead<RL> = Pending<RL, RegisterRead, ()>;

impl<ML: MutLinearizer<RegisterWrite>> Pending<ML, RegisterWrite, ClientToken> {
    pub proof fn new(
        tracked lin: ML,
        tracked token: ClientToken,
        tracked op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            timestamp.client_id == token@,
        ensures
            result == (Pending { lin, token, op, timestamp }),
            result.inv(),
    {
        Pending { lin, token, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
        &&& self.timestamp.client_id == self.token@
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: Completed<ML, ML::Completion, (), RegisterWrite, ClientToken>)
        requires
            self.inv(),
            old(register).id() == self.op.id,
            timestamp >= self.timestamp,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            self.token == r.token,
            old(register).id() == register.id(),
            register@ == r.op.new_value,
        opens_invariants self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        CompletedWrite::new(completion, self.token, lin_copy, self.op, self.timestamp)
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
            r.0 == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 == self.token,
    {
        (
            MaybeWriteLinearized::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            },
            self.token,
        )
    }
}

impl<RL: ReadLinearizer<RegisterRead>> Pending<RL, RegisterRead, ()> {
    pub proof fn new(
        tracked lin: RL,
        tracked op: RegisterRead,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (Pending { lin, token: (), op, timestamp }),
            result.inv(),
    {
        Pending { lin, token: (), op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &GhostVarAuth<Option<u64>>,
        exec_res: Option<u64>,
        timestamp: Timestamp,
    ) -> (tracked r: Completed<RL, RL::Completion, Option<u64>, RegisterRead, ()>)
        requires
            self.inv(),
            register.id() == self.op.id,
            timestamp >= self.timestamp,
            register@ == &exec_res,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            self.token == r.token,
            exec_res == r.exec_res,
        opens_invariants self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, &exec_res);
        CompletedRead::new(completion, exec_res, lin_copy, self.op, self.timestamp)
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
            r == (MaybeReadLinearized::<RL, RL::Completion>::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeReadLinearized::Linearizer { lin: self.lin, op: self.op, timestamp: self.timestamp }
    }
}

} // verus!
