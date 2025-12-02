#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::maybe_lin::MaybeReadLinearized;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::maybe_lin::MaybeWriteLinearized;
use crate::abd::invariants::logatom::{RegisterRead, RegisterWrite};
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct CompletedWrite<ML, MC> {
    pub completion: MC,
    pub token: ClientToken,
    pub op: RegisterWrite,
    pub ghost lin: ML,
    pub ghost timestamp: Timestamp,
}

pub struct CompletedRead<RL, RC> {
    pub completion: RC,
    pub op: RegisterRead,
    pub ghost lin: RL,
    pub ghost value: Option<u64>,
    pub ghost timestamp: Timestamp,
}

impl<ML: MutLinearizer<RegisterWrite>> CompletedWrite<ML, ML::Completion> {
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
            r == (CompletedWrite { completion, token, lin, op, timestamp }),
    {
        CompletedWrite { completion, token, lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
        &&& self.timestamp.client_id == self.token@
    }

    pub proof fn maybe(tracked self) -> (tracked r: (
        MaybeWriteLinearized<ML, ML::Completion>,
        ClientToken,
    ))
        requires
            self.inv(),
        ensures
            r.0.inv(),
            r.0.timestamp().client_id == r.1@,
            r.0 == (MaybeWriteLinearized::Completion {
                completion: self.completion,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 == self.token,
    {
        (
            MaybeWriteLinearized::Completion {
                completion: self.completion,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            },
            self.token,
        )
    }
}

impl<RL: ReadLinearizer<RegisterRead>> CompletedRead<RL, RL::Completion> {
    pub proof fn new(
        tracked completion: RL::Completion,
        tracked op: RegisterRead,
        lin: RL,
        value: Option<u64>,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, value, completion),
        ensures
            r.inv(),
            r == (CompletedRead { completion, value, lin, op, timestamp }),
    {
        CompletedRead { completion, value, lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, self.value, self.completion)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeReadLinearized<RL, RL::Completion>)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeReadLinearized::<RL, RL::Completion>::Completion {
                completion: self.completion,
                op: self.op,
                lin: self.lin,
                value: self.value,
            }),
    {
        MaybeReadLinearized::Completion {
            completion: self.completion,
            op: self.op,
            lin: self.lin,
            value: self.value,
        }
    }
}

} // verus!
