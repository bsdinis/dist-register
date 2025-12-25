use crate::abd::invariants::committed_to::WriteCommitment;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::maybe_lin::MaybeReadLinearized;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::maybe_lin::MaybeWriteLinearized;
use crate::abd::invariants::logatom::{RegisterRead, RegisterWrite};
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct CompletedWrite<ML, MC> {
    pub completion: MC,
    pub op: RegisterWrite,
    pub commitment: WriteCommitment,
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
        tracked op: RegisterWrite,
        tracked commitment: WriteCommitment,
        lin: ML,
        timestamp: Timestamp,
    ) -> (tracked r: Self)
        requires
            lin.post(op, (), completion),
            commitment.key() == timestamp,
            commitment.value() == op.new_value,
        ensures
            r.inv(),
            r == (CompletedWrite { completion, op, commitment, lin, timestamp }),
    {
        CompletedWrite { completion, op, commitment, lin, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
        &&& self.commitment.key() == self.timestamp
        &&& self.commitment.value() == self.op.new_value
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeWriteLinearized<ML, ML::Completion>)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeWriteLinearized::Completion {
                completion: self.completion,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeWriteLinearized::Completion {
            completion: self.completion,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
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
