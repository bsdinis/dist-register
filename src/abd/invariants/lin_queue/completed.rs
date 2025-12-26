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
    completion: MC,
    op: RegisterWrite,
    commitment: WriteCommitment,
    ghost lin: ML,
    ghost timestamp: Timestamp,
}

pub struct CompletedRead<RL, RC> {
    completion: RC,
    op: RegisterRead,
    ghost lin: RL,
    ghost value: Option<u64>,
    ghost timestamp: Timestamp,
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
            r.lin() == lin,
            r.completion() == completion,
            r.op() == op,
            r.timestamp() == timestamp,
            r.commitment() == commitment,
    {
        CompletedWrite { completion, op, commitment, lin, timestamp }
    }

    pub closed spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
        &&& self.commitment.key() == self.timestamp
        &&& self.commitment.value() == self.op.new_value
    }

    pub closed spec fn lin(self) -> ML {
        self.lin
    }

    pub closed spec fn completion(self) -> ML::Completion {
        self.completion
    }

    pub closed spec fn op(self) -> RegisterWrite {
        self.op
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub open spec fn value(self) -> Option<u64> {
        self.op().new_value
    }

    pub closed spec fn commitment(self) -> WriteCommitment {
        self.commitment
    }

    pub open spec fn register_id(self) -> int {
        self.op().id@
    }

    pub open spec fn commitment_id(self) -> int {
        self.commitment().id()
    }

    pub proof fn duplicate_commitment(tracked &mut self) -> (tracked r: WriteCommitment)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.timestamp() == old(self).timestamp(),
            self.value() == old(self).value(),
            self.lin() == old(self).lin(),
            self.op() == old(self).op(),
            self.commitment()@ == old(self).commitment()@,
            self.commitment().id() == old(self).commitment().id(),
            self.completion() == old(self).completion(),
            r.id() == self.commitment_id(),
            r.key() == self.timestamp(),
            r.value() == self.value()
    {
        self.commitment.duplicate()
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeWriteLinearized<ML, ML::Completion>)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeWriteLinearized::Completion {
                completion: self.completion(),
                lin: self.lin(),
                op: self.op(),
                timestamp: self.timestamp(),
            }),
    {
        MaybeWriteLinearized::Completion {
            completion: self.completion,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }

    pub proof fn tracked_completion(tracked self) -> (tracked r: ML::Completion)
        requires
            self.inv(),
        ensures
            r == self.completion(),
            self.lin().post(self.op(), (), self.completion())
    {
        self.completion
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
            r.lin() == lin,
            r.completion() == completion,
            r.op() == op,
            r.timestamp() == timestamp,
            r.value() == value,
    {
        CompletedRead { completion, value, lin, op, timestamp }
    }

    pub closed spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, self.value, self.completion)
    }

    pub closed spec fn lin(self) -> RL {
        self.lin
    }

    pub closed spec fn completion(self) -> RL::Completion {
        self.completion
    }

    pub closed spec fn op(self) -> RegisterRead {
        self.op
    }

    pub closed spec fn timestamp(self) -> Timestamp {
        self.timestamp
    }

    pub closed spec fn value(self) -> Option<u64> {
        self.value
    }

    pub open spec fn register_id(self) -> int {
        self.op().id@
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeReadLinearized<RL, RL::Completion>)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeReadLinearized::<RL, RL::Completion>::Completion {
                completion: self.completion(),
                op: self.op(),
                lin: self.lin(),
                value: self.value(),
            }),
    {
        MaybeReadLinearized::Completion {
            completion: self.completion,
            op: self.op,
            lin: self.lin,
            value: self.value,
        }
    }

    pub proof fn tracked_completion(tracked self) -> (tracked r: RL::Completion)
        requires
            self.inv(),
        ensures
            r == self.completion(),
            self.lin().post(self.op(), self.value(), self.completion())
    {
        self.completion
    }
}

} // verus!
