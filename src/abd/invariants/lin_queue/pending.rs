use crate::abd::invariants::committed_to::WriteCommitment;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::CompletedRead;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::CompletedWrite;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeReadLinearized;
#[allow(unused_imports)]
use crate::abd::invariants::lin_queue::MaybeWriteLinearized;
use crate::abd::invariants::logatom::RegisterRead;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;

use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct PendingWrite<ML> {
    pub lin: ML,
    pub op: RegisterWrite,
    pub commitment: WriteCommitment,
    pub ghost timestamp: Timestamp,
}

pub struct PendingRead<RL> {
    pub lin: RL,
    pub op: RegisterRead,
    pub ghost value: Option<u64>,
}

impl<ML: MutLinearizer<RegisterWrite>> PendingWrite<ML> {
    pub proof fn new(
        tracked lin: ML,
        tracked op: RegisterWrite,
        tracked commitment: WriteCommitment,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            commitment.key() == timestamp,
            commitment.value() == op.new_value,
        ensures
            result == (PendingWrite { lin, op, commitment, timestamp }),
            result.inv(),
    {
        PendingWrite { lin, op, commitment, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
        &&& self.commitment.key() == self.timestamp
        &&& self.commitment.value() == self.op.new_value
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: CompletedWrite<ML, ML::Completion>)
        requires
            self.inv(),
            old(register).id() == self.op.id,
            timestamp >= self.timestamp,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            self.commitment == r.commitment,
            old(register).id() == register.id(),
            register@ == r.op.new_value,
        opens_invariants self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        CompletedWrite::new(completion, self.op, self.commitment, lin_copy, self.timestamp)
    }

    // TODO(maybe): add commitment to MaybeWriteLinearized
    pub proof fn maybe(tracked self) -> (tracked r:
        MaybeWriteLinearized<ML, ML::Completion>
    )
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeWriteLinearized::Linearizer {
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }
}

impl<RL: ReadLinearizer<RegisterRead>> PendingRead<RL> {
    pub proof fn new(
        tracked lin: RL,
        tracked op: RegisterRead,
        value: Option<u64>,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (PendingRead { lin, op, value }),
            result.inv(),
    {
        PendingRead { lin, op, value }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: CompletedRead<RL, RL::Completion>)
        requires
            self.inv(),
            register.id() == self.op.id,
            register@ == &self.value,
        ensures
            r.inv(),
            self.op == r.op,
            self.value == r.value,
            self.lin == r.lin,
            r.timestamp == timestamp,
        opens_invariants self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, &self.value);
        CompletedRead::new(completion, self.op, lin_copy, self.value, timestamp)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeReadLinearized<RL, RL::Completion>)
        requires
            self.inv(),
        ensures
            r.inv(),
            r == (MaybeReadLinearized::<RL, RL::Completion>::Linearizer {
                lin: self.lin,
                op: self.op,
                value: self.value,
            }),
    {
        MaybeReadLinearized::Linearizer { lin: self.lin, op: self.op, value: self.value }
    }
}

} // verus!
