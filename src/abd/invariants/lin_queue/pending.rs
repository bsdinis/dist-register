use crate::abd::invariants::committed_to::WriteAllocation;
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

pub enum WriteStatus {
    Allocated { allocation: WriteAllocation },
    Committed { commitment: WriteCommitment },
}

impl WriteStatus {
    pub open spec fn id(self) -> int {
        match self {
            WriteStatus::Allocated { allocation } => allocation.id(),
            WriteStatus::Committed { commitment } => commitment.id(),
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            WriteStatus::Allocated { allocation } => allocation.key(),
            WriteStatus::Committed { commitment } => commitment.key(),
        }
    }

    pub open spec fn value(self) -> Option<u64> {
        match self {
            WriteStatus::Allocated { allocation } => allocation.value(),
            WriteStatus::Committed { commitment } => commitment.value(),
        }
    }

    proof fn allocated(tracked allocation: WriteAllocation) -> (tracked r: WriteStatus)
        ensures
            r is Allocated,
            r->allocation == allocation,
    {
        WriteStatus::Allocated { allocation }
    }

    proof fn commit(tracked self) -> (tracked r: Self)
        ensures
            r is Committed,
            self is Committed ==> r == self,
            self is Allocated ==> {
                &&& r.id() == self.id()
                &&& r.timestamp() == self.timestamp()
                &&& r.value() == self.value()
            },
    {
        let tracked commitment = match self {
            WriteStatus::Allocated { allocation } => allocation.persist(),
            WriteStatus::Committed { commitment } => commitment,
        };

        WriteStatus::Committed { commitment }
    }

    proof fn duplicate(tracked self) -> (tracked r: (Self, WriteCommitment))
        requires
            self is Committed,
        ensures
            r.0.id() == self.id(),
            r.0.timestamp() == self.timestamp(),
            r.0.value() == self.value(),
            r.0 is Committed,
            r.1.id() == r.0.id(),
            r.1.key() == r.0.timestamp(),
            r.1.value() == r.0.value(),
    {
        match self {
            WriteStatus::Committed { mut commitment } => {
                let tracked dup = commitment.duplicate();
                let tracked new_self = WriteStatus::Committed { commitment };
                (new_self, dup)
            },
            WriteStatus::Allocated { .. } => vstd::pervasive::proof_from_false(),
        }
    }

    proof fn tracked_destruct_commitment(tracked self) -> (tracked r: WriteCommitment)
        requires
            self is Committed,
        ensures
            r.id() == self->commitment.id(),
            r@ == self->commitment@,
    {
        match self {
            WriteStatus::Committed { commitment } => commitment,
            WriteStatus::Allocated { .. } => vstd::pervasive::proof_from_false(),
        }
    }

    proof fn tracked_destruct_allocation(tracked self) -> (tracked r: WriteAllocation)
        requires
            self is Allocated,
        ensures
            r.id() == self->allocation.id(),
            r@ == self->allocation@,
    {
        match self {
            WriteStatus::Committed { .. } => vstd::pervasive::proof_from_false(),
            WriteStatus::Allocated { allocation } => allocation,
        }
    }
}

pub struct PendingWrite<ML> {
    pub lin: ML,
    pub op: RegisterWrite,
    pub write_status: WriteStatus,
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
        tracked allocation: WriteAllocation,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            allocation.key() == timestamp,
            allocation.value() == op.new_value,
        ensures
            result == (PendingWrite {
                lin,
                op,
                write_status: WriteStatus::Allocated { allocation },
                timestamp,
            }),
            result.inv(),
    {
        PendingWrite { lin, op, write_status: WriteStatus::Allocated { allocation }, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
        &&& self.write_status.timestamp() == self.timestamp
        &&& self.write_status.value() == self.op.new_value
    }

    pub proof fn commit(tracked self) -> (tracked r: (Self, WriteCommitment))
        requires
            self.inv(),
        ensures
            r.0.inv(),
            r.0.lin == self.lin,
            r.0.op == self.op,
            r.0.timestamp == self.timestamp,
            r.0.write_status is Committed,
            r.0.write_status.id() == self.write_status.id(),
            r.0.write_status.id() == r.1.id(),
            r.0.write_status.timestamp() == r.1.key(),
            r.0.write_status.value() == r.1.value(),
    {
        let tracked PendingWrite { lin, op, write_status, timestamp } = self;
        let tracked (write_status, dup) = write_status.commit().duplicate();
        let tracked pending = PendingWrite { lin, op, write_status, timestamp };
        (pending, dup)
    }

    pub proof fn apply_linearizer(
        tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        timestamp: Timestamp,
    ) -> (tracked r: CompletedWrite<ML, ML::Completion>)
        requires
            self.inv(),
            self.write_status is Committed,
            old(register).id() == self.op.id,
            timestamp >= self.timestamp,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            self.write_status.id() == r.commitment.id(),
            self.write_status.timestamp() == r.commitment.key(),
            self.write_status.value() == r.commitment.value(),
            old(register).id() == register.id(),
            register@ == r.op.new_value,
        opens_invariants self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        CompletedWrite::new(
            completion,
            self.op,
            self.write_status.tracked_destruct_commitment(),
            lin_copy,
            self.timestamp,
        )
    }

    pub proof fn maybe(tracked self) -> (tracked r: (
        MaybeWriteLinearized<ML, ML::Completion>,
        Option<WriteAllocation>,
    ))
        requires
            self.inv(),
        ensures
            r.0.inv(),
            r.0 == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 is Some <==> self.write_status is Allocated,
            r.1 is Some ==> {
                let allocation = r.1->Some_0;
                &&& allocation.id() == self.write_status.id()
                &&& allocation.key() == self.write_status.timestamp()
                &&& allocation.value() == self.write_status.value()
            },
    {
        let tracked maybe = MaybeWriteLinearized::Linearizer {
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        };

        let tracked allocation_opt = if &self.write_status is Allocated {
            let tracked allocation = self.write_status.tracked_destruct_allocation();
            Some(allocation)
        } else {
            None
        };

        (maybe, allocation_opt)
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
