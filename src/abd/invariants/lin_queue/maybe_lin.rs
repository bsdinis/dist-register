use crate::abd::invariants::logatom::{RegisterRead, RegisterWrite};
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::{MutLinearizer, ReadLinearizer};
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub enum MaybeLinearized<L, C, E, Op> {
    Linearizer { lin: L, ghost op: Op, ghost timestamp: Timestamp },
    Completion {
        // is GhostVar<Option<u64>>
        completion: C,
        ghost exec_res: E,
        ghost op: Op,
        ghost timestamp: Timestamp,
        ghost lin: L,
    },
}

pub type MaybeWriteLinearized<ML, MC> = MaybeLinearized<ML, MC, (), RegisterWrite>;

pub type MaybeReadLinearized<RL, RC> = MaybeLinearized<RL, RC, Option<u64>, RegisterRead>;

impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML, ML::Completion, (), RegisterWrite> {
    pub proof fn linearizer(
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeWriteLinearized::<ML, ML::Completion>::Linearizer {
                lin,
                op,
                timestamp,
            }),
            result.inv(),
    {
        MaybeWriteLinearized::Linearizer { lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.namespaces().finite()
        &&& self is Linearizer ==> self.lin().pre(self.op())
        &&& self is Completion ==> self.lin().post(self.op(), (), self->completion)
    }

    /*
    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            self.inv(),
            old(register).id() == self.op().id,
        ensures
            r.inv(),
            self.op() == r.op(),
            self.timestamp() == r.timestamp(),
            self.lin() == r.lin(),
            old(register).id() == register.id(),
            resolved_timestamp >= self.timestamp() ==> r is Completion,
        opens_invariants
            self.namespaces()
    {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp } if timestamp <= resolved_timestamp => {
                    let ghost lin_copy = lin;
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Completion { completion, timestamp, lin: lin_copy, op }
            } ,
            other => other
        }
    }
    */
    pub open spec fn lin(self) -> ML {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin,
            MaybeLinearized::Completion { lin, .. } => lin,
        }
    }

    pub open spec fn op(self) -> RegisterWrite {
        match self {
            MaybeLinearized::Linearizer { op, .. } => op,
            MaybeLinearized::Completion { op, .. } => op,
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeLinearized::Completion { timestamp, .. } => timestamp,
        }
    }

    pub open spec fn namespaces(self) -> Set<int> {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeLinearized::Completion { .. } => Set::empty(),
        }
    }

    pub proof fn tracked_extract_completion(tracked self) -> (tracked r: ML::Completion)
        requires
            self is Completion,
            self.inv(),
        ensures
            self->completion == r,
    {
        match self {
            MaybeLinearized::Completion { completion, .. } => completion,
            _ => proof_from_false(),
        }
    }
}

impl<RL: ReadLinearizer<RegisterRead>> MaybeLinearized<
    RL,
    RL::Completion,
    Option<u64>,
    RegisterRead,
> {
    pub proof fn linearizer(
        tracked lin: RL,
        op: RegisterRead,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (MaybeLinearized::<
                RL,
                RL::Completion,
                Option<u64>,
                RegisterRead,
            >::Linearizer { lin, op, timestamp }),
            result.inv(),
    {
        MaybeLinearized::Linearizer { lin, op, timestamp }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.namespaces().finite()
        &&& self is Linearizer ==> self.lin().pre(self.op())
        &&& self is Completion ==> self.lin().post(self.op(), self->exec_res, self->completion)
    }

    /*
    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            self.inv(),
            old(register).id() == self.op().id,
        ensures
            r.inv(),
            self.op() == r.op(),
            self.timestamp() == r.timestamp(),
            self.lin() == r.lin(),
            old(register).id() == register.id(),
            resolved_timestamp >= self.timestamp() ==> r is Completion,
        opens_invariants
            self.namespaces()
    {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp } if timestamp <= resolved_timestamp => {
                    let ghost lin_copy = lin;
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Completion { completion, timestamp, lin: lin_copy, op }
            } ,
            other => other
        }
    }
    */
    pub open spec fn lin(self) -> RL {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin,
            MaybeLinearized::Completion { lin, .. } => lin,
        }
    }

    pub open spec fn op(self) -> RegisterRead {
        match self {
            MaybeLinearized::Linearizer { op, .. } => op,
            MaybeLinearized::Completion { op, .. } => op,
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeLinearized::Completion { timestamp, .. } => timestamp,
        }
    }

    pub open spec fn namespaces(self) -> Set<int> {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeLinearized::Completion { .. } => Set::empty(),
        }
    }

    pub proof fn tracked_extract_completion(tracked self) -> (tracked r: RL::Completion)
        requires
            self is Completion,
            self.inv(),
        ensures
            self->completion == r,
    {
        match self {
            MaybeLinearized::Completion { completion, .. } => completion,
            _ => proof_from_false(),
        }
    }
}

} // verus!
