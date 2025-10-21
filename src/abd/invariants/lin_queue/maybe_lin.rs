use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub enum MaybeLinearized<ML: MutLinearizer<RegisterWrite>> {
    Linearizer {
        lin: ML,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
    },
    Comp {
        // is GhostVar<Option<u64>>
        completion: ML::Completion,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
        ghost lin: ML,
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub proof fn linearizer(tracked lin: ML, op: RegisterWrite, timestamp: Timestamp) -> (tracked result: Self)
        ensures
            result == (MaybeLinearized::Linearizer { lin, op, timestamp, })
    {
        MaybeLinearized::Linearizer {
            lin,
            op,
            timestamp,
        }
    }

    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            self is Linearizer ==> self.lin().pre(self.op()),
            old(register).id() == self.op().id,
        ensures
            old(register).id() == register.id(),
        opens_invariants
            self.namespaces()
    {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp, .. } if timestamp < resolved_timestamp => {
                    let ghost lin_copy = lin;
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Comp { completion, timestamp, lin: lin_copy, op }
            } ,
            other => other
        }
    }

    pub open spec fn lin(self) -> ML {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin,
            MaybeLinearized::Comp { lin, .. } => lin,
        }
    }

    pub open spec fn op(self) -> RegisterWrite {
        match self {
            MaybeLinearized::Linearizer { op, .. } => op,
            MaybeLinearized::Comp { op, .. } => op,
        }
    }

    pub open spec fn timestamp(self) -> Timestamp {
        match self {
            MaybeLinearized::Linearizer { timestamp, .. } => timestamp,
            MaybeLinearized::Comp { timestamp, .. } => timestamp,
        }
    }

    pub open spec fn namespaces(self) -> Set<int> {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeLinearized::Comp { .. } => Set::empty(),
        }
    }

    pub proof fn tracked_get_completion(tracked self) -> (tracked r: ML::Completion)
        requires self is Comp,
        ensures self->completion == r
    {
        match self {
            MaybeLinearized::Comp { completion, .. } => completion,
            _ => proof_from_false()
        }
    }
}

}
