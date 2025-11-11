use crate::abd::invariants::lin_queue::completed::Completed;
use crate::abd::invariants::lin_queue::maybe_lin::MaybeLinearized;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Pending<ML: MutLinearizer<RegisterWrite>> {
    pub lin: ML,
    pub ghost op: RegisterWrite,
    pub ghost timestamp: Timestamp,
}

impl<ML: MutLinearizer<RegisterWrite>> Pending<ML> {
    pub proof fn new(
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
        ensures
            result == (Pending { lin, op, timestamp }),
            result.inv()
    {
        Pending {
            lin,
            op,
            timestamp,
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
    }

    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Completed<ML>)
        requires
            self.inv(),
            old(register).id() == self.op.id,
            resolved_timestamp >= self.timestamp,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            old(register).id() == register.id(),
        opens_invariants
            self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        Completed::new(completion, lin_copy, self.op, self.timestamp)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeLinearized<ML>)
        requires
            self.inv()
        ensures
            r.inv(),
            r == (MaybeLinearized::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeLinearized::Linearizer {
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }
}

}
