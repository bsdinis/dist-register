use crate::abd::invariants::lin_queue::maybe_lin::MaybeLinearized;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Completed<ML: MutLinearizer<RegisterWrite>> {
    // is GhostVar<Option<u64>>
    pub completion: ML::Completion,
    pub ghost lin: ML,
    pub ghost op: RegisterWrite,
    pub ghost timestamp: Timestamp,
}

impl<ML: MutLinearizer<RegisterWrite>> Completed<ML> {
    pub proof fn new(
        tracked completion: ML::Completion,
        lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            lin.post(op, (), completion)
        ensures
            r.inv(),
            r == (Completed { completion, lin, op, timestamp }),
    {
        Completed {
            completion,
            lin,
            op,
            timestamp
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
    }

    pub proof fn maybe(tracked self) -> (tracked r: MaybeLinearized<ML>)
        requires
            self.inv()
        ensures
            r.inv(),
            r == (MaybeLinearized::Comp {
                completion: self.completion,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
    {
        MaybeLinearized::Comp {
            completion: self.completion,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }
    }
}

}
