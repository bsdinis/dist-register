use crate::abd::invariants::lin_queue::Completed;
use crate::abd::invariants::lin_queue::MaybeLinearized;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Pending<ML, Op> {
    pub lin: ML,
    pub client_token: ClientToken,
    pub ghost op: Op,
    pub ghost timestamp: Timestamp,
}

impl<ML: MutLinearizer<RegisterWrite>> Pending<ML, RegisterWrite> {
    pub proof fn new(
        tracked lin: ML,
        tracked client_token: ClientToken,
        op: RegisterWrite,
        timestamp: Timestamp,
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            timestamp.client_id == client_token@,
        ensures
            result == (Pending { lin, client_token, op, timestamp }),
            result.inv()
    {
        Pending {
            lin,
            client_token,
            op,
            timestamp,
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.namespaces().finite()
        &&& self.lin.pre(self.op)
        &&& self.timestamp.client_id == self.client_token@
    }

    pub proof fn apply_linearizer(tracked self,
        tracked register: &mut GhostVarAuth<Option<u64>>,
        resolved_timestamp: Timestamp
    ) -> (tracked r: Completed<ML, ML::Completion, RegisterWrite>)
        requires
            self.inv(),
            old(register).id() == self.op.id,
            resolved_timestamp >= self.timestamp,
        ensures
            r.inv(),
            self.op == r.op,
            self.timestamp == r.timestamp,
            self.lin == r.lin,
            self.client_token == r.client_token,
            old(register).id() == register.id(),
        opens_invariants
            self.lin.namespaces()
    {
        let ghost lin_copy = self.lin;
        let tracked completion = self.lin.apply(self.op, register, (), &());
        Completed::new(completion, self.client_token, lin_copy, self.op, self.timestamp)
    }

    pub proof fn maybe(tracked self) -> (tracked r: (MaybeLinearized<ML, ML::Completion, RegisterWrite>, ClientToken))
        requires
            self.inv()
        ensures
            r.0.inv(),
            r.0.timestamp().client_id == r.1@,
            r.0 == (MaybeLinearized::<ML, ML::Completion, RegisterWrite>::Linearizer {
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 == self.client_token,
    {
        (MaybeLinearized::Linearizer {
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }, self.client_token)
    }
}

}
