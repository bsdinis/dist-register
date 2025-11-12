use crate::abd::invariants::lin_queue::maybe_lin::MaybeLinearized;
use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::invariants::ClientToken;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

use vstd::logatom::MutLinearizer;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct Completed<ML: MutLinearizer<RegisterWrite>> {
    // is GhostVar<Option<u64>>
    pub completion: ML::Completion,
    pub client_token: ClientToken,
    pub ghost lin: ML,
    pub ghost op: RegisterWrite,
    pub ghost timestamp: Timestamp,
}

impl<ML: MutLinearizer<RegisterWrite>> Completed<ML> {
    pub proof fn new(
        tracked completion: ML::Completion,
        tracked client_token: ClientToken,
        lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (tracked r: Self)
        requires
            lin.post(op, (), completion),
            timestamp.client_id == client_token@,
        ensures
            r.inv(),
            r == (Completed { completion, client_token, lin, op, timestamp }),
    {
        Completed {
            completion,
            client_token,
            lin,
            op,
            timestamp
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.lin.post(self.op, (), self.completion)
        &&& self.timestamp.client_id == self.client_token@
    }

    pub proof fn maybe(tracked self) -> (tracked r: (MaybeLinearized<ML>, ClientToken))
        requires
            self.inv()
        ensures
            r.0.inv(),
            r.0.timestamp().client_id == r.1@,
            r.0 == (MaybeLinearized::Completion {
                completion: self.completion,
                lin: self.lin,
                op: self.op,
                timestamp: self.timestamp,
            }),
            r.1 == self.client_token
    {
        (MaybeLinearized::Completion {
            completion: self.completion,
            lin: self.lin,
            op: self.op,
            timestamp: self.timestamp,
        }, self.client_token)
    }
}

}
