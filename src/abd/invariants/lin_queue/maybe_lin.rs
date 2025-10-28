use crate::abd::invariants::client_token::ClientToken;
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
        tracked client_token: ClientToken,
    },
    Comp {
        // is GhostVar<Option<u64>>
        completion: ML::Completion,
        ghost op: RegisterWrite,
        ghost timestamp: Timestamp,
        ghost lin: ML,
        tracked client_token: ClientToken,
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub proof fn linearizer(
        tracked lin: ML,
        op: RegisterWrite,
        timestamp: Timestamp,
        tracked client_token: ClientToken
    ) -> (tracked result: Self)
        requires
            lin.namespaces().finite(),
            lin.pre(op),
            client_token.inv(),
            client_token.client_id() == timestamp.client_id,
        ensures
            result == (MaybeLinearized::Linearizer { lin, op, timestamp, client_token}),
            result.inv()
    {
        MaybeLinearized::Linearizer {
            lin,
            op,
            timestamp,
            client_token,
        }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.namespaces().finite()
        &&& self is Linearizer ==> self.lin().pre(self.op())
        &&& self is Comp ==> self.lin().post(self.op(), (), self->completion)
        &&& self.client_token().inv()
        &&& self.client_token().client_id() == self.timestamp().client_id
    }

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
            self.client_token() == r.client_token(),
            old(register).id() == register.id(),
            resolved_timestamp >= self.timestamp() ==> r is Comp,
        opens_invariants
            self.namespaces()
    {
        match self {
             MaybeLinearized::Linearizer { lin, op, timestamp, client_token } if timestamp <= resolved_timestamp => {
                    let ghost lin_copy = lin;
                    let tracked completion = lin.apply(op, register, (), &());
                    MaybeLinearized::Comp { completion, timestamp, lin: lin_copy, op, client_token }
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

    pub open spec fn client_token(self) -> ClientToken {
        match self {
            MaybeLinearized::Linearizer { client_token, .. } => client_token,
            MaybeLinearized::Comp { client_token, .. } => client_token,
        }
    }

    pub open spec fn namespaces(self) -> Set<int> {
        match self {
            MaybeLinearized::Linearizer { lin, .. } => lin.namespaces(),
            MaybeLinearized::Comp { .. } => Set::empty(),
        }
    }

    pub proof fn tracked_destruct(tracked self) -> (tracked r: (ML::Completion, ClientToken))
        requires
            self is Comp,
            self.inv(),
        ensures
            self->completion == r.0,
            r.1.inv(),
            r.1.client_id() == self.timestamp().client_id,
            r.1.id() == self.client_token().id(),
    {
        match self {
            MaybeLinearized::Comp { completion, client_token, .. } => (completion, client_token),
            _ => proof_from_false()
        }
    }

    pub proof fn tracked_extract_token(tracked self) -> (tracked r: ClientToken)
        requires
            self.inv(),
        ensures
            r.inv(),
            r.client_id() == self.timestamp().client_id,
            r.id() == self.client_token().id(),
    {
        match self {
            MaybeLinearized::Linearizer { client_token, .. } => client_token,
            MaybeLinearized::Comp { client_token, .. } => client_token,
        }
    }
}

}
