#[allow(unused_imports)]
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVarAuth;

verus! {

pub struct RegisterRead {
    /// resource location
    pub id: Ghost<int>,
}

pub struct RegisterWrite {
    /// resource location
    pub id: Ghost<int>,

    pub new_value: Option<u64>,
}

impl RegisterWrite {
    pub open spec fn spec_clone(&self) -> RegisterWrite {
        RegisterWrite { id: Ghost(self.id@), new_value: self.new_value }
    }
}

impl ReadOperation for RegisterRead {
    type Resource = GhostVarAuth<Option<u64>>;
    type ExecResult = Option<u64>;

    open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.id() == self.id
        &&& r@ == e
    }
}

impl MutOperation for RegisterWrite {
    type Resource = GhostVarAuth<Option<u64>>;
    type ExecResult = ();
    type NewState = ();


    open spec fn requires(
        self,
        pre: Self::Resource,
        new_state: Self::NewState,
        e: Self::ExecResult,
    ) -> bool {
        &&& pre.id() == self.id
    }

    open spec fn ensures(
        self,
        pre: Self::Resource,
        post: Self::Resource,
        new_state: Self::NewState,
    ) -> bool {
        &&& pre.id() == post.id()
        &&& post@ == self.new_value
    }
}

}
