#[allow(unused_imports)]
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
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

pub struct WritePerm {
    pub val: Option<u64>,
    pub tracked register: GhostVar<Option<u64>>,
}

impl MutLinearizer<RegisterWrite> for WritePerm {
    type Completion = GhostVar<Option<u64>>;

    open spec fn namespaces(self) -> Set<int> { Set::empty() }

    // TODO: do I not need some better like \exists v: r -> v
    open spec fn pre(self, op: RegisterWrite) -> bool {
        op.id == self.register.id()
    }

    open spec fn post(self, op: RegisterWrite, exec_res: (), completion: Self::Completion) -> bool {
        &&& op.id == self.register.id()
        &&& op.id == completion.id()
        &&& op.new_value == completion@
    }

    proof fn apply(
        tracked self,
        op: RegisterWrite,
        tracked resource: &mut GhostVarAuth<Option<u64>>,
        new_state: (),
        exec_res: &()
    ) -> (tracked result: Self::Completion)
    {
        let tracked mut mself = self;

        resource.update(&mut mself.register, op.new_value);
        mself.register
    }

    proof fn peek(tracked &self, op: RegisterWrite, tracked resource: &GhostVarAuth<Option<u64>>) {}
}

}
