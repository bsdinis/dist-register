#[allow(unused_imports)]
use verus_builtin::*;
use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVar;
#[allow(unused_imports)]
use vstd::tokens::frac::GhostVarAuth;

use crate::abd::client::logatom::RegisterWrite;

verus! {

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
