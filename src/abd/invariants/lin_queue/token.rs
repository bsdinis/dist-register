use crate::abd::invariants::logatom::RegisterWrite;
use crate::abd::proto::Timestamp;

use vstd::logatom::MutLinearizer;
use vstd::tokens::map::GhostSubmap;

use vstd::prelude::*;

verus! {

pub struct LinToken<ML: MutLinearizer<RegisterWrite>> {
    pub submap: GhostSubmap<Timestamp, (ML, RegisterWrite)>,
}

impl<ML: MutLinearizer<RegisterWrite>> LinToken<ML> {
    pub open spec fn inv(self) -> bool {
        &&& self.submap@.len() == 1
        &&& self.submap@.dom().finite()
    }

    pub open spec fn id(self) -> int {
        self.submap.id()
    }

    pub open spec fn timestamp(self) -> Timestamp
        recommends self.inv()
    {
        self.submap@.dom().choose()
    }

    pub open spec fn lin(self) -> ML
        recommends self.inv()
    {
        self.submap@[self.timestamp()].0
    }

    pub open spec fn op(self) -> RegisterWrite
        recommends self.inv()
    {
        self.submap@[self.timestamp()].1
    }

    pub proof fn lemma_dom(self)
        requires
            self.inv(),
        ensures
            self.submap@.dom() == set![self.timestamp()]
    {
        let timestamp = self.timestamp();
        let target_dom = set![timestamp];

        assert(self.submap@.dom().len() == 1);
        assert(target_dom.len() == 1);

        assert(self.submap@.dom().finite());
        assert(target_dom.finite());

        assert(self.submap@.dom().contains(timestamp));
        assert(target_dom.contains(timestamp));

        assert(self.submap@.dom().remove(timestamp).len() == 0);
        assert(target_dom.remove(timestamp).len() == 0);

        assert(self.submap@.dom() =~= target_dom);
    }
}

}
