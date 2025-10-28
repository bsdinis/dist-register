use vstd::tokens::map::GhostMapAuth;
use vstd::tokens::map::GhostSubmap;

use vstd::prelude::*;

verus! {

pub type ClientTokenAuth = GhostMapAuth<u64, ()>;

pub struct ClientToken {
    pub submap: GhostSubmap<u64, ()>,
}

impl ClientToken {
    pub proof fn empty(id: int) -> (tracked r: Self)
        ensures r.id() == id
    {
        ClientToken { submap: GhostSubmap::empty(id) }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.submap@.len() == 1
        &&& !self.submap@.is_empty() // This is not implied by len == 1
        &&& self.submap@.dom().finite()
    }

    pub open spec fn id(self) -> int {
        self.submap.id()
    }

    pub open spec fn client_id(self) -> u64
        recommends self.inv()
    {
        self.submap@.dom().choose()
    }

    pub proof fn lemma_dom(self)
        requires
            self.inv(),
        ensures
            self.submap@.dom() == set![self.client_id()]
    {
        let client_id = self.client_id();
        let target_dom = set![client_id];

        assert(self.submap@.dom().len() == 1);
        assert(target_dom.len() == 1);

        assert(self.submap@.dom().finite());
        assert(target_dom.finite());

        assert(self.submap@.dom().contains(client_id));
        assert(target_dom.contains(client_id));

        assert(self.submap@.dom().remove(client_id).len() == 0);
        assert(target_dom.remove(client_id).len() == 0);

        assert(self.submap@.dom() =~= target_dom);
    }

    pub proof fn agree(tracked &self, tracked token_auth: &ClientTokenAuth)
        requires
            self.id() == token_auth.id(),
            self.inv(),
        ensures
            token_auth@.contains_key(self.client_id())
    {
        self.submap.agree(token_auth);
        // XXX: load bearing assert
        assert(self.submap@.dom() <= token_auth@.dom());
    }
}

}
