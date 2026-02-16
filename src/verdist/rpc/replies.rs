#![allow(dead_code)]
use std::collections::BTreeMap;

use crate::verdist::network::error::TryRecvError;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub struct Replies<ChanId, T, R, Pred> where
    Pred: InvariantPredicate<Pred, RepliesView<ChanId, T, R>>,
    ChanId: Ord,
 {
    replies: BTreeMap<ChanId, T>,
    invalid_replies: BTreeMap<ChanId, R>,
    errors: BTreeMap<ChanId, TryRecvError>,
    pred: Ghost<Pred>,
}

#[verifier::reject_recursive_types(ChanId)]
pub struct RepliesView<ChanId, T, R> {
    pub replies: Map<ChanId, T>,
    pub invalid_replies: Map<ChanId, R>,
    pub errors: Map<ChanId, TryRecvError>,
}

impl<ChanId, T, R> RepliesView<ChanId, T, R> {
    pub open spec fn empty() -> Self {
        RepliesView { replies: Map::empty(), invalid_replies: Map::empty(), errors: Map::empty() }
    }
}

impl<ChanId, T, R, Pred> Replies<ChanId, T, R, Pred> where
    Pred: InvariantPredicate<Pred, RepliesView<ChanId, T, R>>,
    ChanId: Ord,
 {
    pub closed spec fn view(self) -> RepliesView<ChanId, T, R> {
        RepliesView {
            replies: self.replies@,
            invalid_replies: self.invalid_replies@,
            errors: self.errors@,
        }
    }

    pub fn new(pred: Ghost<Pred>) -> (r: Self)
        requires
            Pred::inv(pred@, RepliesView::empty()),
            vstd::std_specs::btree::obeys_key_model::<ChanId>(),
        ensures
            r@ == RepliesView::<ChanId, T, R>::empty(),
    {
        Replies {
            replies: BTreeMap::new(),
            invalid_replies: BTreeMap::new(),
            errors: BTreeMap::new(),
            pred,
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.replies.len() + self.invalid_replies.len() + self.errors.len() <= usize::MAX
        &&& Pred::inv(self.pred@, self@)
        &&& vstd::std_specs::btree::obeys_key_model::<ChanId>()
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self.spec_len(),
    {
        self.replies.len()
    }

    pub closed spec fn spec_len(self) -> (r: usize) {
        self.replies.len()
    }

    pub fn n_received(&self) -> usize {
        proof {
            use_type_invariant(self);
        }
        self.replies.len() + self.invalid_replies.len() + self.errors.len()
    }

    pub fn replies(&self) -> (r: &BTreeMap<ChanId, T>)
        ensures
            r.len() == self.spec_len(),
    {
        &self.replies
    }

    pub fn into_replies(self) -> (r: BTreeMap<ChanId, T>)
        ensures
            r.len() == self.spec_len(),
    {
        self.replies
    }

    pub fn invalid_replies(&self) -> &BTreeMap<ChanId, R> {
        &self.invalid_replies
    }

    pub fn into_invalid_replies(self) -> BTreeMap<ChanId, R> {
        self.invalid_replies
    }

    pub fn errors(&self) -> &BTreeMap<ChanId, TryRecvError> {
        &self.errors
    }

    pub fn into_errors(self) -> BTreeMap<ChanId, TryRecvError> {
        self.errors
    }

    pub fn insert_reply(&mut self, id: ChanId, v: T)
        ensures
            self@.replies == old(self)@.replies.insert(id, v),
            self@.invalid_replies == old(self)@.invalid_replies,
            self@.errors == old(self)@.errors,
    {
        proof {
            use_type_invariant(&*self);
        }
        // XXX: integer overflow
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        assume(Pred::inv(
            self.pred@,
            RepliesView {
                replies: self@.replies.insert(id, v),
                invalid_replies: self@.invalid_replies,
                errors: self@.errors,
            },
        ));
        Self::insert_helper(&mut self.replies, id, v);
    }

    pub fn insert_invalid_reply(&mut self, id: ChanId, resp: R)
        ensures
            self@.replies == old(self)@.replies,
            self@.invalid_replies == old(self)@.invalid_replies.insert(id, resp),
            self@.errors == old(self)@.errors,
    {
        proof {
            use_type_invariant(&*self);
        }
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        assume(Pred::inv(
            self.pred@,
            RepliesView {
                replies: self@.replies,
                invalid_replies: self@.invalid_replies.insert(id, resp),
                errors: self@.errors,
            },
        ));
        Self::insert_helper(&mut self.invalid_replies, id, resp);
    }

    pub fn insert_error(&mut self, id: ChanId, resp: TryRecvError)
        ensures
            self@.replies == old(self)@.replies,
            self@.invalid_replies == old(self)@.invalid_replies,
            self@.errors == old(self)@.errors.insert(id, resp),
    {
        proof {
            use_type_invariant(&*self);
        }
        assume(self.replies.len() + self.invalid_replies.len() + self.errors.len() < usize::MAX);
        assume(Pred::inv(
            self.pred@,
            RepliesView {
                replies: self@.replies,
                invalid_replies: self@.invalid_replies,
                errors: self@.errors.insert(id, resp),
            },
        ));
        Self::insert_helper(&mut self.errors, id, resp);
    }

    // This helps bypass the no_unwind requirement on Self, which has a type invariant
    fn insert_helper<K: Ord, V>(map: &mut BTreeMap<K, V>, k: K, v: V)
        requires
            vstd::std_specs::btree::obeys_key_model::<K>(),
        ensures
            map@ == old(map)@.insert(k, v),
        no_unwind
    {
        broadcast use vstd::std_specs::btree::group_btree_axioms;

        map.insert(k, v);
    }
}

} // verus!
