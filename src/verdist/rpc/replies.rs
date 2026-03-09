use std::collections::BTreeMap;

use crate::verdist::network::error::TryRecvError;
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub trait ReplyAccumulator<ChanId, Pred>: Sized where Pred: InvariantPredicate<Pred, Self> {
    /// Type that is accumulated
    type T;

    fn insert(&mut self, pred: Ghost<Pred>, id: ChanId, reply: Self::T)
        requires
            Pred::inv(pred@, *old(self)),
        ensures
            Pred::inv(pred@, *self),
            self.spec_n_replies() == old(self).spec_n_replies() + 1,
        no_unwind
    ;

    spec fn spec_n_replies(self) -> nat;

    fn n_replies(&self) -> (r: usize)
        ensures
            r == self.spec_n_replies(),
    ;
}

pub struct Replies<ChanId, Pred, R, A> where
    ChanId: Ord,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<ChanId, Pred>,
 {
    pred: Ghost<Pred>,
    reply_accum: A,
    n_replies: usize,
    n_received: usize,
    invalid_replies: BTreeMap<ChanId, R>,
    errors: BTreeMap<ChanId, TryRecvError>,
}

impl<ChanId, Pred, R, A> Replies<ChanId, Pred, R, A> where
    ChanId: Ord,
    Pred: InvariantPredicate<Pred, A>,
    A: ReplyAccumulator<ChanId, Pred>,
 {
    pub fn new(pred: Ghost<Pred>, accum: A) -> (r: Self)
        requires
            Pred::inv(pred@, accum),
            accum.spec_n_replies() == 0,
            vstd::laws_cmp::obeys_cmp_spec::<ChanId>(),
        ensures
            r.spec_len() == 0,
            r.pred() == pred@,
    {
        Replies {
            pred,
            reply_accum: accum,
            invalid_replies: BTreeMap::new(),
            errors: BTreeMap::new(),
            n_replies: 0,
            n_received: 0,
        }
    }

    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.spec_len() + self.invalid_replies.len() as nat + self.errors.len() as nat
            == self.n_received as nat
        &&& self.spec_len() == self.n_replies as nat
        &&& vstd::laws_cmp::obeys_cmp_spec::<ChanId>()
        &&& Pred::inv(self.pred(), self.reply_accum)
    }

    pub fn lemma_pred(&self)
        ensures
            Pred::inv(self.pred(), self.accumulator()),
    {
        proof {
            use_type_invariant(self);
        }
    }

    pub closed spec fn pred(self) -> Pred {
        self.pred@
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r as nat == self.spec_len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.n_replies
    }

    pub closed spec fn spec_len(self) -> (r: nat) {
        self.reply_accum.spec_n_replies()
    }

    pub fn n_received(&self) -> usize {
        self.n_received
    }

    pub closed spec fn accumulator(self) -> A {
        self.reply_accum
    }

    pub fn into_accumulator(self) -> (r: A)
        ensures
            r.spec_n_replies() == self.spec_len(),
            r == self.accumulator(),
    {
        self.reply_accum
    }

    pub closed spec fn spec_invalid_replies(self) -> Map<ChanId, R> {
        self.invalid_replies@
    }

    pub fn invalid_replies(&self) -> (r: &BTreeMap<ChanId, R>)
        ensures
            r@ == self.spec_invalid_replies(),
    {
        &self.invalid_replies
    }

    pub fn into_invalid_replies(self) -> (r: BTreeMap<ChanId, R>)
        ensures
            r@ == self.spec_invalid_replies(),
    {
        self.invalid_replies
    }

    pub closed spec fn spec_errors(self) -> (r: Map<ChanId, TryRecvError>) {
        self.errors@
    }

    pub fn errors(&self) -> (r: &BTreeMap<ChanId, TryRecvError>)
        ensures
            r@ == self.spec_errors(),
    {
        &self.errors
    }

    pub fn into_errors(self) -> (r: BTreeMap<ChanId, TryRecvError>)
        ensures
            r@ == self.spec_errors(),
    {
        self.errors
    }

    pub fn insert_reply(&mut self, id: ChanId, v: A::T)
        ensures
            self.spec_len() == old(self).spec_len() + 1,
            self.spec_invalid_replies() == old(self).spec_invalid_replies(),
            self.spec_errors() == old(self).spec_errors(),
            self.pred() == old(self).pred(),
    {
        proof {
            use_type_invariant(&*self);
        }
        Self::insert_reply_helper(
            self.pred,
            &mut self.reply_accum,
            &mut self.n_replies,
            &mut self.n_received,
            id,
            v,
        );
    }

    pub fn insert_invalid_reply(&mut self, id: ChanId, resp: R)
        ensures
            self.accumulator() == old(self).accumulator(),
            self.spec_invalid_replies() == old(self).spec_invalid_replies().insert(id, resp),
            self.spec_errors() == old(self).spec_errors(),
            self.pred() == old(self).pred(),
    {
        proof {
            use_type_invariant(&*self);
        }
        Self::insert_helper(&mut self.invalid_replies, &mut self.n_received, id, resp);
    }

    pub fn insert_error(&mut self, id: ChanId, err: TryRecvError)
        ensures
            self.accumulator() == old(self).accumulator(),
            self.spec_invalid_replies() == old(self).spec_invalid_replies(),
            self.spec_errors() == old(self).spec_errors().insert(id, err),
            self.pred() == old(self).pred(),
    {
        proof {
            use_type_invariant(&*self);
        }
        Self::insert_helper(&mut self.errors, &mut self.n_received, id, err);
    }

    fn insert_reply_helper(
        pred: Ghost<Pred>,
        accum: &mut A,
        n_replies: &mut usize,
        n_received: &mut usize,
        id: ChanId,
        v: A::T,
    )
        requires
            Pred::inv(pred@, *old(accum)),
            old(accum).spec_n_replies() == *old(n_replies),
        ensures
            Pred::inv(pred@, *accum),
            accum.spec_n_replies() == *n_replies,
            old(n_received) - old(accum).spec_n_replies() == n_received - accum.spec_n_replies(),
            accum.spec_n_replies() == old(accum).spec_n_replies() + 1,
            *n_replies == *old(n_replies) + 1,
            *n_received == *old(n_received) + 1,
        no_unwind
    {
        assume(n_received < usize::MAX);  // XXX: integer overflow
        assume(n_replies < usize::MAX);  // XXX: integer overflow

        accum.insert(pred, id, v);
        *n_replies += 1;
        *n_received += 1;
    }

    // This helps bypass the no_unwind requirement on Self, which has a type invariant
    fn insert_helper<K: Ord, V>(map: &mut BTreeMap<K, V>, n_received: &mut usize, k: K, v: V)
        requires
            vstd::laws_cmp::obeys_cmp_spec::<K>(),
        ensures
            old(n_received) - old(map)@.len() == n_received - map@.len(),
            map@ == old(map)@.insert(k, v),
            *n_received == *old(n_received) + 1,
        no_unwind
    {
        broadcast use vstd::std_specs::btree::group_btree_axioms;

        assume(n_received < usize::MAX);  // XXX: integer overflow
        assume(!map@.contains_key(k));  // TODO: where does this come from?!

        map.insert(k, v);
        *n_received += 1;
    }
}

} // verus!
