use vstd::modes::tracked_swap;
use vstd::pcm::*;
use vstd::pcm_lib::duplicate;
use vstd::prelude::*;

// This implements a resource for ownership of subsets of values in a set.

verus! {

broadcast use vstd::group_vstd_default;

#[verifier::reject_recursive_types(T)]
#[verifier::ext_equal]
struct SetCarrier<T> {
    auth: Option<Option<Set<T>>>,
    frac: Option<Set<T>>,
}

impl<T> PCM for SetCarrier<T> {
    closed spec fn valid(self) -> bool {
        match self.frac {
            None => false,
            Some(f) => match self.auth {
                None => true,
                Some(None) => false,
                Some(Some(a)) => f.subset_of(a),
            },
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        let auth = match (self.auth, other.auth) {
            (Some(_), Some(_)) => Some(None),
            (Some(_), None) => self.auth,
            (None, _) => other.auth,
        };

        let frac = match (self.frac, other.frac) {
            (Some(sfrac), Some(ofrac)) if sfrac.disjoint(ofrac) => Some(sfrac.union(ofrac)),
            _ => None,
        };
        SetCarrier { auth, frac }
    }

    closed spec fn unit() -> Self {
        SetCarrier { auth: None, frac: Some(Set::empty()) }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        broadcast use lemma_op_frac_subset_of;

    }

    proof fn commutative(a: Self, b: Self) {
        let ab = Self::op(a, b);
        let ba = Self::op(b, a);
        assert(ab == ba);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        let bc = Self::op(b, c);
        let ab = Self::op(a, b);
        let a_bc = Self::op(a, bc);
        let ab_c = Self::op(ab, c);
        assert(a_bc == ab_c);
    }

    proof fn op_unit(a: Self) {
        let x = Self::op(a, Self::unit());
        assert(a == x);
    }

    proof fn unit_valid() {
    }
}

broadcast proof fn lemma_op_frac_subset_of<T>(a: SetCarrier<T>, b: SetCarrier<T>)
    requires
        #[trigger] SetCarrier::op(a, b).valid(),
    ensures
        a.frac.unwrap() <= SetCarrier::op(a, b).frac.unwrap(),
        b.frac.unwrap() <= SetCarrier::op(a, b).frac.unwrap(),
{
}

pub struct Exclusive;
pub struct Monotonic;

mod private {
    pub trait GhostSetMode {}
}

impl private::GhostSetMode for Exclusive {}
impl private::GhostSetMode for Monotonic {}

#[verifier::reject_recursive_types(T)]
pub struct GhostSetAuth<T, Mode: > {
    resource: Resource<SetCarrier<T>>,
    _marker: std::marker::PhantomData<Mode>,
}

#[verifier::reject_recursive_types(T)]
pub struct GhostSubset<T, Mode: > {
    resource: Resource<SetCarrier<T>>,
    _marker: std::marker::PhantomData<Mode>,
}

/// implementation of a resource for owning a subset of keys in a map.
///
/// `GhostSetAuth<T, Mode>` represents authoritative ownership of the entire
/// set, and `GhostSubset<T, Mode>` represents client ownership of some subset
/// of values.  Updating the authoritative `GhostSetAuth<T, Mode>`
/// requires a `GhostSubset<T, Mode>` containing the values being updated.
/// `GhostSubset<T, Mode>`s can be combined or split.
///
/// ### Example
///
/// ```
/// fn example_use() {
///     let tracked (mut auth, mut sub) = GhostSetAuth::new(set![1u8, 2u8, 3u8]);
///
///     // Allocate some more keys in the auth map, receiving a new subset.
///     let tracked sub2 = auth.insert(set![4u8, 5u8]);
///     proof { sub.combine(sub2); }
///
///     // Delete some keys in the auth map, by returning corresponding subset.
///     let tracked sub3 = sub.split(set![3u8, 4u8]);
///     proof { auth.delete(sub3); }
///
///     // Split the subset into a multiple subsets.
///     let tracked sub4 = sub.split(set![1u8, 5u8]);
///
///     // In general, we might need to call agree() to establish the fact that
///     // a subset has the same values as the auth set.  Here, Verus doesn't need
///     // agree because it can track where both the auth and subset came from.
///     proof { sub.agree(&auth); }
///     proof { sub4.agree(&auth); }
///
///     assert(sub4.contains(1u8) && auth.contains(1u8));
///     assert(sub4.contains(5u8) && auth.contains(5u8));
///     assert(sub.contains(2u8) && auth.contains(2u8));
///     assert(sub.contains(2u8) && auth.contains(2u8));
///
///     assert(sub@ < auth@);
///
///     // Not shown in this simple example is the main use case of this resource:
///     // maintaining an invariant between GhostSetAuth<T, Mode> and some exec-mode
///     // shared state with a map view (e.g., HashSet<T>), which states that
///     // the Set<T> view of GhostSetAuth<T, Mode> is the same as the view of the
///     // HashSet<T>, and then handing out a GhostSubset<T, Mode> to different
///     // clients that might need to operate on different keys in this map.
/// }
/// ```
///
impl<T, Mode: > GhostSetAuth<T, Mode> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.resource.value().auth is Some
        &&& self.resource.value().auth.unwrap() is Some
        &&& self.resource.value().frac == Some(Set::<T>::empty())
    }

    pub closed spec fn id(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn view(self) -> Set<T> {
        self.resource.value().auth.unwrap().unwrap()
    }

    pub proof fn dummy() -> (tracked result: GhostSetAuth<T, Mode>) {
        let tracked (auth, subset) = GhostSetAuth::<T, Mode>::new(Set::empty());
        auth
    }

    pub proof fn take(tracked &mut self) -> (tracked result: GhostSetAuth<T, Mode>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);
        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

    pub proof fn empty(tracked &self) -> (tracked result: GhostSubset<T, Mode>)
        ensures
            result.id() == self.id(),
            result@ == Set::<T>::empty(),
    {
        use_type_invariant(self);
        GhostSubset::<T, Mode>::empty(self.id())
    }

    pub proof fn insert(tracked &mut self, insert_set: Set<T>) -> (tracked result: GhostSubset<T, Mode>)
        requires
            old(self)@.disjoint(insert_set),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union(insert_set),
            result.id() == self.id(),
            result@ == insert_set,
    {
        broadcast use lemma_op_frac_subset_of;

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);

        use_type_invariant(&mself);
        assert(mself.inv());
        let tracked mut resource = mself.resource;

        let new_carrier = SetCarrier {
            auth: Some(Some(resource.value().auth.unwrap().unwrap().union(insert_set))),
            frac: Some(insert_set),
        };

        let tracked updated_resource = resource.update(new_carrier);

        let auth_carrier = SetCarrier { auth: updated_resource.value().auth, frac: Some(Set::empty()) };

        let frac_carrier = SetCarrier { auth: None, frac: updated_resource.value().frac };

        assert(updated_resource.value() == SetCarrier::op(auth_carrier, frac_carrier));
        let tracked (auth_resource, frac_resource) = updated_resource.split(auth_carrier, frac_carrier);
        self.resource = auth_resource;
        GhostSubset { resource: frac_resource, _marker: std::marker::PhantomData }
    }

    pub proof fn new(s: Set<T>) -> (tracked result: (GhostSetAuth<T, Mode>, GhostSubset<T, Mode>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == s,
            result.1@ == s,
    {
        let tracked resource = Resource::alloc(SetCarrier { auth: Some(Some(s)), frac: Some(s) });

        let auth_carrier = SetCarrier { auth: Some(Some(s)), frac: Some(Set::empty()) };

        let frac_carrier = SetCarrier { auth: None, frac: Some(s) };

        assert(resource.value() == SetCarrier::op(auth_carrier, frac_carrier));
        let tracked (auth_resource, frac_resource) = resource.split(auth_carrier, frac_carrier);
        (GhostSetAuth { resource: auth_resource, _marker: std::marker::PhantomData }, GhostSubset { resource: frac_resource, _marker: std::marker::PhantomData })
    }
}

impl<T> GhostSetAuth<T, Exclusive> {
    pub proof fn delete(tracked &mut self, tracked delete_set: GhostSubset<T, Exclusive>)
        requires
            delete_set.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.difference(delete_set@),
    {
        broadcast use lemma_op_frac_subset_of;

        use_type_invariant(&*self);
        use_type_invariant(&delete_set);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut resource = mself.resource;

        resource = resource.join(delete_set.resource);

        let auth_set = resource.value().auth.unwrap().unwrap();
        let auth_set = auth_set.difference(delete_set@);

        let new_resource = SetCarrier { auth: Some(Some(auth_set)), frac: Some(Set::empty()) };

        self.resource = resource.update(new_resource);
    }
}


impl<T, Mode: > GhostSubset<T, Mode> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.resource.value().auth is None
        &&& self.resource.value().frac is Some
    }

    pub closed spec fn id(self) -> Loc {
        self.resource.loc()
    }

    pub closed spec fn view(self) -> Set<T> {
        self.resource.value().frac.unwrap()
    }

    pub proof fn dummy() -> (tracked result: GhostSubset<T, Mode>) {
        let tracked (auth, subset) = GhostSetAuth::<T, Mode>::new(Set::empty());
        subset
    }

    pub proof fn empty(id: int) -> (tracked result: GhostSubset<T, Mode>)
        ensures
            result.id() == id,
            result@ == Set::<T>::empty(),
    {
        let tracked resource = Resource::create_unit(id);
        GhostSubset { resource, _marker: std::marker::PhantomData }
    }

    pub proof fn take(tracked &mut self) -> (tracked result: GhostSubset<T, Mode>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);

        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

    pub proof fn agree(tracked self: &GhostSubset<T, Mode>, tracked auth: &GhostSetAuth<T, Mode>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        use_type_invariant(self);
        use_type_invariant(auth);

        let tracked joined = self.resource.join_shared(&auth.resource);
        joined.validate();
        assert(self.resource.value().frac.unwrap() <= joined.value().frac.unwrap());
    }

    pub proof fn combine(tracked &mut self, tracked other: GhostSubset<T, Mode>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union(other@),
            old(self)@.disjoint(other@),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);

        let tracked mut resource = Resource::alloc(SetCarrier::unit());
        tracked_swap(&mut self.resource, &mut resource);
        resource.validate_2(&other.resource);
        self.resource = resource.join(other.resource);
    }

    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubset<T, Mode>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.disjoint(other@),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.resource.validate_2(&other.resource);
    }

    pub proof fn split(tracked &mut self, split_set: Set<T>) -> (tracked result: GhostSubset<T, Mode>)
        requires
            split_set <= old(self)@,
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.union(result@),
            result@ == split_set,
            self@ == old(self)@ - split_set,
    {
        use_type_invariant(&*self);

        let tracked mut resource = Resource::alloc(SetCarrier::<T>::unit());
        tracked_swap(&mut self.resource, &mut resource);

        let self_carrier = SetCarrier { auth: None, frac: Some(resource.value().frac.unwrap().difference(split_set)) };

        let result_carrier = SetCarrier { auth: None, frac: Some(resource.value().frac.unwrap().intersect(split_set)) };

        assert(resource.value().frac == SetCarrier::op(self_carrier, result_carrier).frac);
        let tracked (self_resource, result_resource) = resource.split(self_carrier, result_carrier);
        self.resource = self_resource;
        GhostSubset { resource: result_resource, _marker: std::marker::PhantomData }
    }

    pub proof fn update(tracked &mut self, tracked auth: &mut GhostSetAuth<T, Mode>, s: Set<T>)
        requires
            s <= old(self)@,
            old(self).id() == old(auth).id(),
        ensures
            self.id() == old(self).id(),
            auth.id() == old(auth).id(),
            self@ == old(self)@.union(s),
            auth@ == old(auth)@.union(s),
    {
        broadcast use lemma_op_frac_subset_of;

        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut frac_resource = mself.resource;

        let tracked mut mauth = GhostSetAuth::<T, Mode>::dummy();
        tracked_swap(auth, &mut mauth);
        let tracked mut auth_resource = mauth.resource;

        frac_resource.validate_2(&auth_resource);
        let tracked mut resource = frac_resource.join(auth_resource);

        assert(resource.value().frac == frac_resource.value().frac);

        let carrier = SetCarrier {
            auth: Some(Some(resource.value().auth.unwrap().unwrap().union(s))),
            frac: Some(resource.value().frac.unwrap().union(s)),
        };

        let tracked updated_resource = resource.update(carrier);

        let auth_carrier = SetCarrier { auth: updated_resource.value().auth, frac: Some(Set::empty()) };

        let frac_carrier = SetCarrier { auth: None, frac: updated_resource.value().frac };

        assert(updated_resource.value().frac == SetCarrier::op(auth_carrier, frac_carrier).frac);
        let tracked (auth_resource, frac_resource) = updated_resource.split(auth_carrier, frac_carrier);
        auth.resource = auth_resource;
        self.resource = frac_resource;
    }
}

impl<T> GhostSubset<T, Monotonic> {
    pub proof fn duplicate(tracked &self) -> (tracked r: Self)
        ensures
            self.id() == r.id(),
            self@ == r@,
    {
        GhostSubset {
            resource: duplicate(&self.resource),
            _marker: std::marker::PhantomData,
        }
    }
}

} // verus!
