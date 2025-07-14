use builtin_macros::*;
use vstd::pcm::*;
#[cfg(verus_keep_ghost)]
use vstd::pcm_lib::*;
use vstd::prelude::*;

verus! {

pub enum LogResourceValue<T> {
    PrefixKnowledge { prefix: Seq<T> },
    FullAuthority { log: Seq<T> },
    Invalid,
}

pub open spec fn is_prefix<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    &&& s1.len() <= s2.len()
    &&& forall|i| 0 <= i < s1.len() ==> s1[i] == s2[i]
}

impl<T> PCM for LogResourceValue<T> {
    open spec fn valid(self) -> bool {
        &&& !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (
                Self::PrefixKnowledge { prefix: prefix1 },
                Self::PrefixKnowledge { prefix: prefix2 },
            ) => if is_prefix(prefix1, prefix2) {
                other
            } else {
                if is_prefix(prefix2, prefix1) {
                    self
                } else {
                    Self::Invalid
                }
            },
            (Self::PrefixKnowledge { prefix }, Self::FullAuthority { log }) => if is_prefix(
                prefix,
                log,
            ) {
                other
            } else {
                Self::Invalid
            },
            (Self::FullAuthority { log }, Self::PrefixKnowledge { prefix }) => if is_prefix(
                prefix,
                log,
            ) {
                self
            } else {
                Self::Invalid
            },
            (_, _) => Self::Invalid,
        }
    }

    open spec fn unit() -> Self {
        Self::PrefixKnowledge { prefix: Seq::<T>::empty() }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
        assert(forall|log1: Seq<T>, log2: Seq<T>|
            is_prefix(log1, log2) && is_prefix(log2, log1) ==> log1 =~= log2);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        assert(forall|log1: Seq<T>, log2: Seq<T>|
            is_prefix(log1, log2) && is_prefix(log2, log1) <==> log1 =~= log2);
        assert(forall|log| is_prefix(log, Seq::<T>::empty()) ==> log =~= Seq::<T>::empty());
    }

    proof fn op_unit(a: Self) {
        assert(forall|log| is_prefix(log, Seq::<T>::empty()) ==> log =~= Seq::<T>::empty());
    }

    proof fn unit_valid() {
    }
}

impl<T> LogResourceValue<T> {
    pub open spec fn log(self) -> Seq<T> {
        match self {
            LogResourceValue::PrefixKnowledge { prefix } => prefix,
            LogResourceValue::FullAuthority { log } => log,
            LogResourceValue::Invalid => Seq::<T>::empty(),
        }
    }

    proof fn op_unit(a: Self) {
        assert(forall|log| is_prefix(log, Seq::<T>::empty()) ==> log =~= Seq::<T>::empty());
    }

    proof fn unit_valid() {
    }
}

pub struct LogResource<T> {
    r: Resource<LogResourceValue<T>>,
}

impl<T> LogResource<T> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> LogResourceValue<T> {
        self.r.value()
    }

    pub proof fn alloc() -> (tracked result: LogResource<T>)
        ensures
            result@ is FullAuthority,
            result@.log() == Seq::<T>::empty(),
    {
        let v = LogResourceValue::<T>::FullAuthority { log: Seq::<T>::empty() };
        let tracked r = Resource::<LogResourceValue::<T>>::alloc(v);
        Self { r }
    }

    pub proof fn append(tracked &mut self, v: T)
        requires
            old(self)@ is FullAuthority,
        ensures
            self@ is FullAuthority,
            self.id() == old(self).id(),
            self@.log() == old(self)@.log() + seq![v],
    {
        let value = LogResourceValue::<T>::FullAuthority { log: self@.log() + seq![v] };
        update_mut(&mut self.r, value);
    }

    pub proof fn extract_prefix_knowledge(tracked &self) -> (tracked out: Self)
        ensures
            out@ is PrefixKnowledge,
            out.id() == self.id(),
            out@.log() == self@.log(),
    {
        let v = LogResourceValue::<T>::PrefixKnowledge { prefix: self@.log() };
        let tracked r = copy_duplicable_part(&self.r, v);
        Self { r }
    }

    pub proof fn deduce_prefix_relation(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            self@ == old(self)@,
            is_prefix(self@.log(), other@.log()) || is_prefix(other@.log(), self@.log()),
            self@ is FullAuthority ==> is_prefix(other@.log(), self@.log()),
            other@ is FullAuthority ==> is_prefix(self@.log(), other@.log()),
    {
        self.r.validate_2(&other.r)
    }
}


} // verus!
