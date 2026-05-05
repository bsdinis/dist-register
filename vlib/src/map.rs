use vstd::prelude::*;

verus! {

pub proof fn lemma_map_values_dom<K, V, W>(a: Map<K, V>, f: spec_fn(V) -> W)
    requires
        a.dom().finite(),
    ensures
        a.map_values(f).dom() == a.dom(),
{
    let b = a.map_values(f);
    assert forall|k: K| #[trigger] a.contains_key(k) implies b.contains_key(k) by {}

    assert forall|k: K| #[trigger] b.contains_key(k) implies a.contains_key(k) by {}
}

} // verus!
