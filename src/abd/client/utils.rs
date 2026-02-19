#![allow(dead_code)]

use std::collections::BTreeMap;

use crate::abd::proto::{GetResponse, GetTimestampResponse};

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::btree::BTreeMapAdditionalSpecFns;

verus! {

pub fn max_from_get_replies(vals: &BTreeMap<(u64, u64), GetResponse>) -> (r: Option<GetResponse>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.values().contains(r->0)
            &&& forall|id| #[trigger] vals@.contains_key(id) ==> (r->0).spec_timestamp() >= vals[id].spec_timestamp()
        }),
        vals.len() == 0 ==> r is None,
{
    // TODO(obeys_cmp_spec): add this to verus
    assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
    if vals.is_empty() {
        proof {
            vals@.dom().lemma_len0_is_empty();
        }
        assert(vals.len() == 0);
        return None;
    }
    assert(vals.len() > 0);

    let mut max: Option<&GetResponse> = None;
    let it = vals.iter();
    for (_k, v) in it {
        let mut new_val = None;
        if let Some(max_resp) = max.as_ref() {
            if v.timestamp() > max_resp.timestamp() {
                new_val = Some(v);
            }
        } else {
            max = Some(v)
        }
        if new_val.is_some() {
            max = new_val
        }
    }


    // XXX: this requires looking into building a type invariant over there, which is a big pain
    assume(max is Some);
    let rmax = max.unwrap().clone();
    assume(vals@.values().contains(rmax));
    assume(forall|id| #[trigger] vals@.contains_key(id) ==> rmax.spec_timestamp() >= vals[id].spec_timestamp());
    Some(rmax)
}

pub fn max_from_get_ts_replies(vals: &BTreeMap<(u64, u64), GetTimestampResponse>) -> (r: Option<GetTimestampResponse>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.values().contains(r->0)
            &&& forall|id| #[trigger] vals@.contains_key(id) ==> (r->0).spec_timestamp() >= vals[id].spec_timestamp()
        }),
        vals.len() == 0 ==> r is None,
{
    // TODO(obeys_cmp_spec): add this to verus
    assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
    if vals.len() == 0 {
        return None;
    }
    assert(vals.len() > 0);

    let mut max: Option<&GetTimestampResponse> = None;
    let it = vals.iter();
    for (_k, v) in it {
        let mut new_val = None;
        if let Some(max_resp) = max.as_ref() {
            if v.timestamp() > max_resp.timestamp() {
                new_val = Some(v);
            }
        } else {
            max = Some(v)
        }
        if new_val.is_some() {
            max = new_val
        }
    }

    // XXX: this requires looking into building a type invariant over there, which is a big pain
    assume(max is Some);
    let rmax = max.unwrap().clone();
    assume(vals@.values().contains(rmax));
    assume(forall|id| #[trigger] vals@.contains_key(id) ==> rmax.spec_timestamp() >= vals[id].spec_timestamp());
    Some(rmax)
}

} // verus!
