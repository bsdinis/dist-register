#![allow(dead_code)]

use std::collections::BTreeMap;

use crate::abd::proto::Timestamp;

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::BTreeMapAdditionalSpecFns;

verus! {

pub fn max_from_get_replies(vals: &BTreeMap<(u64, u64), (Timestamp, Option<u64>)>) -> (r: Option<
    (Timestamp, Option<u64>),
>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.values().contains(r->0)
            &&& forall|id| #[trigger] vals@.contains_key(id) ==> (r->0).0 >= vals[id].0
        }),
        vals.len() == 0 ==> r is None,
{
    if vals.is_empty() {
        assert(vals.len() == 0);
        return None;
    }
    assert(vals.len() > 0);

    let mut max: Option<(Timestamp, Option<u64>)> = None;
    let it = vals.iter();
    for (_k, v) in it {
        let mut new_val = None;
        if let Some((max_ts, _max_v)) = max.as_ref() {
            if v.0 > *max_ts {
                new_val = Some(*v);
            }
        } else {
            max = Some(*v)
        }
        if new_val.is_some() {
            max = new_val
        }
    }

    // XXX: this requires looking into building a type invariant over there, which is a big pain
    assume(max is Some);
    assume(vals@.values().contains(max->0));
    assume(forall|id| #[trigger] vals@.contains_key(id) ==> (max->0).0 >= vals[id].0);
    max
}

pub fn max_from_get_ts_replies(vals: &BTreeMap<(u64, u64), Timestamp>) -> (r: Option<Timestamp>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.values().contains(r->0)
            &&& forall|id| #[trigger] vals@.contains_key(id) ==> (r->0) >= vals[id]
        }),
        vals.len() == 0 ==> r is None,
{
    if vals.len() == 0 {
        return None;
    }
    assert(vals.len() > 0);

    let mut max_ts: Option<Timestamp> = None;
    let it = vals.iter();
    for (_k, v) in it {
        let mut new_ts = None;
        if let Some(mts) = max_ts.as_ref() {
            if *v > *mts {
                new_ts = Some(*v)
            }
        } else {
            max_ts = Some(*v)
        }
        if new_ts.is_some() {
            max_ts = new_ts
        }
    }

    // XXX: this requires looking into building a type invariant over there, which is a big pain
    assume(max_ts is Some);
    assume(vals@.values().contains(max_ts->0));
    assume(forall|id| #[trigger] vals@.contains_key(id) ==> (max_ts->0) >= vals[id]);
    max_ts
}

} // verus!
