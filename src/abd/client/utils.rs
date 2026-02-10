#![allow(dead_code)]

use crate::abd::min::MinOrd;
use crate::abd::timestamp::Timestamp;

use vstd::prelude::*;

verus! {

pub fn max_from_get_replies<Id: MinOrd + Clone>(vals: &[(usize, (Timestamp<Id>, Option<u64>))]) -> (r: Option<
    (Timestamp<Id>, Option<u64>),
>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.map_values(|v: (usize, (Timestamp<Id>, Option<u64>))| v.1).contains(r->0)
            &&& forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).0 >= vals[idx].1.0
        }),
        vals.len() == 0 ==> r is None,
{
    if vals.is_empty() {
        return None;
    }
    assert(vals.len() > 0);

    let mut max_idx = 0;
    let mut max_ts = vals[0].1.0.clone();
    for idx in 1..(vals.len())
        invariant
            0 <= max_idx < vals.len(),
    {
        if vals[idx].1.0.seqno > max_ts.seqno || (vals[idx].1.0.seqno == max_ts.seqno
            && vals[idx].1.0.client_id > max_ts.client_id) {
            max_ts = vals[idx].1.0.clone();
            max_idx = idx;
        }
    }

    let max_val = vals[max_idx].1.1.clone();
    let r = Some((max_ts, max_val));
    assert(r is Some);
    assume(vals@.map_values(|v: (usize, (Timestamp<Id>, Option<u64>))| v.1).contains(r->0));
    assume(forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).0 >= vals[idx].1.0);
    r
}

pub fn max_from_get_ts_replies<Id: MinOrd + Clone>(vals: &[(usize, Timestamp<Id>)]) -> (r: Option<Timestamp<Id>>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.map_values(|v: (usize, Timestamp<Id>)| v.1).contains(r->0)
            &&& forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0) >= vals[idx].1
        }),
        vals.len() == 0 ==> r is None,
{
    if vals.len() == 0 {
        return None;
    }
    assert(vals.len() > 0);

    let mut max_ts = vals[0].1.clone();
    for idx in 1..(vals.len()) {
        if vals[idx].1.seqno > max_ts.seqno || (vals[idx].1.seqno == max_ts.seqno
            && vals[idx].1.client_id > max_ts.client_id) {
            max_ts = vals[idx].1.clone();
        }
    }

    let r = Some(max_ts);
    assert(r is Some);
    assume(vals@.map_values(|v: (usize, Timestamp<Id>)| v.1).contains(r->0));
    assume(forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0) >= vals[idx].1);
    r
}

} // verus!
