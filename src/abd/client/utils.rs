use crate::abd::proto::Timestamp;

use vstd::prelude::*;

verus! {

pub fn max_from_get_replies(vals: &[(usize, (Timestamp, Option<u64>))]) -> (r: Option<(Timestamp, Option<u64>)>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.map_values(|v: (usize, (Timestamp, Option<u64>))| v.1).contains(r->0)
            &&& forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).0.ge(&vals[idx].1.0)
        }),
        vals.len() == 0 ==> r is None
{
    if vals.len() == 0 {
        return None;
    }

    assert(vals.len() > 0);

    let mut max_idx = 0;
    let mut max_ts = vals[0].1.0;
    for idx in 1..(vals.len())
        invariant
            0 <= max_idx < vals.len(),
    {
        if vals[idx].1.0.seqno > max_ts.seqno ||
            (
        vals[idx].1.0.seqno == max_ts.seqno &&
        vals[idx].1.0.client_id > max_ts.client_id
            )
        {
            max_ts = vals[idx].1.0;
            max_idx = idx;
        }
    }

    let r = Some(vals[max_idx].1);
    assert(r is Some);
    assume(vals@.map_values(|v: (usize, (Timestamp, Option<u64>))| v.1).contains(r->0));
    assume(forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).0.ge(&vals[idx].1.0));
    r
}

pub fn max_from_get_ts_replies(vals: &[(usize, Timestamp)]) -> (r: Option<Timestamp>)
    ensures
        vals.len() > 0 ==> ({
            &&& r is Some
            &&& vals@.map_values(|v: (usize, Timestamp)| v.1).contains(r->0)
            &&& forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).ge(&vals[idx].1)
        }),
        vals.len() == 0 ==> r is None
{
    if vals.len() == 0 {
        return None;
    }

    assert(vals.len() > 0);

    let mut max_ts = vals[0].1;
    for idx in 1..(vals.len())
    {
        if vals[idx].1.seqno > max_ts.seqno ||
            (
        vals[idx].1.seqno == max_ts.seqno &&
        vals[idx].1.client_id > max_ts.client_id
            )
        {
            max_ts = vals[idx].1;
        }
    }

    let r = Some(max_ts);
    assert(r is Some);
    assume(vals@.map_values(|v: (usize, Timestamp)| v.1).contains(r->0));
    assume(forall|idx: int| #![auto] 0 <= idx < vals.len() ==> (r->0).ge(&vals[idx].1));
    r
}

}
