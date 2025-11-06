#[allow(unused_imports)]
use crate::abd::invariants::committed_to::WriteCommitment;
#[allow(unused_imports)]
use crate::abd::invariants::quorum::Quorum;
#[allow(unused_imports)]
use crate::abd::invariants::quorum::ServerUniverse;
#[allow(unused_imports)]
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

verus! {

// This axioms are very much unsound
//
// (they allows duplication of resources)
//
pub axiom fn axiom_get_unanimous_replies(
    replies: &[(usize, (Timestamp, Option<u64>))],
    tracked map: &mut ServerUniverse,
    min_ts: Timestamp,
    max_ts: Timestamp,
    max_val: Option<u64>,
    commitment_id: int,
) -> (tracked r: (Quorum, WriteCommitment))
    requires
        old(
            map,
        ).inv(),
// NOTE(net_axiom): timestamps in the replies need to be above the lower bounds in old_map
// How to do? network spec + sending lower bounds on read
// This will enable removing the min_ts requirement

    ensures
        map.inv(),
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        map.valid_quorum(r.0),
        r.0.inv(),
        forall|k: nat|
            map.contains_key(k) ==> {
                // this is derivable if replies come with lower bounds
                &&& old(map)[k]@@.timestamp() <= map[k]@@.timestamp()
                &&& exists|idx: nat|
                    0 <= idx < replies.len() && replies[idx as int].0 == k ==> {
                        map[k]@@.timestamp() == replies[idx as int].1.0
                    }
                &&& !(exists|idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k) ==> {
                    map[k] == old(map)[k]
                }
            },
        forall|k: nat| r.0@.contains(k) ==> map[k]@@.timestamp() == max_ts,
        min_ts <= max_ts,
        r.1@ == (max_ts, max_val),
        r.1.id() == commitment_id,
;

pub axiom fn axiom_writeback_unanimous_replies(
    get_replies: &[(usize, (Timestamp, Option<u64>))],
    wb_replies: &[(usize, ())],
    tracked map: &mut ServerUniverse,
    min_ts: Timestamp,
    max_ts: Timestamp,
    max_val: Option<u64>,
    commitment_id: int,
) -> (tracked r: (Quorum, WriteCommitment))
    requires
        old(
            map,
        ).inv(),
// NOTE(net_axiom): relate the get_replies to the wb_replies (i.e., if something in the
// get_replies is < max_ts then that idx must be in wb_replies)
// NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
// How to do? network spec + sending lower bounds on read
// This will enable removing the min_ts requirement

    ensures
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        r.0.inv(),
        map.valid_quorum(r.0),
        forall|k: nat|
            map.contains_key(k) ==> {
                // this is derivable if replies come with lower bounds
                &&& old(map)[k]@@.timestamp() <= map[k]@@.timestamp()
                &&& exists|g_idx: nat|
                    0 <= g_idx < get_replies.len() && get_replies[g_idx as int].0 == k ==> {
                        let get_ts = get_replies[g_idx as int].1.0;
                        ({
                            ||| get_ts == max_ts ==> map[k]@@.timestamp() == get_ts
                            ||| exists|wb_idx: nat|
                                0 <= wb_idx < wb_replies.len() && wb_replies[wb_idx as int].0 == k
                                    ==> { map[k]@@.timestamp() == max_ts }
                        }) && r.0@.contains(k)
                    }
                &&& !(exists|idx: nat|
                    0 <= idx < get_replies.len() && get_replies[idx as int].0 == k) ==> {
                    &&& map[k] == old(map)[k]
                    &&& !r.0@.contains(k)
                }
            },
        forall|k: nat| r.0@.contains(k) ==> map[k]@@.timestamp() == max_ts,
        min_ts <= max_ts,
        r.1@ == (max_ts, max_val),
        r.1.id() == commitment_id,
;

pub axiom fn axiom_get_ts_replies(
    replies: &[(usize, Timestamp)],
    tracked map: &mut ServerUniverse,
    max_ts: Timestamp,
) -> (tracked r: Quorum)
    requires
        old(map).inv(),
        exists|idx: int| 0 <= idx < replies.len() ==> replies[idx].1 == max_ts,
        forall|idx: int| 0 <= idx < replies.len() ==> replies[idx].1 <= max_ts,
    ensures
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        r.inv(),
        map.valid_quorum(r),
        forall|k: nat|
            map.contains_key(k) ==> {
                // this is derivable if replies come with lower bounds
                &&& old(map)[k]@@.timestamp() <= map[k]@@.timestamp()
                &&& exists|idx: int|
                    0 <= idx < replies.len() && replies[idx].0 == k ==> {
                        &&& map[k]@@.timestamp() == replies[idx as int].1
                        &&& r@.contains(k)
                    }
                &&& !(exists|idx: int| 0 <= idx < replies.len() && replies[idx].0 == k) ==> {
                    &&& map[k] == old(map)[k]
                    &&& !r@.contains(k)
                }
            },
        map.quorum_timestamp(r) == max_ts,
;

pub axiom fn axiom_write_replies(
    replies: &[(usize, ())],
    tracked map: &mut ServerUniverse,
    exec_ts: Timestamp,
) -> (tracked r: Quorum)
    requires
        old(
            map,
        ).inv(),
// NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
// How to do? network spec + sending lower bounds on read

    ensures
        map.map.dom() == old(map).map.dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        r.inv(),
        map.valid_quorum(r),
        forall|k: nat|
            map.contains_key(k) ==> {
                // this is derivable if replies come with lower bounds
                &&& old(map)[k]@@.timestamp() <= map.map[k]@@.timestamp()
                &&& exists|idx: nat|
                    0 <= idx < replies.len() && replies[idx as int].0 == k ==> {
                        &&& map[k]@@.timestamp() >= exec_ts
                        &&& r@.contains(k)
                    }
                &&& !(exists|idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k) ==> {
                    &&& map[k] == old(map)[k]
                    &&& !r@.contains(k)
                }
            },
        forall|k: nat| r@.contains(k) ==> map[k]@@.timestamp() >= exec_ts,
;

} // verus!
