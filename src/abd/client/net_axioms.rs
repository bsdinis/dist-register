use crate::abd::client::utils::max_from_get_ts_replies;
use crate::abd::invariants::quorum::Quorum;
use crate::abd::invariants::quorum::ServerUniverse;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::prelude::*;

verus! {

// This axioms are very much unsound
//
// (they allows duplication of resources)
//

pub axiom fn axiom_get_unanimous_replies(
    replies: &[(usize, (Timestamp, Option<u64>))],
    tracked old_map: ServerUniverse,
    max_ts: Timestamp,
) -> (tracked r: (ServerUniverse, Quorum))
    requires
        old_map.inv(),
        // NOTE(net_axiom): timestamps in the replies need to be above the lower bounds in old_map
        // How to do? network spec + sending lower bounds on read
    ensures
        r.0.map.dom() == old_map.map.dom(),
        r.0.locs() == old_map.locs(),
        r.0.inv(),
        r.1.inv(),
        r.0.valid_quorum(r.1),
        forall |k: nat| r.0.contains_key(k) ==> {
            // this is derivable if replies come with lower bounds
            &&& old_map[k]@@.timestamp() <= r.0.map[k]@@.timestamp()
            &&& exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ==> {
                r.0[k]@@.timestamp() == replies[idx as int].1.0
            }
            &&& ! (exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ) ==> {
                r.0[k] == old_map[k]
            }
        },
        forall |k: nat| r.1@.contains(k) ==> r.0[k]@@.timestamp() == max_ts
;

pub axiom fn axiom_writeback_unanimous_replies(
    get_replies: &[(usize, (Timestamp, Option<u64>))],
    wb_replies: &[(usize, ())],
    tracked old_map: ServerUniverse,
    max_ts: Timestamp,
) -> (tracked r: (ServerUniverse, Quorum))
    requires
        old_map.inv(),
        // NOTE(net_axiom): relate the get_replies to the wb_replies (i.e., if something in the
        // get_replies is < max_ts then that idx must be in wb_replies)
        // NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
        // How to do? network spec + sending lower bounds on read
    ensures
        r.0.map.dom() == old_map.map.dom(),
        r.0.locs() == old_map.locs(),
        r.0.inv(),
        r.1.inv(),
        r.0.valid_quorum(r.1),
        forall |k: nat| r.0.contains_key(k) ==> {
            // this is derivable if replies come with lower bounds
            &&& old_map[k]@@.timestamp() <= r.0.map[k]@@.timestamp()
            &&& exists |g_idx: nat| 0 <= g_idx < get_replies.len() && get_replies[g_idx as int].0 == k ==> {
                let get_ts = get_replies[g_idx as int].1.0;
                ({
                    ||| get_ts == max_ts ==> r.0[k]@@.timestamp() == get_ts
                    ||| exists |wb_idx: nat| 0 <= wb_idx < wb_replies.len() && wb_replies[wb_idx as int].0 == k ==> {
                        r.0[k]@@.timestamp() == max_ts
                    }
                }) && r.1@.contains(k)
            }
            &&& ! (exists |idx: nat| 0 <= idx < get_replies.len() && get_replies[idx as int].0 == k ) ==> {
                &&& r.0[k] == old_map[k]
                &&& !r.1@.contains(k)
            }
        },
        forall |k: nat| r.1@.contains(k) ==> r.0[k]@@.timestamp() == max_ts
;

pub axiom fn axiom_get_ts_replies(
    replies: &[(usize, Timestamp)],
    tracked old_map: ServerUniverse,
    max_ts: Timestamp,
) -> (tracked r: (ServerUniverse, Quorum))
    requires
        old_map.inv(),
        exists |idx: int| 0 <= idx < replies.len() ==> replies[idx].1 == max_ts,
        forall |idx: int| 0 <= idx < replies.len() ==> replies[idx].1 <= max_ts,
    ensures
        r.0.map.dom() == old_map.map.dom(),
        r.0.locs() == old_map.locs(),
        r.0.inv(),
        r.1.inv(),
        r.0.valid_quorum(r.1),
        forall |k: nat| r.0.contains_key(k) ==> {
            // this is derivable if replies come with lower bounds
            &&& old_map[k]@@.timestamp() <= r.0[k]@@.timestamp()
            &&& exists |idx: int| 0 <= idx < replies.len() && replies[idx].0 == k ==> {
                 &&& r.0.map[k]@@.timestamp() == replies[idx as int].1
                 &&& r.1@.contains(k)
            }
            &&& ! (exists |idx: int| 0 <= idx < replies.len() && replies[idx].0 == k ) ==> {
                 &&& r.0.map[k] == old_map.map[k]
                 &&& !r.1@.contains(k)
            }
        },
        r.0.quorum_timestamp(r.1) == max_ts
;

pub axiom fn axiom_write_replies(
    replies: &[(usize, ())],
    tracked old_map: ServerUniverse,
    exec_ts: Timestamp,
) -> (tracked r: (ServerUniverse, Quorum))
    requires
        old_map.inv(),
        // NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
        // How to do? network spec + sending lower bounds on read
    ensures
        r.0.map.dom() == old_map.map.dom(),
        r.0.locs() == old_map.locs(),
        r.0.inv(),
        r.1.inv(),
        r.0.valid_quorum(r.1),
        forall |k: nat| r.0.contains_key(k) ==> {
            // this is derivable if replies come with lower bounds
            &&& old_map[k]@@.timestamp() <= r.0.map[k]@@.timestamp()
            &&& exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ==> {
                &&& r.0[k]@@.timestamp() >= exec_ts
                &&& r.1@.contains(k)
            }
            &&& ! (exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ) ==> {
                &&& r.0[k] == old_map[k]
                &&& !r.1@.contains(k)
            }
        },
        forall |k: nat| r.1@.contains(k) ==> r.0[k]@@.timestamp() >= exec_ts
;

}
