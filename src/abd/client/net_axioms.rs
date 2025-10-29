use crate::abd::client::utils::max_from_get_ts_replies;
use crate::abd::invariants::server_map::Quorum;
use crate::abd::invariants::server_map::ServerMap;
use crate::abd::proto::Timestamp;
use crate::abd::resource::monotonic_timestamp::MonotonicTimestampResource;

use vstd::prelude::*;

verus! {

// This axioms are very much unsound
//
// (they allows duplication of resources)
//

pub axiom fn axiom_get_replies(
    replies: &[(usize, (Timestamp, Option<u64>))],
    tracked old_map: ServerMap
) -> (tracked r: ServerMap)
    requires
        old_map.inv(),
        // TODO(network): timestamps in the replies need to be above the lower bounds in old_map
        // How to do? network spec + sending lower bounds on read
    ensures
        r.map.dom() == old_map.map.dom(),
        r.locs() == old_map.locs(),
        r.inv(),
        forall |k: nat| r.map.contains_key(k) ==> {
            &&& exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ==> {
                r.map[k]@@.timestamp() == replies[idx as int].1.0
            }
            &&& ! (exists |idx: nat| 0 <= idx < replies.len() && replies[idx as int].0 == k ) ==> {
                r.map[k] == old_map.map[k]
            }
        }
;

pub axiom fn axiom_get_ts_replies(
    replies: &[(usize, Timestamp)],
    tracked old_map: ServerMap,
    max_ts: Timestamp,
) -> (tracked r: (ServerMap, Quorum))
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
        forall |k: nat| r.0.map.contains_key(k) ==> {
            &&& exists |idx: int| 0 <= idx < replies.len() && replies[idx].0 == k ==> {
                &&& r.0.map[k]@@.timestamp() == replies[idx as int].1
                &&& r.1.submap.contains_key(k)
            }
            &&& ! (exists |idx: int| 0 <= idx < replies.len() && replies[idx].0 == k ) ==> {
                &&& r.0.map[k] == old_map.map[k]
                &&& !r.1.submap.contains_key(k)
            }
        },
        r.1.timestamp() == max_ts
;

}
