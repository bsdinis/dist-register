#[cfg(verus_only)]
use crate::invariants::committed_to::WriteCommitment;
#[cfg(verus_only)]
use crate::invariants::quorum::Quorum;
#[cfg(verus_only)]
use crate::invariants::quorum::ServerUniverse;
#[cfg(verus_only)]
use crate::proto::GetResponse;
#[cfg(verus_only)]
use crate::proto::GetTimestampResponse;
#[cfg(verus_only)]
use crate::timestamp::Timestamp;

#[cfg(verus_only)]
use std::collections::BTreeMap;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::std_specs::btree::BTreeMapAdditionalSpecFns;

verus! {

// This axioms are very much unsound
//
// (they allows duplication of resources)
//
pub axiom fn axiom_get_unanimous_replies(
    replies: &BTreeMap<(u64, u64), GetResponse>,
    tracked map: &mut ServerUniverse,
    min_ts: Timestamp,
    max_ts: Timestamp,
    max_val: Option<u64>,
    commitment_id: Loc,
) -> (tracked r: (Quorum, WriteCommitment))
    requires
        old(map).inv(),
        old(map).is_auth(),
    ensures
// Done: because the servers update the invariant, the server universe does not need to be
// updated

        map.inv(),
        map.is_auth(),
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        forall|k| #[trigger]
            old(map).contains_key(k) ==> {
                &&& old(map)[k]@@ is FullRightToAdvance ==> map[k]@@ is FullRightToAdvance
                &&& old(map)[k]@@ is HalfRightToAdvance ==> map[k]@@ is HalfRightToAdvance
            },
        // Done: post condition on replies ensures the quorum has the correct size
        map.valid_quorum(r.0),
        // Trivial
        r.0.inv(),
        // XXX: Done (ish) -- we in particular can reference the old_server as stored in the GetInv as a
        // lowerbound map (which can be updated with the replies from the servers as reponses come
        // in). By ServerUniverse::lemma_lower_bound, this holds
        old(map).leq(*map),
        // Done (ish) -- ditto
        forall|k: (u64, u64)|
            #![trigger map.contains_key(k.1)]
            #![trigger old(map)[k.1]]
            #![trigger map[k.1]]
            map.contains_key(k.1) ==> {
                &&& old(map)[k.1]@@.timestamp() <= map[k.1]@@.timestamp()
                &&& replies@.contains_key(k) ==> map[k.1]@@.timestamp()
                    == replies[k].spec_timestamp()
                &&& !replies@.contains_key(k) ==> map[k.1] == old(map)[k.1]
            },
        // Done (ish) -- ditto
        forall|k| #[trigger] r.0@.contains(k) ==> map[k]@@.timestamp() == max_ts,
        // TODO: maybe we create the GetInv at the beginning of the call?
        //  - forall |q \in old_server| old_watermark  <= q (from invariant)
        //  - new_server = old_server.update(replies)
        //  - old_server <= new_server
        //  - exists |q \in new_server| q.ts() == max_ts
        //  - old_watermark <= max_ts
        min_ts <= max_ts,
        // TODO: need to get committment ids on the server first
        //  - can move this axiomatization somewhere in the GetInv def
        r.1@ == (max_ts, max_val),
        r.1.id() == commitment_id,
;

pub axiom fn axiom_writeback_unanimous_replies(
    get_replies: &BTreeMap<(u64, u64), GetResponse>,
    wb_replies: &BTreeMap<(u64, u64), ()>,
    tracked map: &mut ServerUniverse,
    min_ts: Timestamp,
    max_ts: Timestamp,
    max_val: Option<u64>,
    commitment_id: Loc,
) -> (tracked r: (Quorum, WriteCommitment))
    requires
        old(map).inv(),
        old(
            map,
        ).is_auth(),
// NOTE(net_axiom): relate the get_replies to the wb_replies (i.e., if something in the
// get_replies is < max_ts then that idx must be in wb_replies)
// NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
// How to do? network spec + sending lower bounds on read
// This will enable removing the min_ts requirement

    ensures
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        map.is_auth(),
        forall|k| #[trigger]
            old(map).contains_key(k) ==> {
                &&& old(map)[k]@@ is FullRightToAdvance ==> map[k]@@ is FullRightToAdvance
                &&& old(map)[k]@@ is HalfRightToAdvance ==> map[k]@@ is HalfRightToAdvance
            },
        r.0.inv(),
        map.valid_quorum(r.0),
        // this is derivable if replies come with lower bounds
        old(map).leq(*map),
        forall|k: (u64, u64)|
            #![trigger map.contains_key(k.1)]
            #![trigger old(map)[k.1]]
            #![trigger map[k.1]]
            map.contains_key(k.1) ==> {
                &&& get_replies@.contains_key(k) ==> {
                    let get_ts = get_replies[k].spec_timestamp();
                    ({
                        ||| get_ts == max_ts ==> map[k.1]@@.timestamp() == get_ts
                        ||| wb_replies@.contains_key(k) ==> map[k.1]@@.timestamp() == max_ts
                    }) && r.0@.contains(k.1)
                }
                &&& !get_replies@.contains_key(k) ==> {
                    &&& map[k.1] == old(map)[k.1]
                    &&& !r.0@.contains(k.1)
                }
            },
        forall|k| #[trigger] r.0@.contains(k) ==> map[k]@@.timestamp() == max_ts,
        min_ts <= max_ts,
        r.1@ == (max_ts, max_val),
        r.1.id() == commitment_id,
;

pub axiom fn axiom_get_ts_replies(
    replies: &BTreeMap<(u64, u64), GetTimestampResponse>,
    tracked map: &mut ServerUniverse,
    max_ts: Timestamp,
) -> (tracked r: Quorum)
    requires
        old(map).inv(),
        old(map).is_auth(),
        exists|k: (u64, u64)| #[trigger]
            replies@.contains_key(k) ==> replies[k].spec_timestamp() == max_ts,
        forall|k: (u64, u64)| #[trigger]
            replies@.contains_key(k) ==> replies[k].spec_timestamp() <= max_ts,
    ensures
        map.dom() == old(map).dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        map.is_auth(),
        forall|k| #[trigger]
            old(map).contains_key(k) ==> {
                &&& old(map)[k]@@ is FullRightToAdvance ==> map[k]@@ is FullRightToAdvance
                &&& old(map)[k]@@ is HalfRightToAdvance ==> map[k]@@ is HalfRightToAdvance
            },
        r.inv(),
        map.valid_quorum(r),
        // this is derivable if replies come with lower bounds
        old(map).leq(*map),
        forall|k: (u64, u64)|
            #![trigger map.contains_key(k.1)]
            #![trigger old(map)[k.1]]
            #![trigger map[k.1]]
            map.contains_key(k.1) ==> {
                &&& replies@.contains_key(k) ==> {
                    &&& map[k.1]@@.timestamp() == replies[k].spec_timestamp()
                    &&& r@.contains(k.1)
                }
                &&& !replies@.contains_key(k) ==> {
                    &&& map[k.1] == old(map)[k.1]
                    &&& !r@.contains(k.1)
                }
            },
        map.quorum_timestamp(r) == max_ts,
;

pub axiom fn axiom_write_replies(
    replies: &BTreeMap<(u64, u64), ()>,
    tracked map: &mut ServerUniverse,
    exec_ts: Timestamp,
) -> (tracked r: Quorum)
    requires
        old(map).inv(),
        old(
            map,
        ).is_auth(),
// NOTE(net_axiom): timestamps in the get_replies need to be above the lower bounds in old_map
// How to do? network spec + sending lower bounds on read

    ensures
        map.map.dom() == old(map).map.dom(),
        map.locs() == old(map).locs(),
        map.inv(),
        map.is_auth(),
        forall|k| #[trigger]
            old(map).contains_key(k) ==> {
                &&& old(map)[k]@@ is FullRightToAdvance ==> map[k]@@ is FullRightToAdvance
                &&& old(map)[k]@@ is HalfRightToAdvance ==> map[k]@@ is HalfRightToAdvance
            },
        r.inv(),
        map.valid_quorum(r),
        // this is derivable if replies come with lower bounds
        old(map).leq(*map),
        forall|k: (u64, u64)|
            #![trigger map.contains_key(k.1)]
            #![trigger old(map)[k.1]]
            #![trigger map[k.1]]
            map.contains_key(k.1) ==> {
                &&& replies@.contains_key(k) ==> {
                    &&& map[k.1]@@.timestamp() >= exec_ts
                    &&& r@.contains(k.1)
                }
                &&& !replies@.contains_key(k) ==> {
                    &&& map[k.1] == old(map)[k.1]
                    &&& !r@.contains(k.1)
                }
            },
        forall|k| #[trigger] r@.contains(k) ==> map[k]@@.timestamp() >= exec_ts,
;

pub axiom fn axiom_fake_commitment(timestamp: Timestamp, value: Option<u64>) -> (tracked r:
    WriteCommitment)
    ensures
        r.key() == timestamp,
        r.value() == value,
;

} // verus!
