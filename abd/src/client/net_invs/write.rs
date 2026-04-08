use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::channel::ChannelInv;
use crate::proto::GetTimestampResponse;
use crate::proto::Response;

use verdist::network::channel::Channel;
use verdist::rpc::replies::ReplyAccumulator;

use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::btree::increasing_seq;

verus! {

#[allow(dead_code)]
pub struct GetTimestampAccumulator<C: Channel<K = ChannelInv>> {
    replies: BTreeMap<(u64, u64), GetTimestampResponse>,
    channels: Ghost<Map<C::Id, C>>,
    request_tag: u64,
}

#[allow(dead_code)]
pub struct WriteAccumulator<C: Channel<K = ChannelInv>> {
    replies: BTreeMap<(u64, u64), ()>,
    channels: Ghost<Map<C::Id, C>>,
    request_tag: u64,
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> GetTimestampAccumulator<C> {
    pub fn new(channels: Ghost<Map<C::Id, C>>, request_tag: u64) -> (r: Self)
        ensures
            r.spec_request_tag() == request_tag,
            r.replies().is_empty(),
            r.spec_channels() == channels@,
    {
        GetTimestampAccumulator { replies: BTreeMap::new(), channels, request_tag }
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.request_tag
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), GetTimestampResponse>)
        ensures
            r@.dom() == self.replies(),
    {
        self.replies
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@.dom()
    }

    pub closed spec fn spec_channels(self) -> Map<C::Id, C> {
        self.channels@
    }
}

impl<C> ReplyAccumulator<C, EmptyPred> for GetTimestampAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response)
        ensures
            self.channels() == old(self).channels(),
    {
        assume(resp.req_type() is GetTimestamp);
        let resp = resp.destruct_get_timestamp();
        // TODO(qed): remove later on
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, resp);
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        clone_domain(&self.replies)
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

impl<C: Channel<K = ChannelInv, Id = (u64, u64)>> WriteAccumulator<C> {
    pub fn new(channels: Ghost<Map<C::Id, C>>, request_tag: u64) -> (r: Self)
        ensures
            r.spec_request_tag() == request_tag,
            r.replies().is_empty(),
            r.spec_channels() == channels@,
    {
        WriteAccumulator { replies: BTreeMap::new(), channels, request_tag }
    }

    pub closed spec fn spec_request_tag(self) -> u64 {
        self.request_tag
    }

    pub fn into(self) -> (r: BTreeMap<(u64, u64), ()>)
        ensures
            r@.dom() == self.replies(),
    {
        self.replies
    }

    pub closed spec fn replies(self) -> Set<C::Id> {
        self.replies@.dom()
    }

    pub closed spec fn spec_channels(self) -> Map<C::Id, C> {
        self.channels@
    }
}

impl<C> ReplyAccumulator<C, EmptyPred> for WriteAccumulator<C> where
    C: Channel<Id = (u64, u64), R = Response, K = ChannelInv>,
 {
    #[allow(unused_variables)]
    #[verifier::exec_allows_no_decreases_clause]
    fn insert(&mut self, pred: Ghost<EmptyPred>, id: (u64, u64), resp: Response)
        ensures
            self.channels() == old(self).channels(),
    {
        assume(resp.req_type() is Write);
        let resp = resp.destruct_write();
        // TODO(qed): remove later on
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        assume(!self.replies@.contains_key(id));
        assert(self.replies@.dom().finite());
        assert(self.replies@.dom().insert(id).len() == self.replies@.dom().len() + 1);
        self.replies.insert(id, ());
    }

    open spec fn request_tag(self) -> u64 {
        self.spec_request_tag()
    }

    open spec fn spec_handled_replies(self) -> Set<C::Id> {
        self.replies()
    }

    fn handled_replies(&self) -> BTreeSet<C::Id> {
        assume(vstd::laws_cmp::obeys_cmp_spec::<(u64, u64)>());
        clone_domain(&self.replies)
    }

    open spec fn channels(self) -> Map<C::Id, C> {
        self.spec_channels()
    }
}

pub struct EmptyPred;

impl<C: Channel<K = ChannelInv>> InvariantPredicate<
    EmptyPred,
    GetTimestampAccumulator<C>,
> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: GetTimestampAccumulator<C>) -> bool {
        true
    }
}

impl<C: Channel<K = ChannelInv>> InvariantPredicate<EmptyPred, WriteAccumulator<C>> for EmptyPred {
    open spec fn inv(pred: EmptyPred, v: WriteAccumulator<C>) -> bool {
        true
    }
}

fn clone_domain<K: Ord + Clone, V>(map: &BTreeMap<K, V>) -> (dom: BTreeSet<K>)
    requires
        vstd::laws_cmp::obeys_cmp_spec::<K>(),
    ensures
        map@.dom() == dom@,
{
    proof {
        admit();  // TODO: prove domain clone
    }
    let map_keys = map.keys();
    assert(map_keys@.0 == 0);
    assert(map_keys@.1.to_set() =~= map@.dom());
    let ghost g_keys = map_keys@.1;

    let mut dom = BTreeSet::new();
    assert(dom@ =~= g_keys.take(0).to_set());

    for k in iter: map_keys
        invariant
            iter.keys == g_keys,
            g_keys == map@.dom().to_seq(),
            increasing_seq(g_keys),
            dom@ == iter@.to_set(),
    {
        assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
        dom.insert(k.clone());
        proof {
            admit();  // TODO: prove domain clone
        }
    }
    dom
}

} // verus!
