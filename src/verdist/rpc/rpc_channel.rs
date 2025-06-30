#![allow(non_shorthand_field_patterns)]
#![allow(unused_variables)]
#![allow(dead_code)]

use vstd::map::Map;
use vstd::prelude::*;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;

use crate::verdist::network::channel::Channel;
use crate::verdist::network::error::SendError;

use std::collections::HashMap;
use std::sync::atomic::AtomicU64;

verus! {

struct EmptyCond;

impl<V> RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

struct ChannelState<Req, Resp> {
    // replies that have not yet been polled
    buffered: HashMap<u64, Resp>,

    // requests that have been sent
    pending: Ghost<Map<u64, Req>>,

    // resolved req/resp
    history: Ghost<Map<u64, (Req, Resp)>>,

    current_tag: u64,
}

impl<Req, Resp> ChannelState<Req, Resp> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.pending@.dom().intersect(self.history@.dom()).len() == 0
        &&& self.buffered@.dom().subset_of(self.pending@.dom())
        &&& self.pending@.dom().finite()
        &&& self.history@.dom().finite()
        &&& self.current_tag <= u64::MAX
    }

    fn empty() -> Self {
        let buffered = HashMap::new();
        let pending = Ghost(Map::empty());
        let history = Ghost(Map::empty());

        assert(pending@.dom().intersect(history@.dom()) == Set::<u64>::empty());

        ChannelState {
            buffered,
            pending,
            history,
            current_tag: 0
        }
    }

    // called on channel.send()
    fn add_pending(self, request: Req) -> (r: (Self, RequestTicket<Req>))
        //requires !self.history@.contains_key(self.current_tag),
        ensures
            r.0.buffered == self.buffered,
            r.0.pending == self.pending@.insert(self.current_tag, request),
            r.0.history == self.history,
            r.0.current_tag == self.current_tag + 1,
            r.1.request_tag == self.current_tag,
    {
        proof {
            use_type_invariant(&self);
        }
        let ChannelState { buffered, pending, history, current_tag } = self;
        assume(current_tag < u64::MAX);
        assume(!history@.contains_key(current_tag));


        let old_intersect = Ghost(pending@.dom().intersect(history@.dom()));
        let pending = Ghost(pending@.insert(current_tag, request));
        let new_intersect = Ghost(pending@.dom().intersect(history@.dom()));

        assert(new_intersect =~= old_intersect);

        (
            ChannelState { buffered, pending, history, current_tag: current_tag + 1 },
            RequestTicket { request_tag: current_tag, request: Tracked(request) }
        )
    }

    // called on channel.recv()
    fn add_response(self, request_tag: u64, response: Resp) -> (r: Self)
        requires
            self.pending@.contains_key(request_tag),
        ensures
            r.buffered@ == self.buffered@.insert(request_tag, response),
            r.pending == self.pending,
            r.history == self.history,
    {
        proof {
            use_type_invariant(&self);
        }
        let ChannelState { mut buffered, pending, history, current_tag } = self;
        buffered.insert(request_tag, response);
        ChannelState { buffered, pending, history, current_tag }
    }

    // called when channel.poll(id) hits
    fn move_request(self, request_tag: u64) -> (r: Self)
        requires
            self.buffered@.contains_key(request_tag),
        ensures
            r.buffered@ == self.buffered@.remove(request_tag),
            r.pending == self.pending@.remove(request_tag),
            r.history == self.history@.insert(request_tag, (self.pending@[request_tag], self.buffered@[request_tag])),
    {
        proof {
            use_type_invariant(&self);
        }

        let ChannelState {
            mut buffered,
            #[allow(unused_assignments)]
            mut pending,
            #[allow(unused_assignments)]
            mut history,
            current_tag,
        } = self;

        #[allow(unused_variables)]
        let request = Ghost(pending@[request_tag]);
        #[allow(unused_variables)]
        let response = buffered.remove(&request_tag).expect("key exists");

        #[allow(unused_variables)]
        let old_intersect = Ghost(pending@.dom().intersect(history@.dom()));
        pending = Ghost(pending@.remove(request_tag));
        history = Ghost(history@.insert(request_tag, (request@, response)));
        #[allow(unused_variables)]
        let new_intersect = Ghost(pending@.dom().intersect(history@.dom()));
        assert(new_intersect =~= old_intersect);

        ChannelState { buffered, pending, history, current_tag }
    }
}

pub struct RpcChannel<C: Channel> {
    request_tag: AtomicU64,
    channel: C,
    state: RwLock<ChannelState<C::S, C::R>, EmptyCond>,
}

pub struct RequestTicket<Req> {
    request_tag: u64,
    request: Tracked<Req>,
}

impl<C: Channel> RpcChannel<C> {
    pub fn async_invoke(&self, request: &C::S) -> Result<RequestTicket<C::S>, SendError<C::S>> {
        self.channel.send(request)?;
        let (state, handle) = self.state.acquire_write();
        let (new_state, request_ticket) = state.add_pending(request.clone());

        handle.release_write(new_state);

        Ok(request_ticket)
    }

    pub fn poll(&self) {
    }

    // non blocking
    pub fn poll_id(&self, ) -> Option<C::R> {
        None
    }
}

}
