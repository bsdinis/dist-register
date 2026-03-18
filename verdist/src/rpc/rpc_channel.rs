use vstd::map::Map;
use vstd::prelude::*;
use vstd::rwlock::RwLock;
use vstd::rwlock::RwLockPredicate;

use crate::network::channel::Channel;
#[cfg(verus_only)]
use crate::network::channel::ChannelInvariant;
use crate::network::error::SendError;

use std::collections::HashMap;
use std::sync::atomic::AtomicU64;

verus! {

struct EmptyCond;

impl<V> RwLockPredicate<V> for EmptyCond {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

pub struct ChannelState<Req, Resp> {
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

    // called on channel.send()
    #[allow(unused_variables)]
    pub fn add_pending(self, request: Req) -> (r: (
        Self,
        RequestTicket<Req>,
    ))
    //requires !self.history@.contains_key(self.current_tag),

        ensures
    //r.0.buffered == self.buffered,
    //r.0.pending == self.pending@.insert(self.current_tag, request),
    //r.0.history == self.history,
    //r.0.current_tag == self.current_tag + 1,
    //r.1.request_tag == self.current_tag,

    {
        proof {
            use_type_invariant(&self);
        }
        #[allow(non_shorthand_field_patterns)]
        let ChannelState { buffered, pending, history, current_tag } = self;
        assume(current_tag < u64::MAX);
        assume(!history@.contains_key(current_tag));

        let Ghost(p) = pending;
        let Ghost(h) = history;
        proof {
            let old_intersect = p.dom().intersect(h.dom());
            let p = p.insert(current_tag, request);
            let new_intersect = p.dom().intersect(h.dom());
            assert(new_intersect =~= old_intersect);
        }

        (
            ChannelState { buffered, pending, history, current_tag: current_tag + 1 },
            RequestTicket { request_tag: current_tag, request: Tracked(request) },
        )
    }

    // called on channel.recv()
    pub fn add_response(self, request_tag: u64, response: Resp) -> (r: Self)
        requires
    //self.pending@.contains_key(request_tag),

        ensures
    //r.buffered@ == self.buffered@.insert(request_tag, response),
    //r.pending == self.pending,
    //r.history == self.history,

    {
        proof {
            use_type_invariant(&self);
            admit();
        }
        #[allow(non_shorthand_field_patterns)]
        let ChannelState { mut buffered, pending, history, current_tag } = self;
        buffered.insert(request_tag, response);
        ChannelState { buffered, pending, history, current_tag }
    }

    // called when channel.poll(id) hits
    pub fn move_request(self, request_tag: u64) -> (r: Self)
        requires
    //self.buffered@.contains_key(request_tag),

        ensures
    //r.buffered@ == self.buffered@.remove(request_tag),
    //r.pending == self.pending@.remove(request_tag),
    //r.history == self.history@.insert(
    //request_tag,
    //(self.pending@[request_tag], self.buffered@[request_tag]),
    //),

    {
        proof {
            use_type_invariant(&self);
            admit();
        }

        #[allow(unused_variables)]
        #[allow(non_shorthand_field_patterns)]
        let ChannelState { mut buffered, pending, history, current_tag } = self;

        let ghost request = pending@[request_tag];
        #[allow(unused_variables)]
        let response = buffered.remove(&request_tag).expect("key exists");

        let Ghost(p) = pending;
        let Ghost(h) = history;
        let ghost new_pending;
        let ghost new_history;
        proof {
            let old_intersect = p.dom().intersect(h.dom());
            new_pending = p.remove(request_tag);
            new_history = h.insert(request_tag, (request, response));
            let new_intersect = p.dom().intersect(h.dom());
            assert(new_intersect =~= old_intersect);
        }

        ChannelState {
            buffered,
            pending: Ghost(new_pending),
            history: Ghost(new_history),
            current_tag,
        }
    }
}

pub struct RpcChannel<C: Channel> {
    #[allow(dead_code)]
    request_tag: AtomicU64,
    channel: C,
    state: RwLock<ChannelState<C::S, C::R>, EmptyCond>,
}

pub struct RequestTicket<Req> {
    #[allow(dead_code)]
    request_tag: u64,
    #[allow(dead_code)]
    request: Tracked<Req>,
}

impl<C: Channel> RpcChannel<C> {
    pub fn async_invoke(&self, request: &C::S) -> Result<RequestTicket<C::S>, SendError<C::S>> {
        assume(C::K::send_inv(self.channel.constant(), self.channel.spec_id(), *request));
        self.channel.send(request)?;
        let (state, handle) = self.state.acquire_write();
        let (new_state, request_ticket) = state.add_pending(request.clone());

        handle.release_write(new_state);

        Ok(request_ticket)
    }

    pub fn poll(&self) {
    }

    // non blocking
    pub fn poll_id(&self) -> Option<C::R> {
        None
    }
}

} // verus!
