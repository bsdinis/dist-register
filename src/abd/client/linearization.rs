use crate::abd::proto::Timestamp;
use vstd::logatom::*;
use vstd::prelude::*;
use vstd::tokens::frac::GhostVarAuth;

use crate::abd::client::logatom::*;

verus! {

pub enum MaybeLinearized<ML: MutLinearizer<RegisterWrite>> {
    Linearizer {
        lin: Tracked<ML>,
        op: RegisterWrite,
        timestamp: Timestamp,
    },
    Comp {
        // is GhostVar<Option<u64>>
        completion: Tracked<ML::Completion>,
        timestamp: Timestamp,
    }
}


impl<ML: MutLinearizer<RegisterWrite>> MaybeLinearized<ML> {
    pub fn apply_linearizer(self, register: &mut Tracked<GhostVarAuth<Option<u64>>>, resolved_timestamp: &Timestamp) -> Self {
        match self {
            MaybeLinearized::Linearizer { lin, op, timestamp } => {
                if timestamp <= *resolved_timestamp {
                    // ???? - this is not true
                    let Tracked(l) = lin;
                    let completion = Tracked({
                        l.apply(op, register.borrow_mut(), (), &())
                    });
                    MaybeLinearized::Comp { completion, timestamp }
                } else {
                    MaybeLinearized::Linearizer { lin, op, timestamp }
                }
            },
            completed => completed
        }
    }
}


// IDEA:
//  - insert_linearizer returns a Token
//  - Token can be complemented by the resource given by apply_linearizer
//  - Together, they can be used to extract the completion

pub struct LinearizationQueue<ML: MutLinearizer<RegisterWrite>> {
    pub queue: Tracked<Map<int, MaybeLinearized<ML>>>,

    // everything up to the watermark is guaranteed to be applied
    pub watermark: Ghost<Timestamp>,

    pub curr_token: Ghost<int>,
}

impl<ML: MutLinearizer<RegisterWrite>> LinearizationQueue<ML> {
    // TODO:
    //  - create function to "create" the atomic invariant with the linearization queue in it
    //  - this queue is assumed to be common to all the clients
    pub fn new() -> Self {
        LinearizationQueue {
            queue: Tracked(Map::tracked_empty()),
            watermark: Ghost(Timestamp { seqno: 0, client_id: 0 }),
            curr_token: Ghost(0 as int),
        }
    }

    /// Inserts the linearizer into the linearization queue
    pub fn insert_linearizer(&mut self,
        lin: Tracked<ML>,
        op: RegisterWrite,
        timestamp: Timestamp
    ) -> (r: Tracked<int>)
        requires timestamp.gt(&old(self).watermark@)
    {
        let tracked pushed = MaybeLinearized::Linearizer { lin, op, timestamp };
        self.curr_token = Ghost(self.curr_token@ + 1);
        proof {
            // TODO: generate tokens
            self.queue.borrow_mut().tracked_insert(self.curr_token@, pushed);
        }

        Tracked(self.curr_token)
    }


    /// Applies the linearizer for all writes prophecized to <= timestamp
    // TODO: extract monotonic resource that claims that up to timestamp everything is resolve
    pub fn apply_linearizer(&mut self,
        register: &mut Tracked<GhostVarAuth<Option<u64>>>,
        timestamp: &Timestamp) -> (r: Tracked<()>)
        ensures self.watermark@.ge(timestamp)
    {
        proof {
            *self.queue.borrow_mut() = self.queue@
                .map_values(|v: MaybeLinearized<ML>| v.apply_linearizer(register, timestamp));
        }

        Tracked(())
    }

    /// Return the completion of the write at timestamp - removing it from the sequence
    // TODO: take in the monotonic resource that proves that the particular
    pub fn extract_completion(&mut self, token: Tracked<int>, resource: Tracked<()>) -> (k: Tracked<ML::Completion>)
        // requires { resource claims that the watermark has reached the sufficient point for the timestamp }
        // ensures { somehow the token is related to the completion }
    {
        Tracked({
            let comp = self.queue.borrow_mut().tracked_remove(token@);
            assume(comp is Comp); // this is known because the resource has been given
            comp->completion@
        })
    }
}

}
