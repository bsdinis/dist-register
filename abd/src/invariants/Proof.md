# Invariants

## Quorum

The quorum library defines what a quorum is and what can be learned from having a quorum.
The following definitions are useful:

A _server universe_ is a snapshot of the entire set of servers and their values.
The set of servers is unchanging but over time their values might progress.

A _quorum_ is a subset of the servers. In our case, a quorum is a majority of the servers. (This might change in the future)

The _timestamp of a quorum_ is the maximum timestamp in the quorum wrt a particular server universe.

A _unanimous quorum at timestamp $t$_ is a quorum where all server values are known be lower bounded by $t$.

**Quorum Monotonicity**
If there is a quorum q within the server universe $S_{t_1}$, and we know that the quorum timestamp, for that version of the universe is at least $M$.
Then, if we have a later server universe $S_{t_1} \leq S_{t_2}$, then the quorum timestamp is still at least $M$.
In other words, the quorum cannot regress if the servers progressed.

**Quorum Intersection**
Given a unanimous quorum at timestamp $t$, we know that all other quorums are lower bounded by $t$.
This comes from quorum intersection -- given all quorums intersect, every quorum will at least have one server lower bounded by $t$, meaning the timestamp of the quorum will also be lower bounded by $t$.

## Committment

It is very important to know that clients commit to writing certain values at certain timestamp.
As a baseline, this gives us timestamp uniqueness (i.e., each timestamp points to a unique value) an non-equivocation in a fell swoop.

This is proven with 3 elements:
- A ghost map of the commitments (timestamp to value).
- A ghost map of client counter tokens (client id to supreme of client counters issued).
- A map of permissions to update the client counter.

For the client to allocate a new timestamp, it must first show that it is going to write to an unused timestamp.
To do this, we keep a per client counter of the number of writes done.
By ensuring that we keep track of the maximum counter value issed (in the client counter token), we know that for a particular client, if the request timestamp is above that then it is unused.
We then require the client to present its token (obtained at login) to both get permission to update its exec counter and allocate a new (timestamp, value) pair in the ghost map.

## Linearization Queue

The linearization queue arises from a necessity of the ABD protocol.
In ABD, operations can be linearized by other clients.
E.g., two clients may be writing at the same time and the one with the latter timestamp might finish (in its actual execution) before the earlier one.
Because the linearization order in ABD corresponds to the timestamp order, the latter client must linearize the first one's before linearizing itself.

To give every client access to each other linearizers, the linearization queue is in the global invariant.

It keeps track of the watermark -- the timestamp of the last operation that was linearized.
Every write bellow the watermark is completed (and as such, the completion can be extracted by the appropriate client).
Otherwise, it is pending -- waiting to be linearized.

When inserting a linearizer in the queue, the client receives a token for that write.
When the client can prove the write has completed, they can use the token to retrieve the completion.

Reads are kept in a slightly more complicated fashion.
Because they need to always be associated with a write, they are indexed by the value they will read.
Clients similarly receive a token associated with the read.
When they can prove, by presenting a commitment, that the timestamp is bellow the watermark and that there was a write at that timestamp that committed that value, then we can safely return the read completion.

The linearization queue also keeps track of all the write commitments that have completed.

## Invariant

The invariant is decomposed as follows:
- The value of the linearization queue at the watermark (last applied write) is the value of the register (as tracked by the GhostVar);
- The linearization queue's known timestamps is exactly the same as the allocatted timestamps in the commitments;
- Any quorum in the current server universe is lower bounded by the watermark; This is equivalent of saying that if we have a unanimous quorum at some timestamp, then we can move the watermark to that quorum's value.
