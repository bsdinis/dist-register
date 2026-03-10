# Client Proof

## Write

The proof for writes goes as follows.

1. Prophecize the sequence number we'll write to; Increment the counter and construct the timestamp.
2. Allocate a (timestamp, value) pair, set it to the value we wish to write (only do this if the timestamp is above the watermark);
3. Insert the timestamp in the queue, get back a token. If the prophecized timestamp was below the watermark, return a failure (which implies the allocation didn't happen);
4. After reading from a quorum, resolve the prophecized sequence number to the sequence number of the quorum, incremented;
5. Use the watermark lemma to prove that the insertion succeeded (i.e., the prophecized timestamp was above the watermark). This also means that the allocation did happened.
6. Write to a quorum
7. Apply linearizers up to the timestamp we wrote to (we can do this because we have a unanimous quorum at our timestamp, allowing us to increase the watermark)
8. Extract the completion

**Watermark Lemma**. The watermark lemma proves that after reading from the values and resolving the timestamp, we can learn that our construction was ahead of the watermark at that time.
The proof goes as follows.

Assume we didn't insert in the queue.
1. If we didn't insert in the queue, then our prophecy was below the watermark: $proph\\_ts \leq watermark$
2. By watermark monotonicity, the current watermark is above our initial watermark: $watermark \leq cur\\_watermark$
3. By the invariant, the watermark is bellow all quorums, including the one we got: $cur\\_watermark \leq quorum.ts$
4. By construction, our watermark is strictly greater than the quorum timestamp: $quorum.ts \lt exec\\_ts$
5. We resolved the timestamp, which means that $exec\\_ts == proph\\_ts$.
6. We have arrived at $proph\\_ts \lt proph\\_ts$, reaching the contradiction.

## Read

For reads, we do as follows:

1. Prophecize the value we'll read. Insert the linearizer in the queue (indexed by the value). Obtain the token.
2. Read from a quorum. At this point we can resolve the value we'll read from (the one with the maximum timestamp).
3. If the quorum is unanimous, we can apply the linearizers up to that timestamp immediately. This allows us to move the watermark and return.
4. Otherwise, we issue a write to the replicas falling behind. After that we know that all replicas are at least at the timestamp we'll read from. This allows us to apply the linearizers at least until the write we want.

Note that to justify returning the completion after applying the linearizers, we keep track of the value of the watermark at insertion time.
The queue maintains the invariant that if there is a read token refering to a value that corresponds to a write that happened it's insertion timestamp and the current watermark then the read was linearized.
We can justify this by presenting the write commitment.

## TODO

- Justify the timestamp structure; (why it is what it is and why no client thread id)
- Justify inserting the linearizers as early as we do
- Justify prophecizing read values

