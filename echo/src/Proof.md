# Proof Structure

This module has a proof of an externsion of the ABD register protocol.
The extension has two components: 1) it allows for multiple concurrent writers and 2) it allows for intra-client concurrency (i.e., the client can issue concurrent requests).
In particular the second extension (AFAIK) is non-standard (i.e., current MWMR implementations might have this bug).

This proof is built in 4 components:
1. [Resources](./resource/Proof.md): a monotonic timestamp;
2. [Invariants](./invariants/Proof.md): invariants upheld by the system and supporting structures (linearization queue, commitments, quorum library);
3. [Server](./server/Proof.md): proof of the server code;
4. [Client](./client/Proof.md): proof of the client library.
