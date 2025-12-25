# Server Proof

The server's proof is remarkably easy.
The server only holds onto a timestamp, value pair.
When receiving a read request, it returns the current value.
When receiving a write request, it updates its value if the timestamp is greater.

It needs only to certify that the request's lowerbound (which it should come accompanied by), is in fact lower than the current resource.
This effectively ensures that clients never see a server "going back in time".
This is naturally done by the resource algebra.

The other resource the servers need to keep is the commitment from the writer whose value they are holding (i.e., the promise they were writing that value to that timestamp).
This ensures -- in the proof -- that writers do not equivocate. And when a client receives a single commitemnt for a particular timestamp, they can know there is no other value at that timestamp.

## TODOs

- Actually receive a lowerbound on request
- Actually receive/hold the write commitments
