
**Learnings**

1) Syncing of History from tail to new servers can be done in a pipeliend manner.

2) In the pipelined syncing approach in this implementation, on addition of one or more servers, Update propagation invariant(History of a server will always be a prefix for all its predecessors) holds for all servers(i<=j), even though they may be catching up from the Tail(through pipelining or directly).

3) A Tail that is not sending updates to a new server, does not need to keep a Sent list. It only creates a Sent list when a new server needs updates from the Tail to catchup.

4) On Tail failure, read history(srvReplied.r in CR an accepted.r in SS ) is forgotten, and there is no ideal way to recover that history. Theoretically, read history can be recovered from resps(Responses), but in the real-world regenerating state from client responses is not feasible.

**Optimizations**
1) During back propagation of Acks in the chain, multiple Acks can be bunched together instead of sending them one by one, thus reducing network traffic, without compromising any safety guarrantees.
2) 
