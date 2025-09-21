
**Learnings**

- In the pipelined syncing approach in this implementation, on addition of one or more servers, Update propagation invariant(History of a server will always be a prefix for all its predecessors) holds for all servers(i<=j), even though they may be catching up from the Tail(through pipelining or directly).

- A Tail that is not sending updates to a new server, does not need to keep a Sent list. It only creates a Sent list when a new server needs updates from the Tail to catchup.

- On Tail failure, read history(srvReplied.r in CR and accepted.r in SS ) is forgotten, and there is no ideal way to recover that history. Theoretically, read history can be recovered from resps(Responses), but in the real-world, regenerating read history state from client responses is not feasible.

- While switching Tail to a newly added and caught-up server, read history can optionally be forgotten or synced from the old Tail. A corresponsing step(ForgetReadHistoryonTail) is added to SS.tla for refinement. Maintaing read history does not practically affect data consistency or safety properties. 

- In refinement of FailStopCR with SS, failure of Tail is seen by SS as forgetting its read history(accepted.r = {} in SS) and potentially getting a new write(if the new Tail, which is a predecessor has a write, that was not seen by the Tail)

**Optimizations**

- During back propagation of Acks in the chain, multiple Acks can be bunched together instead of sending them one by one, thus reducing network traffic, without compromising any safety guarrantees.

- Syncing of History from tail to new servers can be done in a pipeliend manner. This makes catching up of the first new server in the chain faster as it uses Tail's complete outward bandwidth(specially if srvHistory size to sync is really large), compared to a Star based approach, where syncing multiple new servers from Tail can split the outward bandwidth.

 
