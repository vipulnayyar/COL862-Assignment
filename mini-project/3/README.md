
**Approach**

Similar to Q1, the state of each server is maintained in sequences(array) with each element of the array representing a specific type of information about that server. Information related to HEAD is always stored at the first location in the sequence, and similarly, information about TAIL is always stored at the last location in the sequence.
The successor-predecessor links in the CR chain are implicitly maintained by servers being adjacent to each other in the sequence, even after failures.

Failure of a server is modeled by deleting the specific element from the sequence. Head and Tail can also be deleted. At most N-1 servers can be deleted.

The following variables are used to store state information about servers in a chain:

- STEPS : A counter that increases by 1 on each step
- STEP_TAKEN : A string variable that stores the current step being taken
- Current_Tail : stores current position of Tail across failures and normal operations. In CR, TAIL is a constant that cannot change.
- REMOVED_INDICES : Stores set of indices in srvVals that are failed/deleted in FailureAndRecoveryStep
- srvHist : Maintains sequence of write updates for each server
- srvSent : Maintains sequence of write updates sent by a server for which it has not received an Ack
- srvAck : Stores set of updates for which a server has received an Ack, based on which corresponding entry can be deleted from srvSent
- srvMaxWriteSeqNumReceived : Max sequence number of the last update received by a server

The following steps are allowed:

- ModifiedCRNext
    - ModifiedCRIssueRead : Similar to CR IssueRead, but uses Current_Tail instead of TAIL from CR and ensures that a unique read is only added to the request queue of Tail once, by checking its presence in reqs set.
    - ModifiedCRIssueWrite : Similar to CR IssueWrite, but uses Current_Tail instead of TAIL from CR and ensures that a unique write is only added to the request queue of Tail once, by checking its presence in reqs set.
    - DropRead(from CR.tla)
    - DropWrite(from CR.tla)
    - ServerReads(from CR.tla)
    - ModifiedCRServerWrites : Similar to CR ServerWrites, but uses Current_Tail instead of TAIL, and adds sent writes to the Sent sequence on each non-Tail server. Also generates Ack for a write if it is written to Tail.
    - BackPropagateAck : If a server has Acks that are not present in its predecessor, then those unseen Acks are sent to the immediate predecessor on the chain.
    - UpdateSentFromAck : If an Ack for a write in the head of Sent list is found, that write is removed from Sent, which implies that Tail has seen this Write.

- FailureAndRecoveryStep : For all possible sets of servers in the chain, assuming atleast one server is always live, one or more servers are failed in the chain, and its neighbors are synced after deletion in a single step.


Following major safety invariants are used:

- UpdatePropagationSafety : Ensures that for all (non-new)servers, their history sequence(`srvHist`) is a prefix for all its predecessor histories
- InprocessRequestsSafety : Ensures that for all (non-new)servers i,j in the chain, where `i<=j`, `srvHist[i] = srvHist[j] + Sent[i]` (Here + represents combining two sequences where no duplicates are present and total order among updates are maintained)


Following Liveness properties are used:

- AddFailStopLiveness : For all requests in `reqs`, it always happens that the request is eventually found in `resps`
- EventuallySyncwithNewServers : It always happens that eventually Current_Tail and False_Tail will be equal. On addition of new servers, Current_Tail and False_Tail becomes unequal, they should eventually be equal implying that new servers and eventually synced with the Tail, and Tail is moved to the new server.
