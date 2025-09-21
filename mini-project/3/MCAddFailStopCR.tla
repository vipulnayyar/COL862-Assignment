------------------------------ MODULE MCAddFailStopCR ------------------------------------
EXTENDS AddFailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2

LimitedServers == Len(srvVals) <= 2

LimitedServerAddition == NUM_SERVERS_ADDED <= 2
LimitedServerDeletion == NUM_SERVERS_DELETED <= 2
\*DebugConstraints == 
\*    /\ TRUE
\*    /\ Len(srvVals) = 4

=============================================================================