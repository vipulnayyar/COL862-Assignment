------------------------------ MODULE MCAddFailStopCR ------------------------------------
EXTENDS AddFailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2
LimitedServers == Len(srvVals) <= 4

\*DebugConstraints == 
\*    /\ TRUE
\*    /\ Len(srvVals) = 4

=============================================================================