------------------------------ MODULE MCFailStopCR ------------------------------------
EXTENDS FailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2
LimitedServerFailures == Cardinality(DOMAIN srvVals) >= 1
=============================================================================