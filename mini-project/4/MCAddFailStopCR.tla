------------------------------ MODULE MCAddFailStopCR ------------------------------------
EXTENDS AddFailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2

\*DebugConstraints == 
\*    /\ TRUE
\*    /\ Len(srvVals) = 4


SS == INSTANCE SS WITH
    val <- srvVals[Current_Tail]
    ,
    accepted <- srvReplied[Current_Tail]

SSSpec == SS!SSSpec

=============================================================================