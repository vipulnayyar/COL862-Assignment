------------------------------ MODULE MCFailStopCR ------------------------------------
EXTENDS FailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2

DebugConstraints == 
    /\ TRUE
\*    /\ Len(srvVals) = 4


val_bar == srvVals[Current_Tail]
accepted_bar == srvReplied[Current_Tail]

SS == INSTANCE SS WITH
    val <- val_bar
    ,
    accepted <- accepted_bar

SSSpec == SS!SSSpec

=============================================================================