------------------------------ MODULE MCFailStopCR ------------------------------------
EXTENDS FailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2

\*DebugConstraints == 
\*    /\ TRUE
\*    /\ Len(srvVals) = 4

(*
accepted_read == 
    srvReplied[Current_Tail].r 
        \union 
        {
            r.id : r \in
                {   resp \in {resps[i] : i \in DOMAIN resps}
                    :
                    resp \in RdRes
                                
                }
        } 

accepted_write == srvReplied[Current_Tail].w
modified_accepted == [r |-> accepted_read, w |-> accepted_write]
*)

SS == INSTANCE SS WITH
    val <- srvVals[Current_Tail]
    ,
    accepted <- srvReplied[Current_Tail]

SSSpec == SS!SSSpec

=============================================================================