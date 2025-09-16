------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE Flag, Current_Tail



FailAndShiftServerChainBack(failed_servers) == 
    /\ srvVals' = [t \in (1..(Current_Tail-(Cardinality(failed_servers))) |-> IF t < server THEN srvVals[t] ELSE srvVals[t+1]]    
    /\ srvReqs' = [t \in (1..Current_Tail-1) |-> IF t < server THEN srvReqs[t] ELSE srvReqs[t+1]] 
    /\ srvReplied' = [t \in (1..Current_Tail-1) |-> IF t < server THEN srvReplied[t] ELSE srvReplied[t+1]]      
    /\ Flag' = 1
    /\ Current_Tail' = Current_Tail - 1
    /\ UNCHANGED <<reqs, resps>>

FailStopCRTypeOK == 
    /\ srvVals \in [(1..Current_Tail) -> VALS]
    /\ srvReqs \in [(1..Current_Tail) -> Seq(Req)]
    /\ srvReplied \in [(1..Current_Tail) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
    /\ Cardinality(DOMAIN srvVals) > 1

FailStopCRInit == 
    /\ CRInit
    /\ Flag = 0
    /\ Current_Tail = TAIL

FailStopCRNext == 
    \/ \E failed_servers \in (SUBSET (DOMAIN srvVals)):
            IF  Cardinality(failed_servers) < Current_Tail
            THEN
                    FailAndShiftServerChainBack(failed_servers) 
            ELSE
                UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, Current_Tail, Flag>>
    \/ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, Current_Tail, Flag>>

(*
    \/ 
        /\ CRNext
        /\  UNCHANGED <<FLAG>>
*)
    


(*
FailStopCRNext == 
    /\ FLAG' = 1
    /\ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals>>
*)

FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, Flag, Current_Tail>>

=============================================================================
