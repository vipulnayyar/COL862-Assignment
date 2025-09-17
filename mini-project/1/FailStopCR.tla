------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE Flag, Current_Tail, Current_Head, srvNext, srvPrev, srvLive, LiveServerCount

FailServers(failed_servers) ==
    
    /\ LiveServerCount' = LiveServerCount - Cardinality(failed_servers)
    /\  \A server \in failed_servers:
        /\ srvLive' = [srvLive EXCEPT ![server] = 0 ]
        /\ Flag' = Flag + 1
        /\  CASE (srvPrev[server] = 0) -> (
                /\ Current_Head' = srvNext[server] 
                /\ srvPrev' = [srvPrev EXCEPT ![ srvNext[server] ] = 0 ] 
                /\ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, srvNext, Current_Tail>>
            )
            [] (srvNext[server] = 0) -> (
                /\ Current_Tail' = srvPrev[server] 
                /\ srvNext' = [srvNext EXCEPT ![ srvPrev[server] ] = 0]
                /\ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, srvPrev, Current_Head>>
            )
            [] OTHER -> (
                /\ srvPrev' = [srvPrev EXCEPT ![ srvNext[server] ] = srvPrev[server] ] 
                /\ srvNext' = [srvNext EXCEPT ![ srvPrev[server] ] = srvNext[server]] 
                /\ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, LiveServerCount, Current_Head, Current_Tail>>
            )


FailStopCRTypeOK == 
    /\ srvVals \in [(1..Current_Tail) -> VALS]
    /\ srvReqs \in [(1..Current_Tail) -> Seq(Req)]
    /\ srvReplied \in [(1..Current_Tail) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
    /\ srvNext \in [(1..Current_Tail) -> (0..Current_Tail)]
    /\ srvPrev \in [(1..Current_Tail) -> (0..Current_Tail)]
    /\ Flag < 1
\*    /\ Cardinality({k \in (DOMAIN srvLive) : srvLive[k] = 1}) > 1

FailStopCRInit == 
    /\ CRInit
    /\ Flag = 0
    /\ Current_Tail = TAIL
    /\ Current_Head = HEAD
    /\ srvNext = [s \in 1..Current_Tail |-> IF s < Current_Tail THEN s+1 ELSE 0]
    /\ srvPrev = [s \in 1..Current_Tail |-> IF s > 1 THEN s-1 ELSE 0]
    /\ srvLive = [s \in 1..Current_Tail |-> 1]
    /\ LiveServerCount = Current_Tail


FailStopCRNext == 
    /\  Flag = 0
    /\  LiveServerCount > 1 
    /\  FailServers({1,2})
(* 
    \E failed_servers \in SUBSET({k \in (DOMAIN srvLive) : srvLive[k] = 1}):
          IF  Cardinality(failed_servers) < LiveServerCount
            THEN
                TRUE 
               \* FailServers(failed_servers) 
            ELSE
                UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals, Current_Tail, Current_Head, srvLive, Flag, LiveServerCount, srvNext, srvPrev>>
*)


(*
FailStopCRNext == 
    /\ FLAG' = 1
    /\ UNCHANGED <<reqs, srvReqs, srvReplied, resps, srvVals>>
*)

FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, Flag, Current_Tail, Current_Head, LiveServerCount, srvLive, srvNext, srvPrev>>

=============================================================================
