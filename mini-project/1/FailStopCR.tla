------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE DEBUG_STEPS, Current_Tail, DEBUG_REMOVED_INDICES

CONSTANT DEBUG_ENABLE

FailServer(server_state, failed_servers) == 
    [i \in 1..(Len(server_state) - Cardinality(failed_servers)) 
        |->
            LET 
                validindexes == 
                    [j \in 1..Len(server_state) 
                        |-> 
                            IF j \in failed_servers THEN 0 ELSE j]

                filteredindexes == 
                    SelectSeq(validindexes, LAMBDA x : x > 0)

            IN 
                server_state[filteredindexes[i]] ]


DebugTypeOKConstraints ==
    IF DEBUG_ENABLE = 1
    THEN

        /\ DEBUG_STEPS < 10
\*        /\ Cardinality(reqs) < 2
        /\ Len(resps) < 2
        /\ Len(srvVals) = 4

    ELSE
        TRUE

FailStopCRTypeOK == 
    /\ srvVals \in [(1..Len(srvVals)) -> VALS]
    /\ srvReqs \in [(1..Len(srvReqs)) -> Seq(Req)]
    /\ srvReplied \in [(1..Len(srvReplied)) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req

    /\ DebugTypeOKConstraints

DebugInit ==
    /\ DEBUG_STEPS = 0
    /\ DEBUG_REMOVED_INDICES = {}
   
FailStopCRInit == 
    /\ CRInit
    /\ Current_Tail = TAIL
    /\ DebugInit

FailureStep ==    
    /\ \E indices_to_remove \in SUBSET(1..Current_Tail):
        /\ Cardinality(indices_to_remove) < Current_Tail
        /\ DEBUG_REMOVED_INDICES' = indices_to_remove
        /\ srvVals' = FailServer(srvVals, indices_to_remove)
        /\ srvReqs' = FailServer(srvReqs, indices_to_remove)
        /\ srvReplied' = FailServer(srvReplied, indices_to_remove)
        /\ Current_Tail' = Len(srvVals')



ModifiedCRIssueRead(rid) ==
    LET op == [id |-> rid] IN
    /\ reqs' = reqs \cup {op}
    /\ srvReqs' = [srvReqs EXCEPT ![Current_Tail] = Append(@, op)]
    /\ UNCHANGED <<srvVals, srvReplied, resps>>

ModifiedCRServerWrites(op, s) ==
    /\ op.id \in WID
    /\ op.id \notin srvReplied[s].w
    /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.w = @ \union {op.id}]]
    /\ srvVals' = [srvVals EXCEPT ![s] = op.v]
    /\ \/ /\ s+1 > Current_Tail 
          /\ resps' = Append(resps, [id |-> op.id])
          /\ srvReqs' = srvReqs
       \/ /\ s+1 <= Current_Tail
          /\ srvReqs' = [srvReqs  EXCEPT ![s+1] = Append(@, op)]
          /\ resps' = resps
    /\ UNCHANGED <<reqs>>

ModifiedCRNext == 
\*    \/ \E rid \in RID: ModifiedCRIssueRead(rid)
    \/ \E wid \in WID: IssueWrite(wid)
    \/ \E s \in (1..Current_Tail):
        /\ Len(srvReqs[s]) > 0
        /\ LET o == Head(srvReqs[s]) IN
            \/ DropRead(o, s)
            \/ DropWrite(o, s)
            \/ ServerReads(o, s)
            \/ ModifiedCRServerWrites(o, s)    

FailStopCRNext == 
    
    /\  IF DEBUG_ENABLE = 1
        THEN
            DEBUG_STEPS' = DEBUG_STEPS + 1
        ELSE
            UNCHANGED <<DEBUG_STEPS, DEBUG_REMOVED_INDICES>>
    /\
        \/  
            /\ FailureStep
            /\ UNCHANGED <<reqs, resps>>
        \/ 
            /\ ModifiedCRNext
            /\ UNCHANGED  <<Current_Tail, DEBUG_REMOVED_INDICES>>


FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, DEBUG_STEPS, Current_Tail, DEBUG_REMOVED_INDICES>>

=============================================================================
