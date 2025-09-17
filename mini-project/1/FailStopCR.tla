------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE Flag, Current_Tail, removed_indices

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
        

FailStopCRTypeOK == 
    /\ srvVals \in [(1..Len(srvVals)) -> VALS]
    /\ srvReqs \in [(1..Len(srvReqs)) -> Seq(Req)]
    /\ srvReplied \in [(1..Len(srvReplied)) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
\*    /\ Flag < 3
\*    /\ Len(resps) < 1

FailStopCRInit == 
    /\ CRInit
    /\ Flag = 0
    /\ Current_Tail = TAIL
    /\ removed_indices = {}


FailureStep ==
    /\ Flag' = Flag + 1
    
    /\ \E indices_to_remove \in SUBSET(1..Len(srvVals)):
        /\ Cardinality(indices_to_remove) < Len(srvVals)
        /\ removed_indices' = indices_to_remove
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
    \/ \E rid \in RID: ModifiedCRIssueRead(rid)
          \/ \E wid \in WID: IssueWrite(wid)
          \/ \E s \in (1..Len(srvVals)):
            /\ Len(srvReqs[s]) > 0
            /\ LET o == Head(srvReqs[s]) IN
                \/ DropRead(o, s)
                \/ DropWrite(o, s)
                \/ ServerReads(o, s)
                \/ ModifiedCRServerWrites(o, s)    

FailStopCRNext == 
    \/ 
        /\ FailureStep
        /\ UNCHANGED <<reqs, resps>>
    \/ 
        /\ ModifiedCRNext
        /\ UNCHANGED  <<Current_Tail, removed_indices, Flag>>


FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, Flag, Current_Tail, removed_indices>>

=============================================================================
