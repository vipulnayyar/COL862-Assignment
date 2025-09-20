------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE STEPS, STEP_TAKEN, Current_Tail, REMOVED_INDICES, srvHist, srvSent, srvAck, srvMaxWriteSeqNumReceived

CONSTANT DEBUG_ENABLE

SequencetoSet(seq) == 
    {seq[i] : i \in DOMAIN seq}

RemoveElementsfromSequence(seq_to_remove_from, filter_seq) ==
    [i \in 1..Cardinality({j \in DOMAIN seq_to_remove_from : seq_to_remove_from[j] \notin  SequencetoSet(filter_seq)}) 
        |-> 
            LET 
                validindexes == 
                    [j \in 1..Len(seq_to_remove_from) 
                        |-> 
                            IF seq_to_remove_from[j] \in SequencetoSet(filter_seq) THEN 0 ELSE j]

                filteredindexes == 
                    SelectSeq(validindexes, LAMBDA x : x > 0)

            IN 
        
                seq_to_remove_from[filteredindexes[i]] 
    ]


\* Send srvSent updates not present in new successor to its srvReqs
FailureRecovery(server_state, server_history, server_sent, server_max_write_seq_num) ==
    [
        i \in 1..Len(server_state)
            |->
                IF i = 1
                THEN
                    server_state[i]
                ELSE
                    server_state[i] \o
                    
                        LET

                        \*CurrentSequenceCount == Len(server_history[i] \o RemoveElementsfromSequence(server_state[i], server_history[i]))
                        
                        CurrentSequenceCount == server_max_write_seq_num[i]

                        PreviousSequenceCount == Len(server_history[i-1])

                        \*PreviousSequenceCount == server_max_write_seq_num[i-1]
                        
                        LengthofPrevSentToTransfer == PreviousSequenceCount - CurrentSequenceCount

                        IN
                           SubSeq(server_sent[i-1], Len(server_sent[i-1]) - LengthofPrevSentToTransfer + 1, LengthofPrevSentToTransfer  )
                    
                    
    ]
    

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



\* Safety Property
InprocessRequestsSafety == 
    \A i \in (1..Current_Tail):
        \A j \in (i..Current_Tail):
            srvHist[i] = srvHist[j] \o RemoveElementsfromSequence(srvSent[i], srvHist[j]) 

\* Safety Property
UpdatePropagationSafety ==
    \A i \in (1..Current_Tail):
        \A j \in (i..Current_Tail):
            SubSeq(srvHist[i], 1, Len(srvHist[j])) = srvHist[j]


DebugTypeOKConstraints ==
    IF DEBUG_ENABLE = 1
    THEN
        /\ STEPS >= 0
\*        /\ STEPS < 10
\*        /\  srvVals[Current_Tail] \notin DEBUG_NEWVALS
\*        /\ Cardinality(srvReplied[Current_Tail].w) < 2
\*        /\ srvVals[Current_Tail] = "v1"
\*        /\ Cardinality(reqs) < 2
\*        /\ Len(resps) < 2

    ELSE
        TRUE

FailStopCRTypeOK == 
    /\ srvVals \in [(1..Current_Tail) -> VALS]
    /\ srvReqs \in [(1..Current_Tail) -> Seq(Req)]
    /\ srvReplied \in [(1..Current_Tail) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
    /\ srvHist \in [(1..Current_Tail) -> Seq(WrReq)]
    /\ srvMaxWriteSeqNumReceived \in [(1..Current_Tail) -> Nat]
    /\ srvSent \in [(1..Current_Tail) -> Seq(WrReq)]
    /\ srvAck \in [(1..Current_Tail) -> SUBSET WID]
    /\ REMOVED_INDICES \in SUBSET(Nat \ {0})
    /\ STEPS \in Nat

   
FailStopCRInit == 
    /\ CRInit
    /\ Current_Tail = TAIL
    /\ srvHist = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvSent = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvAck = [s \in (1..Current_Tail) |-> {}]
    /\ srvMaxWriteSeqNumReceived = [s \in (1..Current_Tail) |-> 0 ]
    /\ STEPS = 0
    /\ REMOVED_INDICES = {}
    /\ STEP_TAKEN = "INIT"

FailureAndRecoveryStep ==    
    /\ UNCHANGED<<reqs, resps>>
    /\ STEP_TAKEN' = "FailureAndRecoveryStep"
    /\ \E indices_to_remove \in SUBSET(1..Current_Tail):
        /\ Cardinality(indices_to_remove) < Current_Tail
        /\ Cardinality(indices_to_remove) > 0
        /\ REMOVED_INDICES' = indices_to_remove
        /\ srvVals' = FailServer(srvVals, indices_to_remove)
        /\ srvReplied' = FailServer(srvReplied, indices_to_remove)
        /\ srvHist' = FailServer(srvHist, indices_to_remove)
        /\ srvSent' = FailServer(srvSent, indices_to_remove)
        /\ srvAck' = FailServer(srvAck, indices_to_remove)
        /\ Current_Tail' = Len(srvVals')
        /\ srvMaxWriteSeqNumReceived' = FailServer(srvMaxWriteSeqNumReceived, indices_to_remove)
\*        /\ srvReqs' = FailServer(srvReqs, indices_to_remove)
        /\ srvReqs' = FailureRecovery(FailServer(srvReqs, indices_to_remove), FailServer(srvHist, indices_to_remove),  FailServer(srvSent, indices_to_remove), FailServer(srvMaxWriteSeqNumReceived, indices_to_remove) )




ModifiedCRIssueRead(rid) ==
    LET op == [id |-> rid] IN
    /\ reqs' = reqs \cup {op}
    /\ srvReqs' = [srvReqs EXCEPT ![Current_Tail] = Append(@, op)]
    /\ UNCHANGED <<srvVals, srvReplied, resps>>

ModifiedCRIssueWrite(wid) ==
    \E v \in VALS:
        LET op == [id |-> wid, v |-> v] IN
        /\ reqs' = reqs \cup {op}
        /\ srvReqs' = [srvReqs EXCEPT ![HEAD] = Append(@, op)]
        /\ srvMaxWriteSeqNumReceived' = [srvMaxWriteSeqNumReceived EXCEPT ![HEAD] = srvMaxWriteSeqNumReceived[HEAD] + 1 ]
        /\ UNCHANGED <<srvVals, srvReplied, resps>>

ModifiedCRServerWrites(op, s) ==
    /\ op.id \in WID
    /\ op.id \notin srvReplied[s].w
    /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.w = @ \union {op.id}]]
    /\ srvHist' = [srvHist EXCEPT ![s] = Append(@, op)]
    /\ srvSent' = [srvSent EXCEPT ![s] = Append(@, op)]
    /\ srvVals' = [srvVals EXCEPT ![s] = op.v]
    /\ \/ /\ s+1 > Current_Tail 
          /\ resps' = Append(resps, [id |-> op.id])
          /\ srvAck' = [srvAck EXCEPT ![s] = @ \union {op.id} ]
          /\ srvReqs' = srvReqs
          /\ UNCHANGED <<srvMaxWriteSeqNumReceived>>
       \/ /\ s+1 <= Current_Tail
          /\ srvReqs' = [srvReqs  EXCEPT ![s+1] = Append(@, op)]
          /\ srvMaxWriteSeqNumReceived' = [srvMaxWriteSeqNumReceived  EXCEPT ![s+1] = srvMaxWriteSeqNumReceived[s+1] + 1 ]
          /\ resps' = resps
          /\ UNCHANGED <<srvAck>>
    /\ UNCHANGED <<reqs>>


BackPropagateAck(s) ==
    /\ s > HEAD
    /\ Cardinality(srvAck[s] \ srvAck[s-1]) > 0
    /\ srvAck' = [srvAck EXCEPT ![s-1] = srvAck[s]]

UpdateSentFromAck(s) ==
    /\ Len(srvSent[s]) > 0
    /\ Head(srvSent[s]) \in srvAck[s]
    /\ srvSent' = [srvSent EXCEPT ![s] = Tail(@)]

ModifiedCRNext == 
    \/ \E rid \in RID: 
        /\ ModifiedCRIssueRead(rid)
        /\ STEP_TAKEN' = "ModifiedCRIssueRead"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail>>
    \/ \E wid \in WID: 
        /\ ModifiedCRIssueWrite(wid) 
        /\ STEP_TAKEN' = "IssueWrite"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<srvAck, srvHist, srvSent, Current_Tail>>
    \/ \E s \in (1..Current_Tail):
        /\ Len(srvReqs[s]) > 0
        /\ LET o == Head(srvReqs[s]) IN
            \/ 
                /\ DropRead(o, s)
                /\ STEP_TAKEN' = "DropRead"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail>>
            \/ 
                /\ DropWrite(o, s)
                /\ STEP_TAKEN' = "DropWrite"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail>>
            \/ 
                /\ ServerReads(o, s)
                /\ STEP_TAKEN' = "ServerReads"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail>>
            \/ 
                /\ ModifiedCRServerWrites(o, s)    
                /\ STEP_TAKEN' = "ModifiedCRServerWrites"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<Current_Tail>>

    \/ 
        /\ \E s \in (1..Current_Tail): BackPropagateAck(s)
        /\ STEP_TAKEN' = "BackPropagateAck"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail>>
        
    \/ 
        /\ \E s \in (1..Current_Tail): UpdateSentFromAck(s)
        /\ STEP_TAKEN' = "UpdateSentFromAck"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvAck, srvHist, srvMaxWriteSeqNumReceived, Current_Tail>>



FailStopCRNext == 
    /\  STEPS' = STEPS + 1
    /\
        \/ FailureAndRecoveryStep
        \/ ModifiedCRNext
            


FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, STEPS, Current_Tail, REMOVED_INDICES, srvHist, srvSent, srvAck, srvHist, STEP_TAKEN, srvMaxWriteSeqNumReceived>>

=============================================================================
