------------------------------ MODULE FailStopCR ------------------------------------
(* Fail Stop Chain Replication Spec *)

EXTENDS CR, FiniteSets

VARIABLE DEBUG_STEPS, DEBUG_STEP_TAKEN, Current_Tail, DEBUG_REMOVED_INDICES, srvHist, srvSent, srvAck

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
FailureRecovery(server_state, server_history, server_sent) ==
    [
        i \in 1..Len(server_state)
            |->
                IF i = 1
                THEN
                    server_state[i]
                ELSE
                    Append(server_state[i], 
                    
                        LET

                        CurrentSequenceCount == Len(server_history[i] \o RemoveElementsfromSequence(server_state[i], server_history[i]))
                        PreviousSequenceCount == Len(server_history'[i-1])
                        LengthofPrevSentToTransfer == PreviousSequenceCount - CurrentSequenceCount

                        IN
                           SubSeq(server_sent[i-1], Len(server_sent[i-1]) - LengthofPrevSentToTransfer + 1, LengthofPrevSentToTransfer  )
                    
                    )
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



CONSTANT  DEBUG_NEWVALS

DebugTypeOKConstraints ==
    IF DEBUG_ENABLE = 1
    THEN
\*        /\ TRUE
        /\ DEBUG_STEPS < 15
\*        /\  srvVals[Current_Tail] \notin DEBUG_NEWVALS
\*        /\ Cardinality(srvReplied[Current_Tail].w) < 2
\*        /\ srvVals[Current_Tail] = "v1"
\*        /\ Cardinality(reqs) < 2
\*        /\ Len(resps) < 2

    ELSE
        TRUE

FailStopCRTypeOK == 
    /\ srvVals \in [(1..Len(srvVals)) -> VALS]
    /\ srvReqs \in [(1..Len(srvReqs)) -> Seq(Req)]
    /\ srvReplied \in [(1..Len(srvReplied)) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req


DebugInit ==
    /\ DEBUG_STEPS = 0
    /\ DEBUG_REMOVED_INDICES = {}
    /\ DEBUG_STEP_TAKEN = "INIT"
   
FailStopCRInit == 
    /\ CRInit
    /\ Current_Tail = TAIL
    /\ srvHist = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvSent = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvAck = [s \in (1..Current_Tail) |-> {}]
    /\ DebugInit

FailureStep ==    
    /\ DEBUG_STEP_TAKEN' = "FailureStep"
    /\ \E indices_to_remove \in SUBSET(1..Current_Tail):
        /\ Cardinality(indices_to_remove) < Current_Tail
        /\ DEBUG_REMOVED_INDICES' = indices_to_remove
        /\ srvVals' = FailServer(srvVals, indices_to_remove)
        /\ srvReplied' = FailServer(srvReplied, indices_to_remove)
        /\ srvHist' = FailServer(srvHist, indices_to_remove)
        /\ srvSent' = FailServer(srvSent, indices_to_remove)
        /\ srvAck' = FailServer(srvAck, indices_to_remove)
        /\ Current_Tail' = Len(srvVals')
\*        /\ srvReqs' = FailServer(srvReqs, indices_to_remove)
        /\ srvReqs' = FailureRecovery(FailServer(srvReqs, indices_to_remove), FailServer(srvHist, indices_to_remove), FailServer(srvSent, indices_to_remove))




ModifiedCRIssueRead(rid) ==
    LET op == [id |-> rid] IN
    /\ reqs' = reqs \cup {op}
    /\ srvReqs' = [srvReqs EXCEPT ![Current_Tail] = Append(@, op)]
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
       \/ /\ s+1 <= Current_Tail
          /\ srvReqs' = [srvReqs  EXCEPT ![s+1] = Append(@, op)]
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
        /\ DEBUG_STEP_TAKEN' = "ModifiedCRIssueRead"
        /\ UNCHANGED <<srvAck, srvHist, srvSent>>
    \/ \E wid \in WID: 
        /\ IssueWrite(wid) 
        /\ DEBUG_STEP_TAKEN' = "IssueWrite"
        /\ UNCHANGED <<srvAck, srvHist, srvSent>>
    \/ \E s \in (1..Current_Tail):
        /\ Len(srvReqs[s]) > 0
        /\ LET o == Head(srvReqs[s]) IN
            \/ 
                /\ DropRead(o, s)
                /\ DEBUG_STEP_TAKEN' = "DropRead"
                /\ UNCHANGED <<srvAck, srvHist, srvSent>>
            \/ 
                /\ DropWrite(o, s)
                /\ DEBUG_STEP_TAKEN' = "DropWrite"
                /\ UNCHANGED <<srvAck, srvHist, srvSent>>
            \/ 
                /\ ServerReads(o, s)
                /\ DEBUG_STEP_TAKEN' = "ServerReads"
                /\ UNCHANGED <<srvAck, srvHist, srvSent>>
            \/ 
                /\ ModifiedCRServerWrites(o, s)    
                /\ DEBUG_STEP_TAKEN' = "ModifiedCRServerWrites"

    \/ 
        /\ \E s \in (1..Current_Tail): BackPropagateAck(s)
        /\ DEBUG_STEP_TAKEN' = "BackPropagateAck"
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvHist, srvSent>>
        
    \/ 
        /\ \E s \in (1..Current_Tail): UpdateSentFromAck(s)
        /\ DEBUG_STEP_TAKEN' = "UpdateSentFromAck"
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvAck, srvHist>>





FailStopCRNext == 
    
    /\  IF DEBUG_ENABLE = 1
        THEN
            DEBUG_STEPS' = DEBUG_STEPS + 1
        ELSE
            UNCHANGED <<DEBUG_STEPS, DEBUG_REMOVED_INDICES, DEBUG_STEP_TAKEN >>
    /\
        \/  
            /\ FailureStep
            /\ UNCHANGED <<reqs, resps>>
        \/ 
            /\ ModifiedCRNext
            /\ UNCHANGED  <<Current_Tail, DEBUG_REMOVED_INDICES>>


FailStopCRSpec == FailStopCRInit /\ [][FailStopCRNext]_<<srvReplied, srvVals, srvReqs, resps, reqs, DEBUG_STEPS, Current_Tail, DEBUG_REMOVED_INDICES, srvHist, srvSent, srvAck, srvHist, DEBUG_STEP_TAKEN>>

=============================================================================
