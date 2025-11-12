------------------------------ MODULE AddFailStopCR ------------------------------------

EXTENDS CR, FiniteSets

VARIABLE
    STEPS, \* A counter that increases by 1 on each step
    STEP_TAKEN, \* A string variable that stores the current step being taken
    Current_Tail, \* stores current position of Tail across failures and normal operations. In CR, TAIL is a constant that cannot change.
    REMOVED_INDICES, \* Stores set of indices in srvVals that are failed/deleted in FailureAndRecoveryStep
    srvHist, \* Maintains sequence of write updates for each server
    srvSent, \* Maintains sequence of write updates sent by a server for which it has not received an Ack
    srvAck, \* Stores set of updates for which a server has received an Ack, based on which corresponding entry can be deleted from srvSent
    srvMaxWriteSeqNumReceived, \* Max sequence number of the last update received by a server
    False_Tail, \* Tracks last element in a chain which has not caught up. If all servers have caught up, this is equal to Current_Tail
    NUM_SERVERS_DELETED, \* Var to keep track of how many servers have been deleted since the beginning
    NUM_SERVERS_ADDED \* Var to keep track of how many servers have been added since the beginning

CONSTANT DEBUG_ENABLE

(* Helper function to create a set from elements of a Sequence *)
SequencetoSet(seq) == 
    {seq[i] : i \in DOMAIN seq}

(* Sync reads from resps to last server, needed in case Tail fails *)
SyncSrvRepliedReadsFromResps(srvRepliedState, respsState) ==
    [   i \in 1..Len(srvRepliedState) 
        |-> 
        IF 
            i = Len(srvRepliedState) 
        THEN 
            [   r |-> 
                    srvRepliedState[i].r 
                    \union  
                    {
                        r.id : r \in
                            {   resp \in {respsState[j] : j \in DOMAIN respsState}
                                :
                                resp \in RdRes
                                            
                            }
                    }
                , 
                w |-> srvRepliedState[i].w]  
        ELSE 
            srvRepliedState[i] ]



(* Helper function to return a new sequence from elements in argument 1 seq, that are not present in argument 2 seq*)
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


(* After Failure of a Server S between S- and S+, there can be updates that S- sent to S, but were not received by S+. As part of Failure Recovery, the updates not seen by S+, but sent by S- are sent again to S+, to make the Inprocess Requests Invariant True. The suffix of srvSent of S- to be sent is calculated based on srvMaxWriteSeqNumReceived stored by S-, and subtracting it from srvHist of S-, which is the maximum writes sent by S-. *)
FailureRecovery(server_state, server_history, server_sent, server_max_write_seq_num, temp_tail) ==
    [
        i \in 1..Len(server_state)
            |->
                IF (i = 1 \/ i > temp_tail)
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
    

(*State of multiple servers and stored in sequence. Failing a server means deleting an element from that sequence, so that  successor and predecessor relationships are implicit based on adjacent neighbors in the new sequence. For a failure, from each srv variable, elements are deleted that are passed in set failed_servers.*)
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



\* Safety Property added separately as invariant in cfg file
InprocessRequestsSafety == 
    \A i \in (1..Current_Tail):
        \A j \in (i..Current_Tail):
            srvHist[i] = srvHist[j] \o RemoveElementsfromSequence(srvSent[i], srvHist[j]) 

\* Safety Property added separately as invariant in cfg file
UpdatePropagationSafety ==
    \A i \in (1..Current_Tail):
        \A j \in (i..Current_Tail):
            SubSeq(srvHist[i], 1, Len(srvHist[j])) = srvHist[j]


(* Debug Invariant only used when DEBUG_ENABLE constant is 1 in cfg. Does not affect actual FailStopCR spec*)
DebugTypeOKInvariants ==
    IF DEBUG_ENABLE = 1
    THEN
        /\ STEPS >= 0
        /\ ~(STEPS = 12)
\*        /\ ~(
\*            /\  False_Tail > Current_Tail 
\*            /\ STEP_TAKEN = "FailureAndRecoveryStep"
\*            ) 
     
    ELSE
        TRUE

(*Safety properties for all Variables*)
AddFailStopCRTypeOK == 
    /\ srvVals \in [(1..False_Tail) -> VALS]
    /\ srvReqs \in [(1..False_Tail) -> Seq(Req)]
    /\ srvReplied \in [(1..False_Tail) -> [r: SUBSET RID, w: SUBSET WID]]
    /\ resps \in Seq(Res)
    /\ reqs \subseteq Req
    /\ srvHist \in [(1..False_Tail) -> Seq(WrReq)]
    /\ srvMaxWriteSeqNumReceived \in [(1..False_Tail) -> Nat]
    /\ srvSent \in [(1..False_Tail) -> Seq(WrReq)]
    /\ srvAck \in [(1..False_Tail) -> SUBSET WID]
    /\ REMOVED_INDICES \in SUBSET(Nat \ {0})
    /\ STEPS \in Nat

   
(* Setting initial values of all variables *)
AddFailStopCRInit == 
    /\ CRInit
    /\ Current_Tail = TAIL
    /\ srvHist = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvSent = [s \in (1..Current_Tail) |-> <<>>]
    /\ srvAck = [s \in (1..Current_Tail) |-> {}]
    /\ srvMaxWriteSeqNumReceived = [s \in (1..Current_Tail) |-> 0 ]
    /\ STEPS = 0
    /\ REMOVED_INDICES = {}
    /\ STEP_TAKEN = "INIT"
    /\ False_Tail = TAIL
    /\ NUM_SERVERS_DELETED = 0
    /\ NUM_SERVERS_ADDED = 0

(* Failure and Recovery of new successor/predecessor relationships are done in this step*)
FailureAndRecoveryStep ==    
    /\ UNCHANGED<<reqs, resps, NUM_SERVERS_ADDED>>
    /\ STEP_TAKEN' = "FailureAndRecoveryStep"
    /\ \E indices_to_remove \in SUBSET(1..Current_Tail):
        /\ Cardinality(indices_to_remove) < Current_Tail
        /\ Cardinality(indices_to_remove) > 0
        /\ REMOVED_INDICES' = indices_to_remove
        /\ NUM_SERVERS_DELETED' = NUM_SERVERS_DELETED + Cardinality(indices_to_remove)
        /\ srvVals' = FailServer(srvVals, indices_to_remove)
        /\ srvHist' = FailServer(srvHist, indices_to_remove)
        /\ srvSent' = FailServer(srvSent, indices_to_remove)
        /\ srvAck' = FailServer(srvAck, indices_to_remove)
        /\ Current_Tail' = Current_Tail - Cardinality(indices_to_remove)
        /\ False_Tail' = False_Tail - Cardinality(indices_to_remove)
        /\ srvMaxWriteSeqNumReceived' = FailServer(srvMaxWriteSeqNumReceived, indices_to_remove)
        /\ srvReqs' = FailureRecovery(FailServer(srvReqs, indices_to_remove), FailServer(srvHist, indices_to_remove),  FailServer(srvSent, indices_to_remove), FailServer(srvMaxWriteSeqNumReceived, indices_to_remove), Current_Tail - Cardinality(indices_to_remove) )
        /\ resps' = resps \o RemoveElementsfromSequence(FailServer(srvSent, indices_to_remove)[Current_Tail'], resps) \* Sending Writes to resps if Tail is removed
        /\ srvReplied' = FailServer(srvReplied, indices_to_remove)
\*        /\ srvReplied' = SyncSrvRepliedReadsFromResps(FailServer(srvReplied, indices_to_remove), resps) \* Updating srvReplied reads in the new pre-tail server from resps(Needed for refinement mapping with SS)


AddNewServertoChain(num_new_servers) ==
    /\ STEP_TAKEN' = "AddNewServertoChain"
    /\ NUM_SERVERS_ADDED' = NUM_SERVERS_ADDED + num_new_servers
    /\ srvVals' = [ i \in 1..(Len(srvVals) + num_new_servers) |-> IF i <= Len(srvVals) THEN srvVals[i] ELSE INITVAL]
    /\ srvReqs' = [ i \in 1..(Len(srvReqs) + num_new_servers) |-> IF i <= Len(srvReqs) THEN srvReqs[i] ELSE <<>>]
    /\ srvReplied' = [ i \in 1..(Len(srvReplied) + num_new_servers) |-> IF i <= Len(srvReplied) THEN srvReplied[i] ELSE [r |-> {}, w |-> {}]]
    /\ srvHist' = [ i \in 1..(Len(srvHist) + num_new_servers) |-> IF i <= Len(srvHist) THEN srvHist[i] ELSE <<>>]
    /\ srvSent' = [ i \in 1..(Len(srvSent) + num_new_servers) |-> IF i <= Len(srvSent) THEN srvSent[i] ELSE <<>>]
    /\ srvAck' = [ i \in 1..(Len(srvAck) + num_new_servers) |-> IF i <= Len(srvAck) THEN srvAck[i] ELSE {}]
    /\ srvMaxWriteSeqNumReceived' = [ i \in 1..(Len(srvMaxWriteSeqNumReceived) + num_new_servers) |-> IF i <= Len(srvMaxWriteSeqNumReceived) THEN srvMaxWriteSeqNumReceived[i] ELSE 0]
    /\ UNCHANGED  <<reqs, resps, REMOVED_INDICES, Current_Tail, NUM_SERVERS_DELETED>>
    /\ False_Tail' = False_Tail + num_new_servers
    
ShiftCurrentTailToNewServer ==
    /\  STEP_TAKEN' = "ShiftCurrentTailToNewServer"
    /\  Current_Tail < Len(srvVals)
    /\  srvHist[Current_Tail] = srvHist[Current_Tail + 1] \o RemoveElementsfromSequence(srvSent[Current_Tail], srvHist[Current_Tail + 1]) \* Checking InProcess Requests Invariant which implies Tail can be shifted to new node.

    (* Applying elements of Sent from old Tail to new Tail, such that both srvHist of new and old Tail are same *)
    /\ srvHist' = [srvHist EXCEPT ![Current_Tail+1] = srvHist[Current_Tail + 1] \o RemoveElementsfromSequence(srvSent[Current_Tail], srvHist[Current_Tail + 1]) ]
    /\ srvSent' = srvSent
    
    /\ srvReqs' = srvReqs
\*    /\ srvReqs' = [srvReqs EXCEPT ![Current_Tail + 1] = srvSent[Current_Tail] ]

    /\ srvReplied' = 
        [
            s \in 1..False_Tail 
            |->
            IF s = Current_Tail
            THEN
                [ 
                    r |-> {}, \* Deleting read history from server which is not going to be TAIL in the next state
                    w |-> srvReplied[s].w
                ]
            ELSE
                IF s = Current_Tail + 1 \* New Tail in next state
                THEN 
                    [ 
                        \* Syncing read history from old Tail to new Tail, can also be deleted, as history can be large, and does not affect data consistency of SS
                        r |-> srvReplied[s-1].r, 
                        
                        \* New Tail aready has partial write history from old Tail due to srvHist sync. The rest will be updated, when writes received from srvSent of old Tail will be applied
                        w |-> srvReplied[s].w \union srvReplied[s-1].w
                    ]

                ELSE 
                    srvReplied[s]
        ]
    
    /\ Current_Tail' = Current_Tail + 1
    /\ srvVals' = 
        [
            srvVals EXCEPT ![Current_Tail+1] = 
            IF Len(srvSent[Current_Tail]) > 0
            THEN
                srvSent[Current_Tail][Len(srvSent[Current_Tail])].v 
            ELSE
                srvVals[Current_Tail+1]
        ]


    /\ UNCHANGED  <<reqs, resps, REMOVED_INDICES, False_Tail,srvAck, srvMaxWriteSeqNumReceived, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED >>
    
    
SyncHistoryWithNewServer ==
    /\  STEP_TAKEN' = "SyncHistoryWithNewServer"
    /\  Current_Tail < False_Tail
    /\ srvHist[Current_Tail] # srvHist[Current_Tail + 1] \o RemoveElementsfromSequence(srvSent[Current_Tail], srvHist[Current_Tail + 1]) \* Checking In process request invariant is till not TRUE, keep syncing History from Tail to new server.
    /\  srvHist' = 
        [
            s   \in 1..False_Tail 
            |-> 
            IF  
                /\ s > Current_Tail 
                /\ Len(srvHist[s]) < Len(srvHist[s-1])
            THEN 
                Append(srvHist[s], srvHist[s-1][Len(srvHist[s]) + 1])
            ELSE
                srvHist[s]                        
        ]
    /\  srvMaxWriteSeqNumReceived' = 
            [
                s   \in 1..False_Tail 
                |-> 
                IF  
                    /\ s > Current_Tail 
                    /\ Len(srvHist[s]) < Len(srvHist[s-1])
                THEN 
                    srvMaxWriteSeqNumReceived[s] + 1
                ELSE
                    srvMaxWriteSeqNumReceived[s]                        
            ]

    /\  srvReplied' = 
        [
            s   \in 1..False_Tail 
            |-> 
            IF  
                s > Current_Tail /\ Len(srvHist[s]) < Len(srvHist[s-1])
            THEN 
                [
                    r |-> srvReplied[s].r, 
                    w |-> 
                        srvReplied[s].w 
                        \union 
                        { srvHist[s-1][Len(srvHist[s]) + 1].id }]
            ELSE
                srvReplied[s]                        
        ]

    /\  srvVals' = 
            [
                s   \in 1..False_Tail 
                |-> 
                IF  
                    /\ s > Current_Tail 
                    /\ Len(srvHist[s]) < Len(srvHist[s-1])
                THEN 
                    srvHist[s-1][Len(srvHist[s]) + 1].v
                ELSE
                    srvVals[s]                        
            ]

    
    /\ UNCHANGED <<Current_Tail, False_Tail, REMOVED_INDICES, reqs, resps, srvAck, srvReqs, srvSent, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>
    

(* Modifying IssueRead step from CR as it used a constant TAIL, but due to failures, Current_Tail is used here which is updated on each failure*)
ModifiedCRIssueRead(rid) ==
    LET op == [id |-> rid] IN
    /\ op \notin reqs
    /\ reqs' = reqs \cup {op}
    /\ srvReqs' = [srvReqs EXCEPT ![Current_Tail] = Append(@, op)]
    /\ UNCHANGED <<srvVals, srvReplied, resps, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>

(* Modifying IssueWrite step from CR to increase srvMaxWriteSeqNumReceived on HEAD *)
ModifiedCRIssueWrite(wid) ==
    \E v \in VALS:
        LET op == [id |-> wid, v |-> v] IN
        /\ op \notin reqs
        /\ reqs' = reqs \cup {op}
        /\ srvReqs' = [srvReqs EXCEPT ![HEAD] = Append(@, op)]
        /\ srvMaxWriteSeqNumReceived' = [srvMaxWriteSeqNumReceived EXCEPT ![HEAD] = srvMaxWriteSeqNumReceived[HEAD] + 1 ]
        /\ UNCHANGED <<srvVals, srvReplied, resps, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>

(* Modifying ServerWrites step from CR to store srvHist, srvAck, srvSent, srvMaxWriteSeqNumReceived and on each server*)
ModifiedCRServerWrites(op, s) ==
    /\ op.id \in WID
    /\ op.id \notin srvReplied[s].w
    /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.w = @ \union {op.id}]]
    /\ srvHist' = [srvHist EXCEPT ![s] = Append(@, op)]
    /\ srvVals' = [srvVals EXCEPT ![s] = op.v]
    /\ \/ /\ s+1 > Current_Tail 
          /\ resps' = Append(resps, [id |-> op.id])
          /\ srvAck' = [srvAck EXCEPT ![s] = @ \union {op.id} ]
          /\ srvReqs' = srvReqs
          /\ IF False_Tail > Current_Tail
             THEN
                \* Start adding updates to Sent in Tail when syncing with a new server
                srvSent' = [srvSent EXCEPT ![s] = Append(@, op)]
             ELSE 
                srvSent' = srvSent
          /\ UNCHANGED <<srvMaxWriteSeqNumReceived>>
       \/ /\ s+1 <= Current_Tail
          /\ srvSent' = [srvSent EXCEPT ![s] = Append(@, op)]
          /\ srvReqs' = [srvReqs  EXCEPT ![s+1] = Append(@, op)]
          /\ srvMaxWriteSeqNumReceived' = [srvMaxWriteSeqNumReceived  EXCEPT ![s+1] = srvMaxWriteSeqNumReceived[s+1] + 1 ]
          /\ resps' = resps
          /\ UNCHANGED <<srvAck>>
    /\ UNCHANGED <<reqs, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>

ModifiedCRServerReads(op, s) == 
    /\  op.id \in RID
    /\  op.id \notin srvReplied[s].r
    /\  IF s = Current_Tail
        THEN 
            /\ srvReplied' = [srvReplied EXCEPT ![s] = [@ EXCEPT !.r = @ \union {op.id}]]
            /\ resps' = Append(resps, [id |-> op.id, v |-> srvVals[s]])
            /\ UNCHANGED <<srvVals, srvReqs, reqs, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>
        ELSE
            /\ srvReqs' =  
                [
                    i \in 1..False_Tail
                    |->
                    IF 
                        i = Current_Tail
                    THEN
                        Append(srvReqs[i], op) \* Sending read to Tail, if a non-Tail has reads in its srvReqs(from earlier time, when it was a TAIL itself)
                    ELSE
                        IF 
                            i = s
                        THEN
                            Tail(srvReqs[i]) \* Removing read from current srvReqs, as this server is not a Tail and cannot service reads/queries
                        ELSE 
                            srvReqs[i]

                ] 
            /\ UNCHANGED <<srvVals, reqs, resps, srvReplied, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>

(* After Tail finishes a write, it adds that write to its local srvAck. This ack is back propagated back through the chain *)
BackPropagateAck(s) ==
    /\ s > HEAD
    /\ Cardinality(srvAck[s] \ srvAck[s-1]) > 0
    /\ srvAck' = [srvAck EXCEPT ![s-1] = srvAck[s]]

(* For each server, head of srvSent is removed if an ack for that write is received and present in its srvAck*)
UpdateSentFromAck(s) ==
    /\ Len(srvSent[s]) > 0
    /\ Head(srvSent[s]) \in srvAck[s]
    /\ srvSent' = [srvSent EXCEPT ![s] = Tail(@)]

(* Steps related to read and write ops*)
ModifiedCRNext == 
    \/ \E rid \in RID: 
        /\ ModifiedCRIssueRead(rid)
        /\ STEP_TAKEN' = "ModifiedCRIssueRead"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail>>
    \/ \E wid \in WID: 
        /\ ModifiedCRIssueWrite(wid) 
        /\ STEP_TAKEN' = "IssueWrite"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<srvAck, srvHist, srvSent, Current_Tail, False_Tail>>
    \/ \E s \in (1..Current_Tail):
        /\ Len(srvReqs[s]) > 0
        /\ LET o == Head(srvReqs[s]) IN

(* Commenting for Machine checkability under 1 minute
            \/ 
                /\ DropRead(o, s)
                /\ STEP_TAKEN' = "DropRead"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>
            \/ 
                /\ DropWrite(o, s)
                /\ STEP_TAKEN' = "DropWrite"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>
*)
            \/ 
                /\ ModifiedCRServerReads(o, s)
                /\ STEP_TAKEN' = "ModifiedCRServerReads"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<srvAck, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail>>
            \/ 
                /\ ModifiedCRServerWrites(o, s)    
                /\ STEP_TAKEN' = "ModifiedCRServerWrites"
                /\ REMOVED_INDICES' = {}
                /\ UNCHANGED <<Current_Tail, False_Tail>>

    \/ 
        /\ \E s \in (1..Current_Tail): BackPropagateAck(s)
        /\ STEP_TAKEN' = "BackPropagateAck"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvHist, srvSent, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>
        
    \/ 
        /\ \E s \in (1..Current_Tail): UpdateSentFromAck(s)
        /\ STEP_TAKEN' = "UpdateSentFromAck"
        /\ REMOVED_INDICES' = {}
        /\ UNCHANGED <<reqs, resps, srvReplied, srvReqs, srvVals, srvAck, srvHist, srvMaxWriteSeqNumReceived, Current_Tail, False_Tail, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>


(* Next steps of the spec where it can cause failures of maximum N-1 servers in a N length chain or continue normally with read/write operations. With each step, a STEPS counter is always increased*)
AddFailStopCRNext == 
    /\  STEPS' = STEPS + 1
    /\
        \/  FailureAndRecoveryStep
        \/  ModifiedCRNext
        \/  \E num_servers \in {1,2}:
                AddNewServertoChain(num_servers)
        \/  SyncHistoryWithNewServer
        \/  ShiftCurrentTailToNewServer

vars == <<srvReplied, srvVals, srvReqs, resps, reqs, STEPS, Current_Tail, REMOVED_INDICES, srvHist, srvSent, srvAck, srvHist, STEP_TAKEN, srvMaxWriteSeqNumReceived, False_Tail, NUM_SERVERS_ADDED, NUM_SERVERS_DELETED>>   

AddFailStopFairness == WF_vars(AddFailStopCRNext)

AddFailStopLiveness == 
    /\ \A req \in reqs:
        []<>(req \in SequencetoSet(resps)) 

EventuallySyncwithNewServers ==
    []<>(Current_Tail = False_Tail)

(*Final Spec of Fail Stop CR*)
AddFailStopCRSpec == 
    /\ AddFailStopCRInit 
    /\ [][AddFailStopCRNext]_vars 
    /\ AddFailStopFairness 
    /\ AddFailStopLiveness
    /\ EventuallySyncwithNewServers

=============================================================================
