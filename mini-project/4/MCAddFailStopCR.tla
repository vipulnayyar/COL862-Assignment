------------------------------ MODULE MCAddFailStopCR ------------------------------------
EXTENDS AddFailStopCR, FiniteSets, TLC

Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2

LimitedServers == Len(srvVals) <= 4

LimitedServerAddition == NUM_SERVERS_ADDED <= 2
LimitedServerDeletion == NUM_SERVERS_DELETED <= 2

\*DebugConstraints == 
\*    /\ TRUE
\*    /\ Len(srvVals) = 4

(*
RemoveReadsfromSequenceToSet(seq_data) ==
     {
        w.id : w \in
            {   op \in {seq_data[i] : i \in DOMAIN seq_data}
                :
                op \in WrReq
                            
            }
    }

RemoveWritesfromSequenceToSet(seq_data) ==
     {
        w.id : w \in
            {   op \in {seq_data[i] : i \in DOMAIN seq_data}
                :
                op \in RdReq
                            
            }
    }

RemoveReadReqfromSequence(seq_to_remove_from) ==
    [i \in 1..Cardinality({j \in DOMAIN seq_to_remove_from : seq_to_remove_from[j] \notin  RdReq}) 
        |-> 
            LET 
                validindexes == 
                    [j \in 1..Len(seq_to_remove_from) 
                        |-> 
                            IF seq_to_remove_from[j] \in RdReq THEN 0 ELSE j]

                filteredindexes == 
                    SelectSeq(validindexes, LAMBDA x : x > 0)

            IN 
                seq_to_remove_from[filteredindexes[i]] 
    ]

RemoveWriteReqfromSequence(seq_to_remove_from) ==
    [i \in 1..Cardinality({j \in DOMAIN seq_to_remove_from : seq_to_remove_from[j] \notin  RdReq}) 
        |-> 
            LET 
                validindexes == 
                    [j \in 1..Len(seq_to_remove_from) 
                        |-> 
                            IF seq_to_remove_from[j] \in WrReq THEN 0 ELSE j]

                filteredindexes == 
                    SelectSeq(validindexes, LAMBDA x : x > 0)

            IN 
                seq_to_remove_from[filteredindexes[i]] 
    ]

*)





(* accepted_mapping == 
    [ 
        r |-> 
            srvReplied[Current_Tail].r
            \union 
            RemoveWritesfromSequenceToSet(srvReqs[Current_Tail])
        , 

        w |-> 
            srvReplied[Current_Tail].w 
            \union 
            RemoveReadsfromSequenceToSet(srvReqs[Current_Tail])
            
    ] *)

val_mapping == 
    IF 
        Len(srvHist[Current_Tail]) > 0
    THEN
        srvHist[Current_Tail][Len(srvHist[Current_Tail])].v
    ELSE 
        INITVAL


SS == INSTANCE SS WITH
    val <- val_mapping
    ,
    accepted <- srvReplied[Current_Tail]

SSSpec == SS!SSSpec

=============================================================================