


The same AddFailStopCR implementation from Q3 is used for refinment mapping with SS. Overall, the states and transitions of just the Tail in AddFailStopCR, can be mapped to SS states and its transitions.

Following mapping is used for SS variables

- reqs(SS) : mapped to reqs in AddFailStopCR.tla

- resps(SS) : mapped to resps in AddFailStopCR.tla

- accepted(SS) : mapped to srvReplied[Current_Tail] in AddFailstop.tla, which is the read and write history maintained by the Tail in CR.

- val(SS) : mapped to the following. Instead of `srvVals`, the last element of `srvHist` of `Current_Tail` is used if Tail has seen at least one write. Else, the initial value is used.  
```
val_mapping == 
    IF 
        Len(srvHist[Current_Tail]) > 0
    THEN
        srvHist[Current_Tail][Len(srvHist[Current_Tail])].v
    ELSE 
        INITVAL

```

In the original SS.tla implementation, there is no corresponding state for a failed Tail server, that has forgotten its read history(srvReplied.r in AddFailStopCR and accepted.r in SS), as it cannot be regenerated post failure on a new Tail(Regenerating read history from resps is theoretically possible, but not a practical design approach). For this, the following next step is added to SSNext in SS.tla

```
ForgetReadHistoryonTail ==
    /\ accepted' = [accepted EXCEPT !.r = {}] \* Does not impact consistency of data
    /\ UNCHANGED <<reqs, val, resps>>
```

The following SYMMETRY and CONSTRAINT are used to reduce the search state space:
```
Symmetries == Permutations(VALS) \cup Permutations(RID) \cup Permutations(WID)
LimitedMsgs == \A s \in (1..Current_Tail): Len(srvReqs[s]) <= 2
LimitedServers == Len(srvVals) <= 2
LimitedServerAddition == NUM_SERVERS_ADDED <= 2
LimitedServerDeletion == NUM_SERVERS_DELETED <= 2
```
