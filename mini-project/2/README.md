
The same FailStopCR implementation from Q1 is used for refinment mapping with SS. Overall, the states and transitions of just the Tail in FailStopCR, can be mapped to SS states and its transitions.

Following mapping is used for SS variables

- reqs(SS) : mapped to reqs in FailStopCR.tla

- resps(SS) : mapped to resps in FailStopCR.tla

- val(SS) : mapped to srvVals[Current_Tail] in FailStop.tla, which is the value of server state maintained by the Tail in CR.

- accepted(SS) : mapped to srvReplied[Current_Tail] in Failstop.tla, which is the read and write history maintained by the Tail in CR.

In the original SS.tla implementation, there is no corresponding state for a failed Tail server, that has forgotten its read history(srvReplied.r in FailStopCR and accepted.r in SS), as it cannot be regenerated post failure on a new Tail(Regenerating read history from resps is theoretically possible, but not a practical design approach). For this, the following next step is added to SSNext in SS.tla

ForgetReadHistoryonTail ==
    /\ accepted' = [accepted EXCEPT !.r = {}] \* Does not impact consistency of data
    /\ UNCHANGED <<reqs, val, resps>>