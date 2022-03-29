---- MODULE 03a_Canisters ----
EXTENDS TLC, Sequences, Integers, FiniteSets

INITIAL_USER_BALANCE == 2

NEURON_ACCOUNTS == { "na1", "na2" }
USER_ACCOUNTS == { "ua1" }

CLAIM_TIDS == {"c1", "c2"}
DISBURSE_TIDS == {"d1"}

ACCOUNTS == NEURON_ACCOUNTS \union USER_ACCOUNTS

CLAIM_START == "claim_start"
CLAIM_WAIT == "claim_wait"
CLAIM_END == "claim_end"

DISBURSE_START == "disburse_start"
DISBURSE_WAIT == "disburse_wait"
DISBURSE_END == "disburse_end"

QUERY_T == "query"
TRANSFER_T == "transfer"


VARIABLE 
    balance,
    cached_stake,
    requests,
    responses,
    args,
    pc

vars == << balance, cached_stake, requests, responses, args, pc >>

Init ==
    \* (f @@ g)[x] = IF x \in DOMAIN(f) THEN f[x] ELSE g[x]
    /\ balance = [ x \in USER_ACCOUNTS |-> INITIAL_USER_BALANCE ] 
                        @@ [ x \in NEURON_ACCOUNTS |-> 0]
    /\ cached_stake = [ x \in NEURON_ACCOUNTS |-> 0 ]
    \* Empty sequence
    /\ requests = <<>>
    /\ responses = {}
    /\ pc = [ cp \in CLAIM_TIDS |-> CLAIM_START ] 
            @@ [ dp \in DISBURSE_TIDS |-> DISBURSE_START ]
    /\ args = [ p \in CLAIM_TIDS \union DISBURSE_TIDS |-> {} ]

Query(tid, account) == [ type |-> QUERY_T, tid |-> tid, account |-> account ]
Transfer(tid, from, to, amount) == [ type |-> TRANSFER_T, tid |-> tid, from |-> from, to |-> to, amount |-> amount]
Is_Query(msg) == msg.type = QUERY_T
Is_Transfer(msg) == msg.type = TRANSFER_T
Response(type, tid, value) == [ type |-> type, tid |-> tid, value |-> value ]

Claim_Neuron_Start(tid, acc_id) ==
    /\ pc[tid] = CLAIM_START
    /\ requests' = Append(requests, Query(tid, acc_id))
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_WAIT ]
    /\ args' = [ args EXCEPT ![tid] = acc_id ]
    /\ UNCHANGED << balance, responses, cached_stake >>

Ledger_Query ==
    /\ requests # <<>>
    /\ LET
        req == Head(requests)
       IN 
        /\ Is_Query(req)
        /\ responses' = responses \union 
            {Response(QUERY_T, req.tid, balance[req.account])}
        /\ requests' = Tail(requests)
        /\ UNCHANGED << balance, cached_stake, pc, args >>

Claim_Neuron_Wait(tid) ==
  \E response \in responses:
    /\ pc[tid] = CLAIM_WAIT
    /\ Is_Query(response)
    /\ response.tid = tid
    /\ cached_stake' = [ cached_stake EXCEPT ![args[tid]] = response.value ]
    /\ responses' = responses \ {response}
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_END ]
    /\ UNCHANGED << balance, requests, args >>

Disburse_Neuron_Start(tid, neuron, to) ==
    /\ pc[tid] = DISBURSE_START
    /\ requests' = Append(
        requests, 
        Transfer(tid, neuron, to, cached_stake[neuron])
       )
    /\ pc' = [ pc EXCEPT ![tid] = DISBURSE_WAIT ]
    /\ args' = [ args EXCEPT ![tid] = neuron ]
    /\ UNCHANGED << balance, responses, cached_stake >>

Ledger_Neuron_Transfer ==
    /\ requests # <<>>
    /\ LET
        req == Head(requests)
       IN 
        /\ Is_Transfer(req)
        /\ balance' = [ balance EXCEPT
            ![req.from] = @ - req.amount,
            ![req.to] = @ + req.amount]
        /\ responses' = responses \union 
            {Response(TRANSFER_T, req.tid, {})}
        /\ requests' = Tail(requests)
        /\ UNCHANGED << cached_stake, pc, args >>

Disburse_Neuron_Wait(tid) ==
  \E response \in responses:
    /\ pc[tid] = DISBURSE_WAIT
    /\ Is_Transfer(response)
    /\ response.tid = tid
    /\ cached_stake' = [ cached_stake EXCEPT ![args[tid]] = 0 ]
    /\ responses' = responses \ {response}
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_END ]
    /\ UNCHANGED << balance, requests, args >>

Ledger_User_Transfer(user_acc, neuron_acc) ==
  \E amt \in 1..balance[user_acc]:
    /\ balance' = [ balance EXCEPT
            ![user_acc] = @ - amt,
            ![neuron_acc] = @ + amt
        ]
    /\ UNCHANGED << cached_stake, requests, responses, pc, args >>

Next == \E ctid \in CLAIM_TIDS, 
  dtid \in DISBURSE_TIDS, 
  neuron \in NEURON_ACCOUNTS, 
  u \in USER_ACCOUNTS,
  acc \in ACCOUNTS:
    \/ Claim_Neuron_Start(ctid, neuron)
    \/ Claim_Neuron_Wait(ctid)
    \/ Disburse_Neuron_Start(dtid, neuron, acc)
    \/ Disburse_Neuron_Wait(dtid)
    \/ Ledger_Query
    \/ Ledger_Neuron_Transfer
    \/ Ledger_User_Transfer(u, neuron)
    \/ UNCHANGED vars

\******************************
\* Properties

RECURSIVE Sum_F(_, _)
Sum_F(f, S) ==
    IF S = {} THEN 0
    ELSE 
        LET x == CHOOSE y \in S: TRUE
        IN f[x] + Sum_F(f, S \ {x})

Cached_Stake_Is_Bounded_By_Supply ==
    Sum_F(cached_stake, DOMAIN cached_stake) <= INITIAL_USER_BALANCE * Cardinality(USER_ACCOUNTS)

Supply_Is_Constant ==
    /\ Sum_F(balance, DOMAIN balance) = INITIAL_USER_BALANCE * Cardinality(USER_ACCOUNTS)

Balances_Non_Negative == \A acc \in ACCOUNTS: balance[acc] >= 0

====