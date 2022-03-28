---- MODULE 03_Canisters ----
EXTENDS TLC, Sequences, Integers

INITIAL_USER_BALANCE == 2

NEURON_ACCOUNTS == { "na1", "na2" }
USER_ACCOUNTS == { "ua1" }

QUERY_T == "query"
TRANSFER_T == "transfer"

ACCOUNTS == NEURON_ACCOUNTS \union USER_ACCOUNTS

CLAIM_TIDS == {"c1", "c2"}
CLAIM_START == "claim_start"
CLAIM_WAIT == "claim_wait"
CLAIM_END == "claim_end"

DISBURSE_TIDS == {"d1"}
DISBURSE_START == "disburse_start"
DISBURSE_WAIT == "disburse_wait"
DISBURSE_END == "disburse_end"

VARIABLE 
    ledger_balance,
    cached_stake,
    governance_to_ledger,
    ledger_to_governance,
    args,
    pc

vars == << ledger_balance, cached_stake, governance_to_ledger, ledger_to_governance, args, pc >>

Init ==
    /\ ledger_balance = [ x \in USER_ACCOUNTS |-> INITIAL_USER_BALANCE ] @@ [ x \in NEURON_ACCOUNTS |-> 0]
    /\ cached_stake = [ x \in NEURON_ACCOUNTS |-> 0 ]
    /\ governance_to_ledger = <<>>
    /\ ledger_to_governance = {}
    /\ pc = [ cp \in CLAIM_TIDS |-> CLAIM_START ] @@ [ dp \in DISBURSE_TIDS |-> DISBURSE_START ]
    /\ args = [ p \in CLAIM_TIDS \union DISBURSE_TIDS |-> {} ]

Query(tid, account) == [ type |-> QUERY_T, tid |-> tid, account |-> account ]
Transfer(tid, from, to, amount) == [ type |-> TRANSFER_T, tid |-> tid, from |-> from, to |-> to, amount |-> amount]
Is_Query(msg) == msg.type = QUERY_T
Is_Transfer(msg) == msg.type = TRANSFER_T
Response(type, tid, value) == [ type |-> type, tid |-> tid, value |-> value ]

Ledger_Query ==
    /\ governance_to_ledger # <<>>
    /\ LET
        req == Head(governance_to_ledger)
       IN 
        /\ Is_Query(req)
        /\ ledger_to_governance' = ledger_to_governance \union 
            {Response(QUERY_T, req.tid, ledger_balance[req.account])}
        /\ governance_to_ledger' = Tail(governance_to_ledger)
        /\ UNCHANGED << ledger_balance, cached_stake, pc, args >>

Ledger_Neuron_Transfer ==
    /\ governance_to_ledger # <<>>
    /\ LET
        req == Head(governance_to_ledger)
       IN 
        /\ Is_Transfer(req)
        /\ ledger_balance' = [ ledger_balance EXCEPT
            ![req.from] = @ - req.amount,
            ![req.to] = @ + req.amount]
        /\ ledger_to_governance' = ledger_to_governance \union 
            {Response(TRANSFER_T, req.tid, {})}
        /\ governance_to_ledger' = Tail(governance_to_ledger)
        /\ UNCHANGED << cached_stake, pc, args >>

Ledger_User_Transfer(user_acc, neuron_acc) ==
  \E amt \in 1..ledger_balance[user_acc]:
    /\ ledger_balance' = [ ledger_balance EXCEPT
            ![user_acc] = @ - amt,
            ![neuron_acc] = @ + amt
        ]
    /\ UNCHANGED << cached_stake, governance_to_ledger, ledger_to_governance, pc, args >>

Claim_Neuron_1(tid, neuron) ==
    /\ pc[tid] = CLAIM_START
    /\ governance_to_ledger' = Append(governance_to_ledger, Query(tid, neuron))
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_WAIT ]
    /\ args' = [ args EXCEPT ![tid] = neuron ]
    /\ UNCHANGED << ledger_balance, ledger_to_governance, cached_stake >>

Claim_Neuron_2(tid) ==
  \E response \in ledger_to_governance:
    /\ pc[tid] = CLAIM_WAIT
    /\ Is_Query(response)
    /\ response.tid = tid
    /\ cached_stake' = [ cached_stake EXCEPT ![args[tid]] = response.value ]
    /\ ledger_to_governance' = ledger_to_governance \ {response}
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_END ]
    /\ UNCHANGED << ledger_balance, governance_to_ledger, args >>

Disburse_Neuron_1(tid, neuron, to) ==
    /\ pc[tid] = DISBURSE_START
    /\ governance_to_ledger' = Append(
        governance_to_ledger, 
        Transfer(tid, neuron, to, cached_stake[neuron])
       )
    /\ pc' = [ pc EXCEPT ![tid] = DISBURSE_WAIT ]
    /\ args' = [ args EXCEPT ![tid] = neuron ]
    /\ UNCHANGED << ledger_balance, ledger_to_governance, cached_stake >>

Disburse_Neuron_2(tid) ==
  \E response \in ledger_to_governance:
    /\ pc[tid] = DISBURSE_WAIT
    /\ Is_Transfer(response)
    /\ response.tid = tid
    /\ cached_stake' = [ cached_stake EXCEPT ![args[tid]] = 0 ]
    /\ ledger_to_governance' = ledger_to_governance \ {response}
    /\ pc' = [ pc EXCEPT ![tid] = CLAIM_END ]
    /\ UNCHANGED << ledger_balance, governance_to_ledger, args >>

Next == \E ctid \in CLAIM_TIDS, 
  dtid \in DISBURSE_TIDS, 
  neuron \in NEURON_ACCOUNTS, 
  u \in USER_ACCOUNTS,
  acc \in ACCOUNTS:
    \/ Claim_Neuron_1(ctid, neuron)
    \/ Claim_Neuron_2(ctid)
    \/ Disburse_Neuron_1(dtid, neuron, acc)
    \/ Disburse_Neuron_2(dtid)
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

Supply_Is_Constant ==
    /\ Sum_F(ledger_balance, DOMAIN ledger_balance) = INITIAL_USER_BALANCE

Cached_Stake_Is_Bounded_By_Supply ==
    Sum_F(cached_stake, DOMAIN cached_stake) <= INITIAL_USER_BALANCE

====