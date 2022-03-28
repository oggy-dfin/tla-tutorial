---- MODULE 02_Peterson ----
EXTENDS TLC, Integers

Range(f) == { f[x] : x \in DOMAIN f }
TREAD == << 0, 1 >>
TREAD_SET == Range(TREAD)

L_START == "START"
L_GATE == "GATE"
L_WAIT == "WAIT"
L_CRITICAL == "CRITICAL"
L_END == "END"

Other(t) == 1 - t

VARIABLE 
    flag,
    turn,
    pc

Init ==
    /\ flag = [ t \in TREAD_SET |-> FALSE]
    /\ turn = TREAD[1]
    /\ pc = [ t \in TREAD_SET |-> L_START ]

Start(t) ==
    /\ pc[t] = L_START
    /\ flag' = [ flag EXCEPT ![t] = TRUE ]
    /\ pc' = [ pc EXCEPT ![t] = L_GATE ]
    /\ UNCHANGED turn

Gate(t) ==
    /\ pc[t] = L_GATE
    /\ turn' = Other(t)
    /\ pc' = [pc EXCEPT  ![t] = L_WAIT ]
    /\ UNCHANGED flag

Wait(t) ==
    /\ pc[t] = L_WAIT
    /\ 
        \/ flag[Other(t)] = FALSE
        \/ turn # Other(t)
    /\ pc' = [ pc EXCEPT ![t] = L_CRITICAL ]
    /\ UNCHANGED << flag, turn >>

Exit(t) ==
    /\ pc[t] = L_CRITICAL
    /\ flag' = [ flag EXCEPT ![t] = FALSE ]
    /\ pc' = [ pc EXCEPT ![t] = L_END ]
    /\ UNCHANGED turn

Idle(t) ==
    /\ pc[t] = L_END
    /\ UNCHANGED << pc, flag, turn >>

Next == \E t \in TREAD_SET:
    \/ Start(t)
    \/ Gate(t)
    \/ Wait(t)
    \/ Exit(t)
    \/ Idle(t)

Not_Both_In_Critical == \A t1, t2 \in TREAD_SET:
    pc[t1] = L_CRITICAL /\ pc[t2] = L_CRITICAL =>
        t1 = t2



====