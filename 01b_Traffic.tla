You can write your comments here

in free form

---- MODULE 01b_Traffic ----
EXTENDS TLC

VARIABLE 
    light,
    prev

Init ==
    /\ light = "red"
    /\ prev = "red"
    
TurnGreen ==
    /\ light = "yellow"
    /\ prev = "red"
    /\ light' = "green"
    /\ UNCHANGED prev

TurnYellow ==
    /\ light \in {"green", "red"}
    /\ prev' = light
    /\ light' = "yellow"

TurnRed ==
    /\ light = "yellow"
    /\ prev = "green"
    /\ light' = "red"
    /\ UNCHANGED prev

Next ==
    \/ TurnGreen
    \/ TurnYellow
    \/ TurnRed


\* You can also write single-line commennts like this

(* or 

multi-line comments like

this *)

====

and you can also write them here
TLA tools will ignore this completely