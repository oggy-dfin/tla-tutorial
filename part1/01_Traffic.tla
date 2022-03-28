You can write your comments here

in free form

---- MODULE 01_Traffic ----
EXTENDS TLC

VARIABLE 
    light

Init ==
    /\ light = "red"
    
TurnGreen ==
    /\ light = "red"
    /\ light' = "green"

TurnYellow ==
    /\ light = "green"
    /\ light' = "yellow"

TurnRed ==
    /\ light = "yellow"
    /\ light' = "red"

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