---- MODULE 04c_Connections ----
EXTENDS TLC, Integers, Sequences, FiniteSets

\* A few generic auxiliary definitions on functions and sequences
Remove_Argument(f, x) == [ y \in DOMAIN(f) \ {x} |-> f[y] ]

Last(s) == s[Len(s)]

Range(f) ==
  { f[x] : x \in DOMAIN f }

\* The model assumes PARTICIPANTS to be a sequence that models the 
\* fixed sequence of participants in the current group, as recorded in the canister)
PARTICIPANTS == << "p1", "p2", "p3" >>

\* The set of all participants (the "unordered" version of the list)
Participant_Set == Range(PARTICIPANTS)

\* TLC will squeak if an ASSUME statement isn't fulfilled
\* Sanity check that the participant list doesn't contain duplicates
ASSUME
    Len(PARTICIPANTS) = Cardinality(Participant_Set)

\* We make non-active canister states records, so that TLC doesn't complain when 
\* comparing for equality against active states
UNINITIALIZED == [ state |-> "UNINITIALIZED" ]
INITIALIZED == [ state |-> "INITIALIZED" ]
FINISHED == [ state |-> "FINISHED" ]

NEGOTIATING == "NEGOTIATING"
ESTABLISHED == "ESTABLISHED"

\* Sanity check that the different sentinel states are distinct
ASSUME
    Cardinality({UNINITIALIZED, INITIALIZED, FINISHED}) = 3

VARIABLES 
    \* Keep the entire history of the evolution of the canister (i.e., all versions), 
    \* as the participants could get an arbitrarily stale state when performing a query
    \* or after a refresh
    canister_history,
    \* Keeps the state of each participant
    participant

vars == << canister_history, participant >>

Empty_Map == [x \in {} |-> {}]

Init_Participant == [
    video |-> Empty_Map,
    canister_read |-> 1
]

Init_Active == [
    round |-> 0
]

\* We start by assuming that the canister is already in an active state,
\* to simplify the model. We don't simplify further to have a static
\* progression of the canister, even though this would not change the
\* participants behavior, as they could always poll an old version of the canister.
\* However, like this we can easily limit the progress of the canister
\* in order to "stretch out" a proving round to infinity, such that we can
\* analyze the stability properties.
Init_Canister == << UNINITIALIZED, INITIALIZED, Init_Active >>

\* The current state of the canister is the last one in the history
\* We call it just "Canister"
Canister == Last(canister_history)

Init ==
    /\ participant = [ p \in Participant_Set |-> Init_Participant ]
    /\ canister_history = Init_Canister

\* A participant may restart (e.g., by refreshing their browser) at any point in time
\* In that case it reads an arbitrary version of the canister and drops all connections.
Refresh_Connection(p) ==
    /\ \E i \in 1..Len(canister_history):
        /\ participant' = 
            p :> [  
                canister_read |-> i,
                video |-> Empty_Map
            ] @@ participant
    /\ UNCHANGED << canister_history >>

\* A participant drops all connections when it sees a "finished" state.
Finish(p) ==
    /\ canister_history[participant[p].canister_read] = FINISHED
    /\ participant' = [ participant EXCEPT
            ![p] = [ participant[p] EXCEPT !.video = Empty_Map ] 
       ]
    /\ UNCHANGED << canister_history >>

Last_Round == Len(PARTICIPANTS) - 1

\* The main canister action is to update the round.
Update_Round ==
    /\ Canister # FINISHED
    /\ Canister.round # Last_Round
    /\ canister_history' = Append(canister_history, [ Canister EXCEPT
            !.round = @ + 1
        ])
    /\ UNCHANGED << participant >>

\* A canister can also finish the party once it progresses past the last round.
Finish_Party ==
    /\ Canister # FINISHED
    /\ Canister.round = Last_Round
    /\ canister_history' = Append(canister_history, FINISHED)
    /\ UNCHANGED << participant >>

\* We define the prover based on the order in the participant list.
\* We adjust the offset by 1 as TLA sequences are 1-based, and the rounds start from 0,
Prover(round) == PARTICIPANTS[round + 1]

\* Parties can negotiate video.
Start_Negotiating_Video(p1, p2) == 
  LET 
    p1_state == participant[p1]
    p2_state == participant[p2]
  IN
    /\ p2 \notin DOMAIN p1_state.video
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    \* p1 thinks it is the prover
    /\ Prover(canister_history[p1_state.canister_read].round) = p1
    /\ p2 # p1
    \* TODO: We have another global guard here, as we inspect p2's state, so this is not
    \* directly implementable.
    \* We allow p2 to start negotiating even if it doesn't think that p1 is the prover. But
    \* we still require it to be initialized. This may or may not be a sound abstraction.
    /\ canister_history[p2_state.canister_read] \notin {UNINITIALIZED, FINISHED}
    /\ p1 \notin DOMAIN p2_state.video
    /\ participant' = [ participant EXCEPT 
            \* TODO: this is not a local event, as it reads/write the state of multiple participants.
            ![p1] = [ @ EXCEPT !.video = p2 :> [ state |-> NEGOTIATING, initiator |-> TRUE ] @@ @ ],
            ![p2] = [ @ EXCEPT !.video = p1 :> [ state |-> NEGOTIATING, initiator |-> FALSE ] @@ @ ]
        ]
    /\ UNCHANGED << canister_history >>

\* We allow a participant to reject a video negotiation if it doesn't think that the other side is
\* the prover.
Reject_Video(p1, p2) ==
    LET
      p1_state == participant[p1]
    IN
      /\ p2 \in DOMAIN p1_state.video
      /\ p1_state.video[p2].state = NEGOTIATING
      /\ ~p1_state.video[p2].initiator 
      /\ 
        \/ canister_history[p1_state.canister_read] \in {UNINITIALIZED, INITIALIZED, FINISHED}
        \/
           /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
           /\ Prover(canister_history[p1_state.canister_read].round) # p2
      /\ participant' = [ participant EXCEPT 
              ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
          ]
      /\ UNCHANGED << canister_history >>

Establish_Video(p1, p2) ==
  LET 
    p1_state == participant[p1]
  IN
    /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    /\ p2 \in DOMAIN p1_state.video
    /\ p1_state.video[p2].state = NEGOTIATING
    /\ 
        \/ p1_state.video[p2].initiator /\ Prover(canister_history[p1_state.canister_read].round) = p1
        \/ ~p1_state.video[p2].initiator /\ Prover(canister_history[p1_state.canister_read].round) = p2
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.video = [ @ EXCEPT ![p2] = [ @ EXCEPT !.state = ESTABLISHED ] @@ @ ] ]
        ]
    /\ UNCHANGED << canister_history >>

Detect_Video_Loss(p1, p2) ==
    LET
     p1_state == participant[p1]
     p2_state == participant[p2]
    IN
      /\ canister_history[p1_state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
      /\ p2 \in DOMAIN p1_state.video
      /\ p1 \notin DOMAIN p2_state.video
      /\ participant' = [ participant EXCEPT
            ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
         ]
      /\ UNCHANGED << canister_history >>

Lose_Video(p1, p2) ==
  LET
    p1_state == participant[p1]
  IN
    /\ p2 \in DOMAIN p1_state.video
    /\ participant' = [ participant EXCEPT 
            ![p1] = [ @ EXCEPT !.video = Remove_Argument(@, p2) ]
        ]
    /\ UNCHANGED << canister_history >>

Is_Prover_In(p, state) ==
    /\ canister_history[state.canister_read] \notin {UNINITIALIZED, INITIALIZED, FINISHED}
    /\ Prover(canister_history[state.canister_read].round) = p

\* We assume that, when a participant polls a canister, it doesn't go back in history.
\* I.e., even if the query returns an old state, the code should detect this and ignore
\* this change of state.
Poll_Canister(p) ==
    /\ \E i \in (participant[p].canister_read + 1) .. Len(canister_history):
        /\ participant' = [ participant EXCEPT 
                ![p] = 
                  [ @ EXCEPT 
                    !.canister_read = i ,
                    !.video = Empty_Map ]
            ]
    /\ UNCHANGED << canister_history >>

Next == \E p1, p2 \in Participant_Set:
    \/ Refresh_Connection(p1)
    \/ Finish(p1)
    \/ Start_Negotiating_Video(p1, p2)
    \/ Establish_Video(p1, p2)
    \/ Reject_Video(p1, p2)
    \/ Lose_Video(p1, p2)
    \/ Detect_Video_Loss(p1, p2)
    \/ Poll_Canister(p1)
    \* Actions changing the canister state
    \/ Update_Round
    \/ Finish_Party
    
\*****************************************************************
\* Properties

Participant_Doesnt_Connect_To_Itself == \A p \in Participant_Set: 
    LET 
        p_state == participant[p]
    IN
        /\ p \notin DOMAIN p_state.video

Initiate_All_Or_None == \A p \in Participant_Set:
    \A p2, p3 \in DOMAIN participant[p].video:
        participant[p].video[p2].state = ESTABLISHED /\ participant[p].video[p3].state = ESTABLISHED =>
            participant[p].video[p2].initiator = participant[p].video[p3].initiator

One_Inbound_Connection == \A p \in Participant_Set:
    \A p2, p3 \in DOMAIN participant[p].video:
        /\ participant[p].video[p2].initiator = FALSE 
        /\ participant[p].video[p2].state = ESTABLISHED 
        /\ participant[p].video[p3].state = ESTABLISHED 
      => p3 = p2

Dont_Progress_Past(p) == 
  /\ Canister # FINISHED
  /\ \A i \in 1..Len(PARTICIPANTS): PARTICIPANTS[i] = p 
        => Canister.round <= i - 1

Video_Fairness_Condition(p) == \A p2 \in Participant_Set \ {p}:
    /\ WF_vars(Prover(Canister.round) # p /\ Update_Round)
    /\ WF_vars(Start_Negotiating_Video(p, p2))
    /\ WF_vars(Establish_Video(p, p2))
    /\ WF_vars(Establish_Video(p2, p))
    /\ WF_vars(Detect_Video_Loss(p, p2))
    /\ WF_vars(Detect_Video_Loss(p2, p))
    /\ WF_vars(Poll_Canister(p))
    /\ WF_vars(Poll_Canister(p2))

Stable_Video_Connections_From(p) == \A p2 \in Participant_Set \ {p}:
    \/ 
        /\ <>[](
            /\ p2 \in DOMAIN (participant[p].video)
            /\ participant[p].video[p2] = [state |-> ESTABLISHED, initiator |-> TRUE]
          )
        /\ <>[] (
            /\ p \in DOMAIN (participant[p2].video)
            /\ participant[p2].video[p] = [state |-> ESTABLISHED, initiator |-> FALSE]
          )
    \* If we infinitely often spontaneously lose video, and if this transition couldn't be interpreted
    \* as just detecting video loss, or polling the canister (as this also closes connections),
    \* then we don't ask for other guarantees.
    \/ []<><<Lose_Video(p, p2) /\ ~Detect_Video_Loss(p, p2) /\ ~Poll_Canister(p)>>_vars
    \/ []<><<Lose_Video(p2, p) /\ ~Detect_Video_Loss(p2, p) /\ ~Poll_Canister(p2)>>_vars
    \/ []<><<Refresh_Connection(p)>>_vars
    \/ []<><<Refresh_Connection(p2)>>_vars

\* Check that p's connections remain stable forever
P_Property(p) == Stable_Video_Connections_From(p)

\* We can check the stability property for all three participants.
\* So any of these can be used as the spec/property in the TLC configuration
\* file.
\* We can eliminate the duplication as TLC gets confused about what's Init
\* or Next if we try to parametrize these definition
P1_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[1])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[1])
P1_Video_Property == P_Property(PARTICIPANTS[1])

P2_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[2])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[2])
P2_Video_Property == P_Property(PARTICIPANTS[2])

P3_Video_Spec == 
    /\ Init
    /\ [][Next /\ Dont_Progress_Past(PARTICIPANTS[3])]_vars
    /\ Video_Fairness_Condition(PARTICIPANTS[3])
P3_Video_Property == P_Property(PARTICIPANTS[3])

\*****************************************************************
\* Sanity-check properties: MEANT TO BE VIOLATED
\* The purpose is to discover bugs in the model.
\* We'll say things like "we can't finish the party", and see whether
\* we can violate them

Canister_Cant_Finish_Inv == Canister # FINISHED

Parties_Cant_Finish_Inv == \A p \in Participant_Set: canister_history[participant[p].canister_read] # FINISHED

Parties_Cant_Connect_Inv == \A p1, p2 \in Participant_Set: 
    \/ p2 \notin DOMAIN participant[p1].video
    \/ participant[p1].video[p2].state # ESTABLISHED

====