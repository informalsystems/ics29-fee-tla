----- MODULE test -----

EXTENDS Naturals

VARIABLES
    x,
    y

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    \/  /\ x < 10
        /\ x' = x + 1
        /\ UNCHANGED <<y>>
    \/  /\ y < 10
        /\ y' = y + 1
        /\ UNCHANGED <<x>>

WantedState ==
    /\ x = 8
    /\ y = 6

Invariant ==
    ~WantedState

======
