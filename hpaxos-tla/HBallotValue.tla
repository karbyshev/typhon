---------------------------- MODULE HBallotValue ----------------------------
EXTENDS Naturals

Ballot == Nat

CONSTANT Value
ASSUME ValueNonEmpty == Value # {}

CONSTANT BVal

ASSUME BValAssumption == BVal \in [Ballot -> Value]

ASSUME BValValueAssumption ==
    \A B \in Ballot :
    \A val \in Value :
        \E bal \in Ballot :
            B =< bal /\ val = BVal[bal]

=============================================================================
\* Modification History
\* Last modified Thu Jun 12 20:29:29 CEST 2025 by karbyshev
\* Created Fri Jun 06 01:29:34 CEST 2025 by karbyshev
