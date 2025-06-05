---------------------------- MODULE HBallotValue ----------------------------
EXTENDS Naturals

Ballot == Nat

CONSTANT Value

CONSTANT BVal

ASSUME BValAssumption == BVal \in [Ballot -> Value]

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 01:37:14 CEST 2025 by karbyshev
\* Created Fri Jun 06 01:29:34 CEST 2025 by karbyshev
