---------------------------- MODULE LibTheorems ----------------------------
EXTENDS Lib, FiniteSets

LEMMA EmptySetMax == IsMax(0, {})

LEMMA NatFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Nat,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)

=============================================================================
\* Modification History
\* Last modified Mon May 19 20:40:18 CEST 2025 by karbyshev
\* Created Mon May 19 20:15:40 CEST 2025 by karbyshev
