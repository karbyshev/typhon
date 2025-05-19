---------------------------- MODULE LibTheorems ----------------------------
EXTENDS Lib, FiniteSets

LEMMA EmptySetMax == IsMax(0, {})

LEMMA NatFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Nat,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)

LEMMA StrictSubsetCardinality ==
    ASSUME NEW X,
           NEW Y,
           X \in SUBSET Y,
           X # Y,
           IsFiniteSet(Y)
    PROVE  Cardinality(X) < Cardinality(Y)

=============================================================================
\* Modification History
\* Last modified Tue May 20 00:28:17 CEST 2025 by karbyshev
\* Created Mon May 19 20:15:40 CEST 2025 by karbyshev
