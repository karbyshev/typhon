---------------------------- MODULE LibTheorems ----------------------------
EXTENDS Lib, FiniteSets

LEMMA InitialSegmentIsFinite ==
    ASSUME NEW n \in Nat PROVE IsFiniteSet(0..n)

LEMMA EmptySetMax == IsMax(0, {})

LEMMA MaxIsMax ==
    ASSUME NEW S,
           NEW s \in S,
           \E max \in S : IsMax(max, S)
    PROVE  s =< Max(S)

LEMMA MaxUnique ==
    ASSUME NEW S,
           \A x, y \in S : x =< y /\ y =< x => x = y,
           NEW A \in SUBSET S,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y

LEMMA NatFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Nat,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)

=============================================================================
\* Modification History
\* Last modified Tue May 20 17:50:15 CEST 2025 by karbyshev
\* Created Mon May 19 20:15:40 CEST 2025 by karbyshev
