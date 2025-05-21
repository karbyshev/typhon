---------------------------- MODULE LibTheorems ----------------------------
EXTENDS Lib

LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

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

LEMMA SmallestIndexExists ==
    ASSUME NEW S, NEW P(_),
           NEW n \in Nat, NEW seq \in [1..n -> S],
           NEW n0 \in 1..n,
           P(seq[n0])
    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)

\* TODO rename
LEMMA INDUCTION_SCHEME ==
    ASSUME NEW P(_),
           P(0),
           \A k \in Nat : k > 0 /\ P(k - 1) => P(k)
    PROVE  \A n \in Nat : P(n)

=============================================================================
\* Modification History
\* Last modified Wed May 21 23:35:28 CEST 2025 by karbyshev
\* Created Mon May 19 20:15:40 CEST 2025 by karbyshev
