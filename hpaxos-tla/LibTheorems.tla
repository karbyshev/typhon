---------------------------- MODULE LibTheorems ----------------------------
EXTENDS Lib

LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

LEMMA InitialSegmentIsFinite ==
    ASSUME NEW n \in Nat PROVE IsFiniteSet(0..n)

LEMMA EmptySetMax == IsMax(0, {})

LEMMA MaxProperties ==
    ASSUME NEW S,
           \E max \in S : IsMax(max, S)
    PROVE  /\ Max(S) \in S
           /\ \A s \in S : s =< Max(S)

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

LEMMA SmallestIndexExistsSpecialization ==
    ASSUME NEW S, NEW P(_),
           NEW n \in Nat,
           0 < n,
           NEW seq \in [1..n -> S],
           P(seq[n])
    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)

LEMMA NatInductionShifted ==
    ASSUME NEW P(_),
           P(0),
           \A k \in Nat : k > 0 /\ P(k - 1) => P(k)
    PROVE  \A n \in Nat : P(n)

LEMMA FinSubset_sub ==
    ASSUME NEW S,
           NEW F \in FINSUBSET(S)
    PROVE  F \subseteq S

LEMMA FinSubset_empty ==
    ASSUME NEW S PROVE {} \in FINSUBSET(S)

LEMMA FinSubset_subset ==
    ASSUME NEW S, NEW Q \in SUBSET S
    PROVE  FINSUBSET(Q) \in SUBSET FINSUBSET(S)

=============================================================================
\* Modification History
\* Last modified Sat Aug 02 16:13:29 CEST 2025 by karbyshev
\* Created Mon May 19 20:15:40 CEST 2025 by karbyshev
