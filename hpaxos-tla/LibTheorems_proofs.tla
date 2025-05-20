------------------------- MODULE LibTheorems_proofs -------------------------
EXTENDS FiniteSetTheorems, SequenceTheorems, Lib, TLAPS

LEMMA InitialSegmentIsFinite ==
    ASSUME NEW n \in Nat PROVE IsFiniteSet(0..n)
PROOF
<1> DEFINE seq == [x \in 1..n + 1 |-> x - 1]
<1> seq \in Seq(0..n)
    BY SeqDef
<1> ASSUME NEW s \in 0..n PROVE \E i \in 1..Len(seq) : seq[i] = s
  <2> WITNESS s + 1 \in 1..Len(seq)
  <2> QED OBVIOUS
<1> QED BY DEF IsFiniteSet

LEMMA EmptySetMax == IsMax(0, {})
PROOF BY DEF IsMax

LEMMA MaxIsMax ==
    ASSUME NEW S,
           NEW s \in S,
           \E max \in S : IsMax(max, S)
    PROVE  s =< Max(S)
PROOF BY DEF Max, IsMax

LEMMA MaxUnique ==
    ASSUME NEW S,
           \A x, y \in S : x =< y /\ y =< x => x = y,
           NEW A \in SUBSET S,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y
PROOF BY DEF IsMax

\* TODO this can be further generalized to arbitrary linear orders,
\* and partial orders with IsMax defined by
\* IsMax(x, S) == \A y \in S : x =< y => x = y
LEMMA NatFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Nat,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)
PROOF
<1> DEFINE P(X) == X # {} /\ X \in SUBSET Nat => \E max \in X : IsMax(max, X)
<1> SUFFICES ASSUME NEW S, IsFiniteSet(S) PROVE P(S)
    OBVIOUS
<1>0. P({}) OBVIOUS
<1>1. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
      BY <1>1 DEF IsMax
<1> HIDE DEF P
<1>3. QED BY <1>0, <1>1, FS_Induction, Blast

=============================================================================
\* Modification History
\* Last modified Tue May 20 17:56:41 CEST 2025 by karbyshev
\* Created Tue May 20 00:05:14 CEST 2025 by karbyshev
