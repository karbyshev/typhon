------------------------- MODULE LibTheorems_proofs -------------------------
EXTENDS SequenceTheorems, Lib, TLAPS

LOCAL INSTANCE FiniteSetTheorems

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

LEMMA MaxProperties ==
    ASSUME NEW S,
           \E max \in S : IsMax(max, S)
    PROVE  /\ Max(S) \in S
           /\ \A s \in S : s =< Max(S)
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
<1>0. P({})
      OBVIOUS
<1>1. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
      BY <1>1 DEF IsMax
<1> HIDE DEF P
<1>3. QED BY <1>0, <1>1, FS_Induction, Blast

LEMMA SmallestIndexExists ==
    ASSUME NEW S, NEW P(_),
           NEW n \in Nat, NEW seq \in [1..n -> S],
           NEW n0 \in 1..n,
           P(seq[n0])
    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)
PROOF
<1> DEFINE A(x) == x \in 0..n - 1 /\ P(seq[x + 1])
<1>1. SUFFICES \E k \in Nat :
                /\ A(k)
                /\ k = 0 \/ \A i \in 0 .. (k - 1) : ~A(i)
  <2> PICK k \in Nat :
            /\ A(k)
            /\ k = 0 \/ \A i \in 0 .. (k - 1) : ~A(i)
      BY <1>1
  <2> WITNESS k + 1 \in 1..n
  <2>1. P(seq[k + 1])
        OBVIOUS
  <2>2. ASSUME NEW i \in 1..k PROVE ~P(seq[i])
    <3> CASE k = 0 OBVIOUS
    <3> CASE k > 0
      <4> i - 1 \in 0..n - 1
          OBVIOUS
      <4> QED OBVIOUS
    <3> QED OBVIOUS
  <2> QED BY <2>1, <2>2 DEF SmallestIndex
<1> n0 - 1 \in Nat
    OBVIOUS
<1> A(n0 - 1)
    OBVIOUS
<1> HIDE DEF A
<1> QED BY <1>1, SmallestNatural, Blast

LEMMA SmallestIndexExistsSpecialization ==
    ASSUME NEW S, NEW P(_),
           NEW n \in Nat,
           0 < n,
           NEW seq \in [1..n -> S],
           P(seq[n])
    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)
PROOF
<1> n \in 1..n OBVIOUS
<1> QED BY SmallestIndexExists, Blast

LEMMA NatInductionShifted ==
    ASSUME NEW P(_),
           P(0),
           \A k \in Nat : k > 0 /\ P(k - 1) => P(k)
    PROVE  \A n \in Nat : P(n)
PROOF
<1> DEFINE Q(x) == x > 0 => P(x - 1)
<1> SUFFICES \A n \in Nat : Q(n)
    OBVIOUS
<1>0. Q(0)
      OBVIOUS
<1>1. ASSUME NEW m \in Nat, Q(m) PROVE Q(m + 1)
      BY <1>1
<1> HIDE DEF Q
<1> QED BY <1>0, <1>1, NatInduction, Isa

LEMMA FinSubset_sub ==
    ASSUME NEW S,
           NEW F \in FINSUBSET(S)
    PROVE  F \subseteq S
PROOF BY DEF FINSUBSET

LEMMA FinSubset_empty ==
    ASSUME NEW S PROVE {} \in FINSUBSET(S)
PROOF BY FS_EmptySet DEF FINSUBSET

LEMMA FinSubset_subset ==
    ASSUME NEW S, NEW Q \in SUBSET S
    PROVE  FINSUBSET(Q) \in SUBSET FINSUBSET(S)
PROOF BY FS_Subset DEF FINSUBSET

=============================================================================
\* Modification History
\* Last modified Sat Aug 02 16:12:57 CEST 2025 by karbyshev
\* Created Tue May 20 00:05:14 CEST 2025 by karbyshev
