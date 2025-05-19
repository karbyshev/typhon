------------------------- MODULE LibTheorems_proofs -------------------------
EXTENDS FiniteSetTheorems, Lib, TLAPS

LEMMA EmptySetMax == IsMax(0, {})
PROOF BY DEF IsMax

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

LEMMA StrictSubsetCardinality ==
    ASSUME NEW X,
           NEW Y,
           X \in SUBSET Y,
           X # Y,
           IsFiniteSet(Y)
    PROVE  Cardinality(X) < Cardinality(Y)
PROOF BY FS_Union, FS_Subset, FS_Singleton

=============================================================================
\* Modification History
\* Last modified Tue May 20 00:34:20 CEST 2025 by karbyshev
\* Created Tue May 20 00:05:14 CEST 2025 by karbyshev
