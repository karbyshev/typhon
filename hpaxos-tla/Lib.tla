-------------------------------- MODULE Lib --------------------------------
EXTENDS FiniteSetTheorems, TLAPS

\* TODO remove if unused
IsMax(x, S) == \A y \in S : x >= y

Max(S) == CHOOSE x \in S : IsMax(x, S)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

-----------------------------------------------------------------------------
LEMMA EmptySetMax == IsMax(0, {})
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
<1>3. QED BY <1>0, <1>1, FS_Induction, IsaM("blast")

=============================================================================
\* Modification History
\* Last modified Sun May 11 13:22:22 CEST 2025 by karbyshev
\* Created Sat May 10 14:55:17 CEST 2025 by karbyshev
