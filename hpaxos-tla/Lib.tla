-------------------------------- MODULE Lib --------------------------------
EXTENDS Naturals

LOCAL INSTANCE Functions
LOCAL INSTANCE FiniteSets

\* TODO remove if unused
IsMax(x, S) == \A y \in S : y =< x

Max(S) == CHOOSE x \in S : IsMax(x, S)
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

SmallestIndex(seq, P(_), k) ==
    P(seq[k]) /\ \A i \in 1..(k-1) : ~P(seq[i])

FINSUBSET(R) == { M \in SUBSET R : IsFiniteSet(M) }

=============================================================================
\* Modification History
\* Last modified Tue Jul 08 15:06:37 CEST 2025 by karbyshev
\* Created Sat May 10 14:55:17 CEST 2025 by karbyshev
