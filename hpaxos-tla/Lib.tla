-------------------------------- MODULE Lib --------------------------------
EXTENDS Naturals

LOCAL INSTANCE Functions
LOCAL INSTANCE Sequences

\* TODO remove if unused
IsMax(x, S) == \A y \in S : y =< x

Max(S) == CHOOSE x \in S : IsMax(x, S)
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

SmallestIndex(seq, P(_), k) ==
    P(seq[k]) /\ \A i \in 1..(k-1) : ~P(seq[i])

FINSUBSET(R) == { Range(seq) : seq \in Seq(R) }
\*FINSUBSET(S, R) == { Range(seq) : seq \in [R -> S] }
\*FINSUBSET(S, K) == { Range(seq) : seq \in [1..K -> S] }
\*FINSUBSET(S, R) == UNION { {Range(seq) : seq \in [1..K -> S]} : K \in R }

=============================================================================
\* Modification History
\* Last modified Wed May 21 22:40:11 CEST 2025 by karbyshev
\* Created Sat May 10 14:55:17 CEST 2025 by karbyshev
