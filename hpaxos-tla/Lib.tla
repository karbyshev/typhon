-------------------------------- MODULE Lib --------------------------------
EXTENDS Naturals

\* TODO remove if unused
IsMax(x, S) == \A y \in S : x >= y

Max(S) == CHOOSE x \in S : IsMax(x, S)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

=============================================================================
\* Modification History
\* Last modified Mon May 19 19:47:30 CEST 2025 by karbyshev
\* Created Sat May 10 14:55:17 CEST 2025 by karbyshev
