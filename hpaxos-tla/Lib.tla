-------------------------------- MODULE Lib --------------------------------
EXTENDS Naturals

\* TODO remove if unused
IsMax(x, S) == \A y \in S : y =< x

Max(S) == CHOOSE x \in S : IsMax(x, S)
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

=============================================================================
\* Modification History
\* Last modified Tue May 20 14:45:27 CEST 2025 by karbyshev
\* Created Sat May 10 14:55:17 CEST 2025 by karbyshev
