-------------------------- MODULE HPaxos_2_Safety --------------------------
EXTENDS HPaxos_2

-----------------------------------------------------------------------------

Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

-----------------------------------------------------------------------------

THEOREM SafetyResult == Spec => []Safety

=============================================================================
\* Modification History
\* Last modified Wed May 21 15:56:15 CEST 2025 by karbyshev
\* Created Wed May 21 14:29:30 CEST 2025 by karbyshev
