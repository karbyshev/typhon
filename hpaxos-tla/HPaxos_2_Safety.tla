-------------------------- MODULE HPaxos_2_Safety --------------------------
EXTENDS HPaxos_2, HPaxos_2_Specs

-----------------------------------------------------------------------------


-----------------------------------------------------------------------------

THEOREM SafetyResult == Spec => []Safety

=============================================================================
\* Modification History
\* Last modified Wed May 21 15:56:15 CEST 2025 by karbyshev
\* Created Wed May 21 14:29:30 CEST 2025 by karbyshev
