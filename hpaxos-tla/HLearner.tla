------------------------------ MODULE HLearner ------------------------------
EXTENDS Naturals

LOCAL INSTANCE FiniteSets

CONSTANT Learner

CONSTANT N_L

ASSUME LearnerGraphSize ==
    /\ N_L \in Nat
    /\ N_L >= 1

ASSUME LearnerGraphCard ==
    /\ IsFiniteSet(Learner)
    /\ Cardinality(Learner) = N_L

=============================================================================
\* Modification History
\* Last modified Tue May 20 09:45:41 CEST 2025 by karbyshev
\* Created Tue May 14 16:43:44 CEST 2024 by karbyshev
