------------------------------ MODULE HLearner ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Learner

CONSTANT N_L
ASSUME LearnerGraphSize ==
    N_L \in Nat /\ N_L >= 1

ASSUME LearnerGraphCard ==
    Cardinality(Learner) = N_L



=============================================================================
\* Modification History
\* Last modified Tue May 14 16:43:55 CEST 2024 by karbyshev
\* Created Tue May 14 16:43:44 CEST 2024 by karbyshev
