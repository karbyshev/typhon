--------------------------- MODULE HLearnerGraph ---------------------------
EXTENDS HQuorum, HLearner

CONSTANT TrustLive

ASSUME TrustLiveAssumption ==
    TrustLive \in SUBSET [lr : Learner, q : ByzQuorum]

\* TODO check if can be removed
ASSUME TrustLiveNonEmpty ==
    \A L \in TrustLive : L.q # {}

ASSUME TrustLiveClosure ==
    \A L \in TrustLive : \A Q \in ByzQuorum :
        L.q \in SUBSET Q =>
        [lr |-> L.lr, q |-> Q] \in TrustLive

CONSTANT TrustSafe

ASSUME TrustSafeAssumption ==
    TrustSafe \in SUBSET [from : Learner, to : Learner, q : ByzQuorum]

ASSUME LearnerGraphAssumptionSymmetry ==
    \A E \in TrustSafe :
        [from |-> E.to, to |-> E.from, q |-> E.q] \in TrustSafe

ASSUME LearnerGraphAssumptionTransitivity ==
    \A E1, E2 \in TrustSafe :
        E1.q = E2.q /\ E1.to = E2.from =>
        [from |-> E1.from, to |-> E2.to, q |-> E1.q] \in TrustSafe

ASSUME LearnerGraphAssumptionClosure ==
    \A E \in TrustSafe : \A Q \in ByzQuorum :
        E.q \in SUBSET Q =>
        [from |-> E.from, to |-> E.to, q |-> Q] \in TrustSafe

ASSUME LearnerGraphAssumptionValidity ==
    \A E \in TrustSafe : \A Q1, Q2 \in ByzQuorum :
        [lr |-> E.from, q |-> Q1] \in TrustLive /\
        [lr |-> E.to, q |-> Q2] \in TrustLive =>
        \E N \in E.q : N \in Q1 /\ N \in Q2

(* Entanglement relation *)
Ent == { LL \in Learner \X Learner :
         [from |-> LL[1], to |-> LL[2], q |-> SafeAcceptor] \in TrustSafe }

=============================================================================
\* Modification History
\* Last modified Fri Apr 04 00:10:42 CEST 2025 by karbyshev
\* Created Tue May 14 17:03:34 CEST 2024 by karbyshev
