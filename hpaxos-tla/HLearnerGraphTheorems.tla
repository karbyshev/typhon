----------------------- MODULE HLearnerGraphTheorems -----------------------
EXTENDS HLearnerGraph

LEMMA TrustSafeSelfAgreement ==
    ASSUME NEW E \in TrustSafe
    PROVE  [from |-> E.from, to |-> E.from, q |-> E.q] \in TrustSafe

LEMMA EntanglementSym ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE  <<L2, L1>> \in Ent

LEMMA EntanglementTransitive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, NEW L3 \in Learner,
           <<L1, L2>> \in Ent, <<L2, L3>> \in Ent
    PROVE  <<L1, L3>> \in Ent

LEMMA EntanglementSelf ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE  <<L1, L1>> \in Ent

\* TODO remove if not used
LEMMA EntangledAccurate ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE  Accurate(L1)

LEMMA EntanglementTrustLive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q1 \in ByzQuorum, NEW Q2 \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q1] \in TrustLive,
           [lr |-> L2, q |-> Q2] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q1 /\ N \in Q2

LEMMA EntaglementTrustLiveNonEmpty ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q

=============================================================================
\* Modification History
\* Last modified Wed May 28 21:05:50 CEST 2025 by karbyshev
\* Created Mon May 19 20:42:04 CEST 2025 by karbyshev
