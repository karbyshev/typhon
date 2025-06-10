------------------------------ MODULE HQuorum -------------------------------
LOCAL INSTANCE FiniteSets

CONSTANTS Proposer,
          SafeAcceptor,
          FakeAcceptor

ASSUME AcceptorAssumption == SafeAcceptor \cap FakeAcceptor = {}

ASSUME SafeAcceptorNonTrivial == SafeAcceptor # {}

ASSUME FakeAcceptorFinite == IsFiniteSet(FakeAcceptor)

Acceptor == SafeAcceptor \cup FakeAcceptor

ByzQuorum == SUBSET Acceptor

LEMMA ByzQuorumProperties ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor
PROOF BY DEF Acceptor, ByzQuorum

=============================================================================
\* Modification History
\* Last modified Wed May 21 22:14:39 CEST 2025 by karbyshev
\* Created Tue May 14 16:29:16 CEST 2024 by karbyshev
