------------------------------ MODULE HQuorum -------------------------------
EXTENDS HProposer

LOCAL INSTANCE FiniteSets

CONSTANTS SafeAcceptor,
          FakeAcceptor

ASSUME AcceptorAssumption == SafeAcceptor \cap FakeAcceptor = {}

ASSUME SafeAcceptorNonTrivial == SafeAcceptor # {}

ASSUME FakeAcceptorFinite == IsFiniteSet(FakeAcceptor)

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorNotProposer == Proposer \cap Acceptor = {}

ByzQuorum == SUBSET Acceptor

LEMMA ByzQuorumProperties ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor
PROOF BY DEF Acceptor, ByzQuorum

=============================================================================
\* Modification History
\* Last modified Mon Jul 28 10:36:12 CEST 2025 by karbyshev
\* Created Tue May 14 16:29:16 CEST 2024 by karbyshev
