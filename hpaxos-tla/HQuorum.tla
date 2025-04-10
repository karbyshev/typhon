------------------------------ MODULE HQuorum -------------------------------
CONSTANTS Proposer,
          SafeAcceptor,
          FakeAcceptor

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorAssumption ==
        SafeAcceptor \cap FakeAcceptor = {}

ByzQuorum == SUBSET Acceptor

\* TODO rename
LEMMA BQAssumption ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor
PROOF BY DEF Acceptor, ByzQuorum

=============================================================================
\* Modification History
\* Last modified Thu Apr 10 21:32:50 CEST 2025 by karbyshev
\* Created Tue May 14 16:29:16 CEST 2024 by karbyshev
