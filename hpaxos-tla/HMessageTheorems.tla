-------------------------- MODULE HMessageTheorems --------------------------
EXTENDS HMessage

LOCAL INSTANCE FiniteSets

-----------------------------------------------------------------------------

\* TODO clean, not used
LEMMA RefCardinalitySpec ==
    /\ RefCardinality \in SUBSET Nat
    /\ RefCardinality # {}

LEMMA FinSubset_sub ==
    ASSUME NEW S,
           NEW F \in FINSUBSET(S)
    PROVE  F \subseteq S

-----------------------------------------------------------------------------
(* Messages *)

LEMMA OneA_Message ==
    ASSUME NEW bal \in Ballot
    PROVE  LET msg == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> {} ] IN
           /\ msg \in Message
           /\ OneA(msg)

\* TODO needs IsFinite(P)
LEMMA OneB_Message ==
    ASSUME NEW A \in Acceptor,
           NEW P \in Message \cup {NoMessage},
           NEW R \in SUBSET Message,
           R # {}
    PROVE  LET msg == [ type |-> "1b", acc |-> A, prev |-> P, refs |-> R, lrns |-> {} ] IN
           /\ msg \in Message
           /\ OneB(msg)

\* TODO needs IsFinite(P)
LEMMA TwoA_Message ==
    ASSUME NEW A \in Acceptor,
           NEW P \in Message \cup {NoMessage},
           NEW R \in SUBSET Message,
           R # {}
    PROVE  LET msg == [ type |-> "2a", acc |-> A, prev |-> P, refs |-> R, lrns |-> {} ] IN
           /\ msg \in Message
           /\ TwoA(msg)

LEMMA OneB_Message_bis ==
    ASSUME NEW A \in Acceptor,
           NEW P \in Message \cup {NoMessage},
           NEW R \in SUBSET Message,
           IsFiniteSet(R),
           P \in R
    PROVE  LET msg == [ type |-> "1b", acc |-> A, prev |-> P, refs |-> R, lrns |-> {} ] IN
           /\ msg \in Message
           /\ OneB(msg)

LEMMA TwoA_Message_bis ==
    ASSUME NEW A \in Acceptor,
           NEW P \in Message \cup {NoMessage},
           NEW R \in SUBSET Message,
           IsFiniteSet(R),
           P \in R,
           NEW L \in SUBSET Learner
    PROVE  LET msg == [ type |-> "2a", acc |-> A, prev |-> P, refs |-> R, lrns |-> L ] IN
           /\ msg \in Message
           /\ TwoA(msg)

\*LEMMA Message_ref ==
\*    ASSUME NEW m \in Message
\*    PROVE  m.refs \subseteq Message
\*
\*LEMMA Message_prev ==
\*    ASSUME NEW m \in Message
\*    PROVE  m.prev \in Message \cup {NoMessage}
\*
\*LEMMA Message_ref_acyclic ==
\*    ASSUME NEW m \in Message
\*    PROVE  m \notin m.refs

-----------------------------------------------------------------------------
LEMMA NoMessageIsNotAMessage ==
    NoMessage \notin Message

LEMMA MessageSpec ==
    ASSUME NEW m \in Message
    PROVE  \/ /\ m.type = "1a"
              /\ m.bal \in Ballot
              /\ m.prev = NoMessage
              /\ m.refs \in SUBSET Message
           \/ /\ \/ m.type = "1b"
                 \/ m.type = "2a"
              /\ m.acc \in Acceptor
              /\ m.prev \in Message \cup {NoMessage}
              /\ m.refs \in SUBSET Message
              /\ m.lrns \in SUBSET Learner

LEMMA MessageTypeSpec ==
    ASSUME NEW m \in Message
    PROVE  \/ /\  OneA(m)
              /\ ~OneB(m)
              /\ ~TwoA(m)
           \/ /\ ~OneA(m)
              /\  OneB(m)
              /\ ~TwoA(m)
           \/ /\ ~OneA(m)
              /\ ~OneB(m)
              /\  TwoA(m)

-----------------------------------------------------------------------------
(* Transitive references *)

LEMMA Tran_refl ==
    ASSUME NEW m \in Message PROVE m \in Tran(m)

LEMMA Tran_eq ==
    ASSUME NEW m \in Message
    PROVE  Tran(m) = {m} \cup UNION { Tran(r) : r \in m.refs }

LEMMA Tran_Message ==
    ASSUME NEW m1 \in Message
    PROVE  Tran(m1) \in SUBSET Message

LEMMA Tran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1), NEW m3 \in Tran(m2)
    PROVE  m3 \in Tran(m1)

LEMMA Message_ref_Tran ==
    ASSUME NEW m \in Message
    PROVE  m.refs \subseteq Tran(m)

LEMMA Tran_ref_acyclic ==
    ASSUME NEW m \in Message, NEW r \in m.refs
    PROVE  m \notin Tran(r)

LEMMA Tran_acyclic ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           m1 \in Tran(m2)
    PROVE  m1 = m2

-----------------------------------------------------------------------------
(* Transitive references of prev *)

LEMMA PrevTran_refl ==
    ASSUME NEW m \in Message PROVE m \in PrevTran(m)

LEMMA PrevTran_eq ==
    ASSUME NEW m \in Message
    PROVE  PrevTran(m) = {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)

LEMMA PrevTran_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  PrevTran(m) = {m}

\*LEMMA PrevTran_Message ==
\*    ASSUME NEW m1 \in Message
\*    PROVE  PrevTran(m1) \in SUBSET Message

LEMMA PrevTran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in PrevTran(m1), NEW m3 \in PrevTran(m2)
    PROVE  m3 \in PrevTran(m1)

LEMMA Message_prev_PrevTran ==
    ASSUME NEW m \in Message, m.prev # NoMessage
    PROVE  m.prev \in PrevTran(m)

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 15:18:38 CEST 2025 by karbyshev
\* Created Mon May 19 20:59:25 CEST 2025 by karbyshev
