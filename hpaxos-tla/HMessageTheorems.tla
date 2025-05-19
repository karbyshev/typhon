-------------------------- MODULE HMessageTheorems --------------------------
EXTENDS HMessage

-----------------------------------------------------------------------------

\* TODO clean, not used
LEMMA RefCardinalitySpec ==
    /\ RefCardinality \in SUBSET Nat
    /\ RefCardinality # {}

LEMMA FinSubset_sub ==
    ASSUME NEW S,
           NEW F \in FINSUBSET(S)
    PROVE  F \subseteq S

\* TODO remove, not valid
\*LEMMA FinSubset_sub_nontriv ==
\*    ASSUME NEW S,
\*           S # {},
\*           NEW F \in FINSUBSET(S)
\*    PROVE  F # {}

-----------------------------------------------------------------------------
(* Messages *)

LEMMA MessageRec_def ==
    MessageRec = [n \in Nat |->
                    IF n = 0
                    THEN MessageRec0
                    ELSE MessageRec1(MessageRec[n - 1], n)]

LEMMA MessageRec_spec ==
    /\ \A n \in Nat : MessageRec[n] \subseteq Message
    /\ \A m \in Message : \E n \in Nat : m \in MessageRec[n]

LEMMA MessageRec_eq0 == MessageRec[0] = MessageRec0

LEMMA MessageRec_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  MessageRec[n] = MessageRec1(MessageRec[n - 1], n)

LEMMA MessageRec_monotone_1 ==
    ASSUME NEW n \in Nat
    PROVE  MessageRec[n] \subseteq MessageRec[n + 1]

LEMMA MessageRec_monotone ==
    \A n, m \in Nat : n <= m => MessageRec[n] \subseteq MessageRec[m]

LEMMA MessageRec_nontriv ==
    \A n \in Nat : MessageRec[n] # {}

LEMMA MessageRec_ref0 ==
    ASSUME NEW m \in MessageRec[0]
    PROVE  m.refs = {}

LEMMA MessageRec_ref1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  \A m \in MessageRec[n] : m.refs \subseteq MessageRec[n - 1]

LEMMA Message_nontriv == Message # {}

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

\*LEMMA Message_1a_ref ==
\*    \A m \in Message : OneA(m) <=> m.refs = {}

LEMMA Message_ref ==
    ASSUME NEW m \in Message
    PROVE  m.refs \subseteq Message

LEMMA Message_prev ==
    ASSUME NEW m \in Message
    PROVE  m.prev \in Message \cup {NoMessage}

LEMMA MessageRec_min ==
    ASSUME NEW m \in Message
    PROVE  \E n \in Nat :
            /\ m \in MessageRec[n]
            /\ \A k \in 0 .. n - 1 : m \notin MessageRec[k]

LEMMA Message_ref_acyclic ==
    ASSUME NEW m \in Message
    PROVE  m \notin m.refs

-----------------------------------------------------------------------------
LEMMA NoMessageIsNotAMessage ==
    NoMessage \notin Message

LEMMA MessageSpec ==
    ASSUME NEW m \in Message
    PROVE \/ /\ m.type = "1a"
             /\ m.bal \in Ballot
             /\ m.prev = NoMessage
             /\ m.refs = {}
          \/ /\ \/ m.type = "1b"
                \/ m.type = "2a"
                \/ m.type = "2b"
             /\ m.acc \in Acceptor
             /\ m.prev \in Message \cup {NoMessage}
\*             /\ m.refs # {}
             /\ m.refs \in SUBSET Message
             /\ m.lrns \in SUBSET Learner

LEMMA MessageTypeSpec ==
    ASSUME NEW m \in Message
    PROVE \/ /\  OneA(m)
             /\ ~OneB(m)
             /\ ~TwoA(m)
             /\ ~TwoB(m)
          \/ /\ ~OneA(m)
             /\  OneB(m)
             /\ ~TwoA(m)
             /\ ~TwoB(m)
          \/ /\ ~OneA(m)
             /\ ~OneB(m)
             /\  TwoA(m)
             /\ ~TwoB(m)
          \/ /\ ~OneA(m)
             /\ ~OneB(m)
             /\ ~TwoA(m)
             /\  TwoB(m)

LEMMA MessageNonProposalSpec ==
    ASSUME NEW m \in Message,
           ~Proposal(m)
    PROVE  \/ OneB(m)
           \/ TwoA(m)
           \/ TwoB(m)

-----------------------------------------------------------------------------
(* Transitive references *)

LEMMA TranBound_def ==
    TranBound = [n \in Nat |->
                    IF n = 0
                    THEN TranBound0
                    ELSE TranBound1(TranBound[n - 1], n)]

LEMMA Tran_spec ==
    ASSUME NEW m \in Message
    PROVE  /\ \A n \in Nat : TranBound[n][m] \subseteq Tran(m)
           /\ \A r \in Tran(m) : \E n \in Nat : r \in TranBound[n][m]

LEMMA TranBound_eq0 ==
    TranBound[0] = [m \in Message |-> {m}]

LEMMA TranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  TranBound[n] =
            [m \in Message |-> {m} \cup UNION {TranBound[n - 1][r] : r \in m.refs}]

LEMMA Tran_refl ==
    ASSUME NEW m \in Message PROVE m \in Tran(m)

LEMMA Tran_eq ==
    ASSUME NEW m \in Message
    PROVE  Tran(m) = {m} \cup UNION { Tran(r) : r \in m.refs }

LEMMA Tran_1a ==
    ASSUME NEW m \in Message, OneA(m)
    PROVE  Tran(m) = {m}

LEMMA TranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat
    PROVE  TranBound[n][m1] \in SUBSET Message

LEMMA Tran_Message ==
    ASSUME NEW m1 \in Message
    PROVE  Tran(m1) \in SUBSET Message

LEMMA TranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE  TranBound[n][m] \subseteq TranBound[n + 1][m]

LEMMA TranBound_monotone ==
    \A n, m \in Nat : n <= m =>
        \A mm \in Message :
            TranBound[n][mm] \subseteq TranBound[m][mm]

LEMMA Message_ref_TranBound1 ==
    ASSUME NEW m1 \in Message
    PROVE  m1.refs \in SUBSET TranBound[1][m1]

LEMMA TranBound_trans ==
    ASSUME NEW n1 \in Nat, NEW n2 \in Nat,
           NEW m1 \in Message,
           NEW m2 \in TranBound[n1][m1],
           NEW m3 \in TranBound[n2][m2]
    PROVE  m3 \in TranBound[n1 + n2][m1]

LEMMA Tran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1), NEW m3 \in Tran(m2)
    PROVE  m3 \in Tran(m1)

LEMMA Message_ref_Tran ==
    ASSUME NEW m \in Message
    PROVE  m.refs \subseteq Tran(m)

LEMMA MessageRec0_Tran ==
    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in Tran(m1)
    PROVE  m1 = m2

LEMMA MessageRec_Tran_bound ==
    ASSUME NEW n \in Nat, NEW m1 \in MessageRec[n], NEW m2 \in Tran(m1)
    PROVE  m2 \in MessageRec[n]

LEMMA Tran_ref_acyclic ==
    ASSUME NEW m \in Message, NEW r \in m.refs
    PROVE  m \notin Tran(r)

LEMMA Tran_acyclic ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           m1 \in Tran(m2)
    PROVE  m1 = m2

-----------------------------------------------------------------------------
(* Transitive references of prev *)

LEMMA PrevTranBound_def ==
    PrevTranBound = [n \in Nat |->
                    IF n = 0
                    THEN PrevTranBound0
                    ELSE PrevTranBound1(PrevTranBound[n - 1], n)]

LEMMA PrevTran_spec ==
    ASSUME NEW m \in Message
    PROVE  /\ \A n \in Nat : PrevTranBound[n][m] \subseteq PrevTran(m)
           /\ \A r \in PrevTran(m) : \E n \in Nat : r \in PrevTranBound[n][m]

LEMMA PrevTranBound_eq0 ==
    PrevTranBound[0] = [m \in Message |-> {m}]

LEMMA PrevTranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  PrevTranBound[n] =
            [m \in Message |-> {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTranBound[n - 1][m.prev]]

LEMMA PrevTranBound_eq1_prev ==
    ASSUME NEW n \in Nat, n # 0,
           NEW m \in Message, m.prev # NoMessage
    PROVE  PrevTranBound[n][m] = {m} \cup PrevTranBound[n - 1][m.prev]

LEMMA PrevTranBound_refl ==
    ASSUME NEW n \in Nat,
           NEW m \in Message 
    PROVE  m \in PrevTranBound[n][m]

LEMMA PrevTran_refl ==
    ASSUME NEW m \in Message PROVE m \in PrevTran(m)

LEMMA PrevTran_eq ==
    ASSUME NEW m \in Message
    PROVE  PrevTran(m) = {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)

LEMMA PrevTran_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  PrevTran(m) = {m}

LEMMA PrevTranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat
    PROVE  PrevTranBound[n][m1] \in SUBSET Message

LEMMA PrevTran_Message ==
    ASSUME NEW m1 \in Message
    PROVE  PrevTran(m1) \in SUBSET Message

LEMMA PrevTranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE  PrevTranBound[n][m] \subseteq PrevTranBound[n + 1][m]

LEMMA PrevTranBound_monotone ==
    \A n, m \in Nat : n <= m =>
        \A mm \in Message :
            PrevTranBound[n][mm] \subseteq PrevTranBound[m][mm]

LEMMA Message_prev_PrevTranBound1 ==
    ASSUME NEW m \in Message, m.prev # NoMessage
    PROVE  m.prev \in PrevTranBound[1][m]

LEMMA PrevTranBound_trans ==
    ASSUME NEW n1 \in Nat, NEW n2 \in Nat,
           NEW m1 \in Message,
           NEW m2 \in PrevTranBound[n1][m1],
           NEW m3 \in PrevTranBound[n2][m2]
    PROVE  m3 \in PrevTranBound[n1 + n2][m1]

LEMMA PrevTran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in PrevTran(m1), NEW m3 \in PrevTran(m2)
    PROVE  m3 \in PrevTran(m1)

LEMMA Message_prev_PrevTran ==
    ASSUME NEW m \in Message, m.prev # NoMessage
    PROVE  m.prev \in PrevTran(m)

\*LEMMA MessageRec0_PrevTran ==
\*    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in PrevTran(m1)
\*    PROVE  m1 = m2

=============================================================================
\* Modification History
\* Last modified Mon May 19 21:08:03 CEST 2025 by karbyshev
\* Created Mon May 19 20:59:25 CEST 2025 by karbyshev
