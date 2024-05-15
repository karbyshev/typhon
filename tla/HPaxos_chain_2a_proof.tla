----------------------- MODULE HPaxos_chain_2a_proof ------------------------
EXTENDS HPaxos_chain_2a, Sequences, HMessage_proof, TLAPS

-----------------------------------------------------------------------------
LEMMA CaughtMsgSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg(M) \in SUBSET Message
           /\ \A X \in CaughtMsg(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg

LEMMA CaughtMsgEffSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg0(M) \in SUBSET Message
           /\ \A X \in CaughtMsg0(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg0

-----------------------------------------------------------------------------
(* Facts about Get1a, B and V relations *)

LEMMA Get1a_TypeOK ==
    ASSUME NEW m \in Message
    PROVE  /\ Get1a(m) \subseteq Message
           /\ \A x \in Get1a(m) : x.bal \in Ballot
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a

LEMMA Get1a_correct ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m), NEW y \in Get1a(m)
    PROVE  x.bal = y.bal
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a, Ballot

LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE  b1 = b2
PROOF BY DEF B, Get1a, Ballot

LEMMA B_def ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m)
    PROVE  \E b \in Ballot : B(m, b)
PROOF BY Get1a_correct, Get1a_TypeOK DEF B

LEMMA B_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  B(m, m.bal)
PROOF BY MessageTypeSpec, Tran_1a DEF B, Get1a, Ballot

LEMMA V_func ==
    ASSUME NEW m \in Message,
           NEW v1 \in Value, V(m, v1),
           NEW v2 \in Value, V(m, v2)
    PROVE  v1 = v2
PROOF BY Get1a_correct DEF V

LEMMA V_def ==
    ASSUME BVal \in [Ballot -> Value],
           NEW m \in Message,
           NEW b \in Ballot, B(m, b)
    PROVE V(m, BVal[b])
PROOF BY Get1a_TypeOK DEF V, B

LEMMA TranBallot ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           NEW b1 \in Ballot, NEW b2 \in Ballot,
           B(m1, b1), B(m2, b2)
    PROVE  b2 <= b1
PROOF BY Tran_trans DEF B, Get1a

-----------------------------------------------------------------------------
\* Check equivalence of two well-formedness conditions

LEMMA WellFormedCondition1 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    PROVE  \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m)
PROOF
<1> SUFFICES ASSUME NEW y \in Tran(m), m # y, SameBallot(m, y)
             PROVE  y \in Get1a(m)
    OBVIOUS
<1> y.type = "1a" OBVIOUS
<1> y \in Message BY Tran_Message
<1> y.bal \in Ballot BY MessageTypeSpec
<1> B(y, y.bal) BY B_1a
<1> SUFFICES ASSUME NEW z \in Tran(m), z.type = "1a"
             PROVE  z.bal =< y.bal
    BY DEF Get1a
<1> z \in Message BY Tran_Message
<1> z.bal \in Ballot BY MessageTypeSpec
<1> B(z, z.bal) BY B_1a
<1> QED BY TranBallot DEF SameBallot

\* Equivalence of two well-formedness conditions
LEMMA WellFormedConditionEquiv1 ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE  (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m))
           <=>
           (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a")
PROOF BY WellFormedCondition1 DEF Get1a

LEMMA WellFormedCondition2 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    PROVE  \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
PROOF BY Tran_Message, B_func DEF SameBallot

LEMMA WellFormedConditionEquiv2 ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE (\A y \in Tran(m) :
            m # y /\
            (\E bm \in Ballot : B(m, bm)) /\
            (\E by \in Ballot : B(y, by)) /\
            SameBallot(m, y) => y.type = "1a")
          <=>
          (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
PROOF BY Tran_Message, B_func DEF SameBallot

LEMMA WellFormedCondition3 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
    PROVE  \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
PROOF BY TranBallot DEF Ballot

LEMMA WellFormedConditionEquiv3 ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
          <=>
          (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm)
PROOF BY TranBallot DEF Ballot

LEMMA WellFormedCondition4 ==
    ASSUME NEW m \in Message,
           \A y \in m.ref :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
    PROVE \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
\*PROOF BY Message_ref, Tran_Message, Tran_eq, TranBallot DEF Ballot
OMITTED

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor -> SUBSET Message]
    /\ prev_msg \in [Acceptor -> Message \cup {NoMessage}]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]
    /\ BVal \in [Ballot -> Value]

-----------------------------------------------------------------------------
SentBy(acc) == { mm \in msgs : mm.type # "1a" /\ mm.acc = acc }

Sent1bBy(acc) == { mm \in msgs : mm.type = "1b" /\ mm.acc = acc }

RecentMsgsSpec1 ==
    \A A \in SafeAcceptor :
        \A x \in recent_msgs[A] :
            x.acc = A /\ x.type # "1a" => x \in SentBy(A)

RecentMsgsSpec2 ==
    \A A \in SafeAcceptor :
        \A x \in SentBy(A) :
            x \notin known_msgs[A] => x \in recent_msgs[A]

KnownMsgsSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ known_msgs[AL] \in SUBSET msgs
        /\ \A M \in known_msgs[AL] :
            /\ KnownRefs(AL, M)
            /\ WellFormed(M)
            /\ Tran(M) \in SUBSET known_msgs[AL]
            /\ \E b \in Ballot : B(M, b)

CaughtSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught(M) \cap SafeAcceptor = {}

CaughtEffSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught0(M) \cap SafeAcceptor = {}

DecisionSpec ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \in decision[L, BB] => ChosenIn(L, BB, VV)

SafeAcceptorPrevSpec1 ==
    \A A \in SafeAcceptor :
        SentBy(A) = {} <=> prev_msg[A] = NoMessage

SafeAcceptorPrevSpec2 ==
    \A A \in SafeAcceptor :
        prev_msg[A] # NoMessage =>
            /\ prev_msg[A] \in recent_msgs[A]
            /\ prev_msg[A] \in SentBy(A)
            /\ \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])

RecentMsgsUniquePreviousMessageSpec ==
    \A A \in SafeAcceptor :
        \A x, y \in recent_msgs[A] :
            x.type # "1a" /\ y.type # "1a" /\
            x.acc = A /\ y.acc = A =>
            x = y

MsgsSafeAcceptorSpec3 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1.prev = m2.prev => m1 = m2

MsgsSafeAcceptorPrevRefSpec ==
    \A A \in SafeAcceptor :
        \A m \in SentBy(A) :
            m.prev # NoMessage => m.prev \in m.ref

MsgsSafeAcceptorPrevTranSpec ==
    \A A \in SafeAcceptor :
        \A m1 \in SentBy(A) :
            \A m2 \in PrevTran(m1) :
                m2 \in Tran(m1)

MsgsSafeAcceptorPrevTranLinearSpec ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1 \in PrevTran(m2) \/ m2 \in PrevTran(m1)

-----------------------------------------------------------------------------

LEMMA WellFormedMessage ==
    ASSUME NEW M, WellFormed(M) PROVE M \in Message
BY DEF WellFormed

LEMMA TypeOKInvariant ==
    TypeOK /\ NextTLA => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA PROVE TypeOK' OBVIOUS
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> [type |-> "1a", bal |-> bal, prev |-> NoMessage, ref |-> {}] \in Message
      BY Message_spec, MessageRec_eq0 DEF MessageRec0
  <2> QED BY Zenon DEF Send1a, Send, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> m1a \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Recv, TypeOK
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> new1b \in Message
      OBVIOUS
  <2> recent_msgs' \in [Acceptor -> SUBSET Message]
    <3> CASE WellFormed1b(new1b)
        BY Isa DEF TypeOK
    <3> QED BY DEF TypeOK
  <2> QED BY DEF TypeOK, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> acc \in Acceptor BY DEF Acceptor
  <2> m1b \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Recv, TypeOK
  <2> recent_msgs' \in [Acceptor -> SUBSET Message]
    <4> PICK ll \in SUBSET Learner :
        LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                      prev |-> prev_msg[acc],
                      ref |-> recent_msgs[acc] \cup {m1b}] IN
        /\ new2a \in Message
        /\ Send(new2a)
        /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new2a}]
        /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
        BY Zenon
    <4> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                         prev |-> prev_msg[acc],
                         ref  |-> recent_msgs[acc] \cup {m1b}]
    <4> new2a \in Message
        OBVIOUS
    <4> QED BY Zenon DEF TypeOK
  <2> QED BY DEF TypeOK, Send
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> USE DEF Process2a
  <2> QED BY DEF TypeOK, Recv
<1>7. CASE \E l \in Learner : LearnerAction(l)
      BY <1>7, Isa DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8, WellFormedMessage, Zenon
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send, TypeOK
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8
          DEF NextTLA, AcceptorProcessAction

LEMMA UniqueMessageSent ==
    TypeOK /\ NextTLA =>
    \A m1, m2 \in msgs' \ msgs :
        m1 = m2
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    NEW M1 \in msgs' \ msgs,
                    NEW M2 \in msgs' \ msgs
             PROVE  M1 = M2
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Zenon DEF Send1a, Send
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY Isa DEF Process1a, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY Isa DEF Process1b, Send
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY DEF Process2a, Send
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY Isa, <1>8 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
          DEF NextTLA, AcceptorProcessAction, LearnerAction

LEMMA WellFormed_monotone ==
    ASSUME NEW m \in Message, WellFormed(m), BVal' = BVal
    PROVE WellFormed(m)'
PROOF BY Isa DEF WellFormed, WellFormed1b, WellFormed2a, q, Fresh, Con2as, Buried, V

LEMMA KnownMsgMonotone ==
    TypeOK /\ NextTLA =>
    \A AL \in SafeAcceptor \cup Learner :
        known_msgs[AL] \subseteq known_msgs[AL]'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL]
             PROVE  M \in known_msgs[AL]'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY DEF Process1a, Recv, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> QED BY DEF Process1b, Recv, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, m2a \in msgs : Process2a(acc, m2a)
      BY <1>4
  <2> QED BY DEF Process2a, Recv, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, Recv, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
           DEF NextTLA, AcceptorProcessAction, LearnerAction

LEMMA Known2aMonotone ==
    TypeOK /\ NextTLA =>
    \A L \in Learner, bal \in Ballot, val \in Value :
        Known2a(L, bal, val) \subseteq Known2a(L, bal, val)'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    NEW S \in Known2a(L, BB, VV)
             PROVE  S \in Known2a(L, BB, VV)'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF Known2a
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY KnownMsgMonotone DEF Send1a, V, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY KnownMsgMonotone DEF Process1a, V, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY KnownMsgMonotone DEF Process1b, V, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY KnownMsgMonotone DEF Process2a, V, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, KnownMsgMonotone DEF LearnerRecv, V, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8, KnownMsgMonotone, Zenon DEF LearnerDecide, V, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, KnownMsgMonotone
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, V, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
          DEF NextTLA, AcceptorProcessAction, LearnerAction

LEMMA RecentMsgsSpec1Invariant ==
    TypeOK /\ RecentMsgsSpec1 /\ NextTLA =>
    RecentMsgsSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, RecentMsgsSpec1, NextTLA,
                    NEW A \in SafeAcceptor,
                    NEW M \in recent_msgs[A]',
                    M.type # "1a",
                    M.acc = A
             PROVE  M \in SentBy(A)'
    BY DEF RecentMsgsSpec1
<1> TypeOK' BY TypeOKInvariant
<1> SafeAcceptor \in SUBSET Acceptor
    BY DEF Acceptor
<1> A \in Acceptor
    OBVIOUS
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Zenon DEF RecentMsgsSpec1, Send1a, SentBy, Send, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> new1b \in Message
      OBVIOUS
  <2> CASE WellFormed1b(new1b)
    <3> msgs' = msgs \cup {new1b}
        BY DEF Send
    <3> recent_msgs' = [recent_msgs EXCEPT ![acc] = {new1b}]
        OBVIOUS
    <3> CASE A # acc
        BY DEF RecentMsgsSpec1, SentBy, Send, TypeOK
    <3> CASE A = acc
      <4> M = new1b
          BY DEF RecentMsgsSpec1, TypeOK
      <4> QED BY Zenon DEF RecentMsgsSpec1, SentBy, Send, TypeOK
    <3> QED OBVIOUS
  <2> CASE ~WellFormed1b(new1b)
    <3> QED BY Zenon DEF RecentMsgsSpec1, Recv, Send, SentBy, TypeOK
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> m1b \in Message BY DEF TypeOK
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      recent_msgs' = [recent_msgs EXCEPT ![acc] = {new2a}]
      BY Zenon DEF TypeOK
  <2> QED BY Zenon DEF RecentMsgsSpec1, Recv, Send, SentBy, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, m2a \in msgs : Process2a(acc, m2a)
      BY <1>4
  <2> USE DEF Process2a
  <2> QED BY Zenon DEF RecentMsgsSpec1, SentBy, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, msg \in msgs : LearnerRecv(lrn, msg)
      BY <1>7
  <2> QED BY Zenon DEF RecentMsgsSpec1, LearnerRecv, SentBy, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY Zenon, <1>8 DEF RecentMsgsSpec1, LearnerDecide, SentBy, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, Zenon DEF RecentMsgsSpec1, FakeAcceptorAction, FakeSend1b, FakeSend2a, SentBy, Send, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
           DEF NextTLA, AcceptorProcessAction, LearnerAction

LEMMA DecisionSpecInvariant ==
    TypeOK /\ NextTLA /\
    DecisionSpec => DecisionSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA, DecisionSpec,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    VV \in decision[L, BB]'
             PROVE  ChosenIn(L, BB, VV)'
    BY DEF DecisionSpec
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF DecisionSpec
<1> USE DEF ChosenIn
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Known2aMonotone DEF Send1a
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY Known2aMonotone DEF Process1a
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY Known2aMonotone DEF Process1b
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY Known2aMonotone DEF Process2a
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, Known2aMonotone DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, BVal >>
      BY <1>8, Zenon DEF LearnerDecide
  <2>0. QED BY Known2aMonotone DEF TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, Known2aMonotone DEF FakeAcceptorAction, FakeSend1b, FakeSend2a
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
          DEF NextTLA, AcceptorProcessAction, LearnerAction

LEMMA SafeAcceptorPrevSpec1Invariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 =>
    SafeAcceptorPrevSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec1
             PROVE  SafeAcceptorPrevSpec1'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor
             PROVE  SentBy(A)' = {} <=> prev_msg[A]' = NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF SafeAcceptorPrevSpec1
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2>1. CASE acc = A
    <3> DEFINE new1b == [type |-> "1b", acc |-> acc, prev |-> prev_msg[acc],
                         ref |-> recent_msgs[acc] \cup {m1a}]
    <3> new1b \in Message
        OBVIOUS
    <3> CASE WellFormed1b(new1b)
        <4> prev_msg' = [prev_msg EXCEPT ![acc] = new1b]
            OBVIOUS
        <4> new1b \in msgs'
            BY <2>1 DEF Send
        <4> QED BY <2>1, NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
    <3> CASE ~WellFormed1b(new1b)
        <4> QED BY <2>1 DEF SentBy, TypeOK
    <3> QED OBVIOUS
  <2>2. CASE acc # A
        BY <2>2 DEF SentBy, Send, TypeOK
  <2> QED BY <2>1, <2>2
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
        LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                      prev |-> prev_msg[acc],
                      ref |-> recent_msgs[acc] \cup {m1b}] IN
        /\ new2a \in Message
        /\ Send(new2a)
        /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> new2a \in Message
      OBVIOUS
  <2> prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon
  <2> new2a \in msgs'
      BY Zenon DEF Send
  <2> new2a.acc = acc
      OBVIOUS
  <2> CASE acc # A
      BY NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
  <2> QED BY Zenon, NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY DEF Process2a, SentBy, Send, TypeOK
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction, FakeAcceptorAction

LEMMA SafeAcceptorPrevSpec2Invariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 =>
    SafeAcceptorPrevSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2
             PROVE  SafeAcceptorPrevSpec2'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    prev_msg[A]' # NoMessage
             PROVE  /\ prev_msg[A]' \in recent_msgs[A]'
                    /\ prev_msg[A]' \in SentBy(A)'
                    /\ \A m \in SentBy(A)' : m \in PrevTran(prev_msg[A]')
    BY DEF SafeAcceptorPrevSpec2
<1> A \in Acceptor BY DEF Acceptor
<1> SentBy(A) \in SUBSET Message
    BY DEF SentBy, TypeOK
<1> SentBy(A)' \in SUBSET Message
    BY DEF SentBy, TypeOK
<1> USE DEF SafeAcceptorPrevSpec2
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> CASE acc # A
      BY DEF Process1a, SentBy, Send, TypeOK
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> new1b \in Message
      OBVIOUS
  <2> CASE ~WellFormed1b(new1b)
      BY DEF Send, SentBy, TypeOK
  <2> CASE acc = A /\ WellFormed1b(new1b)
    <3> msgs' = msgs \cup {new1b}
        BY DEF Send
    <3> new1b \in Message
        BY DEF TypeOK
    <3> new1b # NoMessage
        BY Zenon, NoMessageIsNotAMessage
    <3> new1b.prev = prev_msg[A]
        OBVIOUS
    <3> SentBy(A)' = SentBy(A) \cup {new1b}
        BY DEF Send, SentBy
    <3> prev_msg[A]' = new1b
        BY DEF Send, TypeOK
    <3> prev_msg[A]' \in recent_msgs[A]'
        BY DEF TypeOK
    <3> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in PrevTran(new1b)
        BY Message_prev_PrevTran DEF SafeAcceptorPrevSpec1
    <3> HIDE DEF new1b
    <3> QED BY PrevTran_trans, PrevTran_refl DEF SafeAcceptorPrevSpec1
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs :
            /\ Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      /\ new2a \in Message
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new2a}]
      BY Zenon
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> new2a \in Message
      OBVIOUS
  <2> CASE acc = A
      <4> msgs' = msgs \cup {new2a}
          BY DEF Send
      <4> new2a # NoMessage
          BY Zenon, NoMessageIsNotAMessage
      <4> new2a.prev = prev_msg[A]
          OBVIOUS
      <4> SentBy(A)' = SentBy(A) \cup {new2a}
          BY DEF Send, SentBy
      <4> prev_msg[A]' = new2a
          BY Zenon DEF Send, TypeOK
      <4> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in PrevTran(new2a)
          BY Message_prev_PrevTran DEF SafeAcceptorPrevSpec1
      <4> prev_msg[A]' \in SentBy(A)'
          OBVIOUS
      <4> prev_msg[A]' \in recent_msgs[A]'
          BY DEF TypeOK
      <4> HIDE DEF new2a
      <4> QED BY PrevTran_trans, PrevTran_refl DEF SafeAcceptorPrevSpec1      
  <2> CASE acc # A
      BY DEF SentBy, Send
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            Process2a(acc, msg)
      BY <1>4
  <2> QED BY DEF Process2a, Send, SentBy
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction, FakeAcceptorAction

\* TODO
LEMMA RecentMsgsSafeAcceptorSpec1Invariant ==
    TypeOK /\ NextTLA /\
    RecentMsgsUniquePreviousMessageSpec =>
    RecentMsgsUniquePreviousMessageSpec'
OMITTED

LEMMA KnownMsgsSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec2 /\
    KnownMsgsSpec =>
    KnownMsgsSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec2,
                    KnownMsgsSpec
             PROVE  KnownMsgsSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL]'
             PROVE  /\ known_msgs[AL]' \in SUBSET msgs'
                    /\ KnownRefs(AL, M)'
                    /\ WellFormed(M)'
                    /\ Tran(M) \in SUBSET known_msgs[AL]'
                    /\ \E b \in Ballot : B(M, b)
    BY DEF KnownMsgsSpec
<1> USE DEF KnownMsgsSpec
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> USE DEF Send1a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Send, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send, Recv
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Recv, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      BY Tran_1a DEF Recv, TypeOK
  <2> \E b \in Ballot : B(M, b)
    <3> CASE M \notin known_msgs[AL]
      <4> M = m1a
          BY DEF Recv
      <4> QED BY B_1a, MessageTypeSpec DEF Recv, TypeOK
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> known_msgs[AL]' \in SUBSET msgs'
    <3> PICK ll \in SUBSET Learner :
        LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                      prev |-> prev_msg[acc],
                      ref |-> recent_msgs[acc] \cup {m1b}] IN
        new2a \in Message
        BY Zenon DEF TypeOK
    <3> QED BY DEF Send, Recv
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Recv, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> M = m1b BY DEF Recv
      <4> AL = acc BY DEF Recv
      <4> M \in Message BY DEF WellFormed
      <4> QED BY Tran_eq, KnownMsgMonotone DEF Recv, KnownRefs
    <3> QED BY DEF Recv
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, m2a \in msgs : Process2a(acc, m2a)
      BY <1>4
  <2> USE DEF Process2a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send, Recv
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Send, Recv, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      BY Tran_eq DEF Recv, KnownRefs, TypeOK
  <2> \E b \in Ballot : B(M, b)
    <3> CASE M \notin known_msgs[AL]
      <4> M = m2a
          BY DEF Recv
      <4> AL = acc BY DEF Recv
      <4> M \in Message BY DEF WellFormed
      <4> QED BY DEF WellFormed
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, m \in msgs : LearnerRecv(lrn, m)
      BY <1>6
  <2> USE DEF LearnerRecv
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Recv
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK, Recv
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> QED BY Tran_eq DEF Recv, KnownRefs, TypeOK
    <3> QED BY DEF Recv
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7
  <2> USE DEF LearnerDecide
  <2> known_msgs[AL]' \in SUBSET msgs'
      OBVIOUS
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>8. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>8
  <2> USE DEF FakeSend1b
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1>9. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>9
  <2> USE DEF FakeSend2a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8, <1>9
        DEF NextTLA, AcceptorProcessAction, LearnerRecv,
            LearnerAction, FakeAcceptorAction

LEMMA MsgsSafeAcceptorPrevTranLinearSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevTranLinearSpec =>
    MsgsSafeAcceptorPrevTranLinearSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2,
                    MsgsSafeAcceptorPrevTranLinearSpec
             PROVE  MsgsSafeAcceptorPrevTranLinearSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs, NEW m2 \in msgs' \ msgs,
                    m1.type # "1a", m2.type # "1a",
                    m1.acc = A, m2.acc = A
             PROVE  m1 \in PrevTran(m2)
  <2> USE DEF MsgsSafeAcceptorPrevTranLinearSpec
  <2> QED BY UniqueMessageSent, PrevTran_refl DEF SentBy, TypeOK
<1> m1 \in SentBy(A)
    BY DEF SentBy
<1> prev_msg[A] # NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
      BY <1>1 DEF ProposerSendAction, Send1a, Send
<1>2. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> acc = A BY DEF Send
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m2 = new1b BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[A] \in PrevTran(m2)
      BY Message_prev_PrevTran
  <2> QED BY PrevTran_trans DEF SentBy
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      /\ new2a \in Message
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon DEF TypeOK
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> m2 = new2a BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[A] \in PrevTran(m2)
      BY Message_prev_PrevTran
  <2> QED BY PrevTran_trans DEF SentBy
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
      BY <1>4 DEF Process2a, Send
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSend1b(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send
<1>8. CASE \E acc \in FakeAcceptor : FakeSend2a(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction,
            FakeAcceptorAction

LEMMA MsgsSafeAcceptorSpec3Invariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec /\
    MsgsSafeAcceptorPrevRefSpec /\
    MsgsSafeAcceptorPrevTranSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorSpec3 => MsgsSafeAcceptorSpec3'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    KnownMsgsSpec,
                    MsgsSafeAcceptorPrevRefSpec,
                    MsgsSafeAcceptorPrevTranSpec,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2,
                    MsgsSafeAcceptorSpec3
             PROVE  MsgsSafeAcceptorSpec3'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs, NEW m2 \in msgs' \ msgs,
                    m1.acc = A, m2.acc = A,
                    m1.type # "1a", m2.type # "1a",
                    m1.prev = m2.prev
             PROVE  m1 = m2
  <2> USE DEF MsgsSafeAcceptorSpec3
  <2> QED BY UniqueMessageSent DEF SentBy, TypeOK
<1> m1 \in Message
    BY DEF TypeOK
<1> SentBy(A) # {}
    BY DEF SentBy, Send, TypeOK
<1> prev_msg[A] # NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
      BY <1>1 DEF ProposerSendAction, Send1a, Send
<1>2. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m2 = new1b
      BY DEF Send
  <2> acc = A
      BY DEF TypeOK
  <2> prev_msg[A] \in m1.ref
      BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy
  <2> m1 \notin Tran(prev_msg[A])
      BY Tran_ref_acyclic
  <2> m1 \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2, MsgsSafeAcceptorPrevTranSpec, SentBy
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon DEF TypeOK
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> m2 = new2a
      BY DEF Send, TypeOK
  <2> acc = A
      BY DEF Send, SentBy, TypeOK
  <2> prev_msg[A] \in Message
      BY DEF TypeOK
  <2> prev_msg[A] \in m1.ref
      BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy
  <2> m1 \notin Tran(prev_msg[A])
      BY Tran_ref_acyclic
  <2> m1 \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2, MsgsSafeAcceptorPrevTranSpec, SentBy
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
      BY <1>4 DEF Process2a, Send
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSend1b(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send
<1>8. CASE \E acc \in FakeAcceptor : FakeSend2a(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction,
            FakeAcceptorAction

LEMMA MsgsSafeAcceptorPrevRefSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevRefSpec =>
    MsgsSafeAcceptorPrevRefSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2,
                    MsgsSafeAcceptorPrevRefSpec
             PROVE  MsgsSafeAcceptorPrevRefSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW mm \in msgs', mm \notin msgs,
                    mm.acc = A, mm.type # "1a",
                    mm.prev # NoMessage
             PROVE  mm.prev \in mm.ref
    BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy, Send
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF MsgsSafeAcceptorPrevRefSpec
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> mm = new1b
      BY DEF Send, TypeOK
  <2> QED BY DEF SafeAcceptorPrevSpec2, Recv,
                 SentBy, Send, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs :
            Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon DEF TypeOK
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> mm = new2a
      BY DEF Send, TypeOK
  <2> QED BY DEF SafeAcceptorPrevSpec2, Recv, SentBy, Send, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
      BY <1>4 DEF Process2a
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction, FakeAcceptorAction

LEMMA MsgsSafeAcceptorPrevTranSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevTranSpec =>
    MsgsSafeAcceptorPrevTranSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    SafeAcceptorPrevSpec2,
                    MsgsSafeAcceptorPrevTranSpec
             PROVE  MsgsSafeAcceptorPrevTranSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs' \ msgs,
                    m1.acc = A, m1.type # "1a",
                    NEW m2 \in PrevTran(m1), m2 # m1
             PROVE  m2 \in Tran(m1)
    BY Tran_refl DEF MsgsSafeAcceptorPrevTranSpec, SentBy, Send, TypeOK
<1> m1 \in Message
    BY DEF TypeOK
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF MsgsSafeAcceptorPrevTranSpec
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor
      BY DEF Acceptor
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m1 = new1b
      BY DEF Send
  <2> new1b.prev = prev_msg[acc]
      OBVIOUS
  <2> m1.prev # NoMessage /\ m2 \in PrevTran(m1.prev)
      BY PrevTran_eq
  <2> prev_msg[acc] \in SentBy(acc)
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[acc] \in recent_msgs[acc]
      BY DEF Send, SafeAcceptorPrevSpec2
  <2> m1.prev \in Message
        BY DEF SentBy, TypeOK
  <2> QED BY Tran_refl, Tran_trans, Tran_eq
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs :
            Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
  <2> PICK ll \in SUBSET Learner :
      LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                    prev |-> prev_msg[acc],
                    ref |-> recent_msgs[acc] \cup {m1b}] IN
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY Zenon DEF TypeOK
  <2> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1b}]
  <2> m1 = new2a
      BY DEF Send, TypeOK
  <2> new2a.prev = prev_msg[acc]
      OBVIOUS
  <2> m1.prev # NoMessage /\ m2 \in PrevTran(m1.prev)
      BY PrevTran_eq
  <2> prev_msg[acc] \in SentBy(acc)
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[acc] \in recent_msgs[acc]
      BY DEF SafeAcceptorPrevSpec2
  <2> m1.prev \in Message
      BY DEF SentBy, TypeOK
  <2> QED BY Tran_refl, Tran_trans, Tran_eq
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
      BY <1>4 DEF Process2a
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF NextTLA, AcceptorProcessAction, FakeAcceptorAction

LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK, KnownMsgsSpec, MsgsSafeAcceptorPrevTranLinearSpec
    PROVE  CaughtSpec
PROOF BY MessageTypeSpec
      DEF MsgsSafeAcceptorPrevTranLinearSpec, CaughtSpec, Caught, CaughtMsg,
      KnownMsgsSpec, SentBy, TypeOK

LEMMA MsgsSafeAcceptorSpecImpliesCaughtEffSpec ==
    ASSUME TypeOK, KnownMsgsSpec, MsgsSafeAcceptorSpec3
    PROVE  CaughtEffSpec
PROOF BY MessageTypeSpec
      DEF MsgsSafeAcceptorSpec3, CaughtEffSpec, Caught0, CaughtMsg0,
          KnownMsgsSpec, SentBy, TypeOK

LEMMA QuorumIntersection ==
    ASSUME TypeOK,
           NEW a \in Learner, NEW b \in Learner,
           NEW M \in Message,
           NEW Qa \in SUBSET Message, NEW Qb \in SUBSET Message,
           NEW S \in ByzQuorum,
           [lr |-> a, q |-> { mm.acc : mm \in Qa }] \in TrustLive,
           [lr |-> b, q |-> { mm.acc : mm \in Qb }] \in TrustLive,
           ConByQuorum(a, b, M, S)
    PROVE  \E p \in S, ma \in Qa, mb \in Qb :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
PROOF
<1> /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
    /\ S \cap Caught(M) = {}
    BY DEF ConByQuorum
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qa }
                     /\ acc \in { mm.acc : mm \in Qb }
    BY TrustLiveAssumption, LearnerGraphAssumptionValidity, Zenon
<1> QED BY BQAssumption

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW a \in Learner, NEW b \in Learner,
           <<a, b>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  ConByQuorum(a, b, m, SafeAcceptor)
PROOF BY BQAssumption DEF ConByQuorum, Ent, CaughtSpec

-----------------------------------------------------------------------------
HeterogeneousSpec(bal) ==
    \A L0, L1, L2 \in Learner :
        <<L1, L2>> \in Ent =>
        \A V1, V2 \in Value :
        \A B1 \in Ballot :
            ChosenIn(L1, B1, V1) =>
            \A M \in known_msgs[L0] :
                M.type = "2a" /\
                L2 \in M.lrn /\
                B(M, bal) /\
                B1 < bal /\
                V(M, V2) =>
                V1 = V2

-----------------------------------------------------------------------------

THEOREM GeneralBallotInduction ==
    ASSUME NEW P(_),
           \A bal \in Ballot : (\A b \in Ballot : b < bal => P(b)) => P(bal)
    PROVE  \A bal \in Ballot : P(bal)
PROOF
<1> USE DEF Ballot
<1> SUFFICES \A n \in Nat : (\A m \in 0..n - 1 : P(m)) => P(n)
    BY GeneralNatInduction, IsaM("blast")
<1> QED OBVIOUS

LEMMA HeterogeneousLemma ==
    TypeOK /\ KnownMsgsSpec /\ CaughtSpec /\
    MsgsSafeAcceptorPrevTranLinearSpec /\
    MsgsSafeAcceptorPrevTranSpec =>
    \A bal \in Ballot : HeterogeneousSpec(bal)
PROOF
<1> ASSUME TypeOK, KnownMsgsSpec, CaughtSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           MsgsSafeAcceptorPrevTranSpec,
           NEW bal \in Ballot,
           (\A b \in Ballot : b < bal => HeterogeneousSpec(b))
    PROVE  HeterogeneousSpec(bal)
  <2> SUFFICES ASSUME NEW L0 \in Learner,
                      NEW L1 \in Learner, NEW L2 \in Learner,
                      NEW V1 \in Value, NEW V2 \in Value,
                      NEW B1 \in Ballot,
                      NEW M \in known_msgs[L0],
                      <<L1, L2>> \in Ent,
                      ChosenIn(L1, B1, V1),
                      M.type = "2a",
                      L2 \in M.lrn,
                      B(M, bal),
                      B1 < bal,
                      V(M, V2)
               PROVE  V1 = V2
      BY DEF HeterogeneousSpec
  <2>1. M \in msgs /\ KnownRefs(L0, M) /\ WellFormed(M)
      BY DEF KnownMsgsSpec
  <2> M \in Message
      BY <2>1 DEF TypeOK
  <2>3. [lr |-> L2, q |-> q(L2, M)] \in TrustLive
      BY <2>1, IsaM("blast") DEF WellFormed, WellFormed2a
  <2> DEFINE Q2 == { m \in Tran(M) :
                        /\ m.type = "1b"
                        /\ Fresh(L2, m)
                        /\ \A b \in Ballot : B(m, b) <=> B(M, b) }
  <2> Q2 \in SUBSET Message
      BY Tran_Message
  <2>5. q(L2, M) = { mm.acc : mm \in Q2 }
      BY DEF q
  <2> [lr |-> L2, q |-> { mm.acc : mm \in Q2 }] \in TrustLive
      BY <2>5, <2>3
  <2> ConByQuorum(L2, L1, M, SafeAcceptor)
      BY EntConnected, EntanglementSym, Zenon
  <2> ConByQuorum(L1, L2, M, SafeAcceptor)
      BY EntConnected, Zenon
  <2>8. PICK Q1 \in SUBSET Known2a(L1, B1, V1) :
                [lr |-> L1, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
      BY Zenon DEF ChosenIn
  <2> Q1 \in SUBSET msgs
      BY DEF Known2a, KnownMsgsSpec
  <2> Q1 \in SUBSET Message
      BY DEF TypeOK
  <2> [lr |-> L1, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
      BY <2>8
  <2> PICK p \in SafeAcceptor, m1b \in Q2, m2a \in Q1 :
            /\ p \notin Caught(M)
            /\ m1b.acc = p
            /\ m2a.acc = p
    <3> HIDE DEF Q2
    <3> QED BY QuorumIntersection, BQAssumption, Isa
  <2> m2a.type = "2a"
      BY <2>8 DEF Known2a
  <2> L1 \in m2a.lrn
      BY <2>8 DEF Known2a
  <2> m2a \in msgs
      OBVIOUS
  <2> B(m2a, B1)
      BY <2>8 DEF Known2a
  <2> V(m2a, V1)
      BY <2>8 DEF Known2a
  <2> m1b.type = "1b"
      OBVIOUS
  <2> m1b \in known_msgs[L0]
      BY DEF KnownMsgsSpec
  <2> m1b \in msgs
      BY DEF KnownMsgsSpec
  <2> WellFormed(m1b)
      BY DEF KnownMsgsSpec
  <2> B(m1b, bal)
      OBVIOUS
  <2> Fresh(L2, m1b) BY DEF q
  <2>13. \A r \in Tran(m1b) :
            r # m1b /\ r.type # "1a" =>
            \A b1, b2 \in Ballot : B(r, b1) /\ B(m1b, b2) => b1 < b2
         BY WellFormedCondition2, WellFormedCondition3 DEF WellFormed, WellFormed1b
  <2>14. m2a \in Tran(m1b)
    <3> ASSUME m1b \in Tran(m2a) PROVE FALSE
        BY TranBallot DEF Ballot
    <3> QED BY DEF MsgsSafeAcceptorPrevTranLinearSpec, MsgsSafeAcceptorPrevTranSpec, SentBy
  <2>15. CASE ~Buried(L1, m2a, m1b)
    <3> L1 \in Con(L2, m1b)
        BY EntConnected, EntanglementSym, BQAssumption DEF Con
    <3> m2a \in Con2as(L2, m1b)
        BY <2>14, <2>15 DEF Con2as
    <3> \A v \in Value : V(m2a, v) <=> V(m1b, v)
        BY DEF Fresh
    <3> V(m1b, V1)
        BY DEF Fresh
    <3> V(m1b, V2)
        BY V_def, V_func DEF TypeOK
    <3> QED BY V_func
  <2>16. CASE Buried(L1, m2a, m1b)
    <3> DEFINE Q == { m \in Tran(m1b) :
                        \E z \in Tran(m) :
                            /\ z.type = "2a"
                            /\ L1 \in z.lrn
                            /\ \A bx, bz \in Ballot :
                                B(m2a, bx) /\ B(z, bz) => bx < bz
                            /\ \A vx, vz \in Value :
                                V(m2a, vx) /\ V(z, vz) => vx # vz }
    <3> [lr |-> L1, q |-> { m.acc : m \in Q }] \in TrustLive
        BY <2>16 DEF Buried
    <3> { m.acc : m \in Q } \in ByzQuorum
        BY TrustLiveAssumption, Zenon
    <3>3. PICK m0 \in { m.acc : m \in Q } : TRUE
        BY EntaglementTrustLiveNonEmpty, Zenon
    <3> PICK r \in Tran(m1b) :
            /\ r.type = "2a"
            /\ L1 \in r.lrn
            /\ \A b2a, br \in Ballot :
                B(m2a, b2a) /\ B(r, br) => b2a < br
            /\ \A v2a, vr \in Value :
                V(m2a, v2a) /\ V(r, vr) => v2a # vr
        BY <3>3, Tran_trans, BQAssumption
    <3> <<L1, L1>> \in Ent
        BY EntanglementSelf
    <3> r \in known_msgs[L0]
        BY DEF KnownMsgsSpec
    <3> r \in Message
        BY DEF TypeOK
    <3> PICK br \in Ballot : B(r, br)
        BY DEF KnownMsgsSpec
    <3> PICK vr \in Value : V(r, vr)
        BY V_def DEF TypeOK
    <3> B1 < br
        OBVIOUS
    <3> V1 # vr
        OBVIOUS
    <3> br < bal
        BY <2>13
    <3> QED BY DEF HeterogeneousSpec
  <2>17. QED BY <2>15, <2>16
<1> QED BY GeneralBallotInduction, IsaM("blast")

LEMMA ChosenSafeCaseEq ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW BB \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, BB, V1), ChosenIn(L2, BB, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET Known2a(L1, BB, V1) :
        [lr |-> L1, q |-> { m.acc : m \in S1 }] \in TrustLive
    BY DEF ChosenIn, Zenon
<1> DEFINE Q1 == { m.acc : m \in S1 }
<1> Q1 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> PICK S2 \in SUBSET Known2a(L2, BB, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY DEF ChosenIn, Zenon
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2
    BY EntanglementTrustLive
<1>4. PICK m1 \in known_msgs[L1] :
        /\ B(m1, BB)
        /\ V(m1, V1)
      BY DEF ChosenIn, Known2a
<1>5. PICK m2 \in known_msgs[L2] :
        /\ B(m2, BB)
        /\ V(m2, V2)
      BY DEF ChosenIn, Known2a
<1>6. QED BY <1>4, <1>5, V_def, V_func DEF TypeOK

LEMMA ChosenSafeCaseLt ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgsSpec, CaughtSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           MsgsSafeAcceptorPrevTranSpec,
           <<L1, L2>> \in Ent,
           B1 < B2,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET Known2a(L1, B1, V1) :
        [lr |-> L1, q |-> { m.acc : m \in S1 }] \in TrustLive
    BY Zenon DEF ChosenIn
<1> DEFINE Q1 == { m.acc : m \in S1 }
<1> Q1 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> PICK S2 \in SUBSET Known2a(L2, B2, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY Zenon DEF ChosenIn
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> <<L2, L2>> \in Ent
    BY EntanglementSelf, EntanglementSym, Zenon
<1> PICK A \in Q2 : TRUE
    BY EntaglementTrustLiveNonEmpty, Zenon
<1> PICK M \in known_msgs[L2] :
        /\ M.type = "2a"
        /\ L2 \in M.lrn
        /\ B(M, B2)
        /\ V(M, V2)
    BY DEF Known2a
<1> QED BY HeterogeneousLemma DEF HeterogeneousSpec

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgsSpec, CaughtSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           MsgsSafeAcceptorPrevTranSpec,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1>0. CASE B1 < B2 BY <1>0, ChosenSafeCaseLt
<1>1. CASE B2 < B1 BY <1>1, ChosenSafeCaseLt, EntanglementSym
<1>2. CASE B1 = B2 BY <1>2, ChosenSafeCaseEq
<1>3. QED BY <1>0, <1>1, <1>2 DEF Ballot

LEMMA SafetyStep ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec /\ CaughtSpec /\
    MsgsSafeAcceptorPrevTranLinearSpec /\
    MsgsSafeAcceptorPrevTranSpec /\
    DecisionSpec /\
    Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, NextTLA,
               KnownMsgsSpec, CaughtSpec,
               MsgsSafeAcceptorPrevTranSpec,
               MsgsSafeAcceptorPrevTranLinearSpec,
               DecisionSpec,
               Safety,
               NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               <<L1, L2>> \in Ent,
               V1 \in decision'[L1, B1], V2 \in decision'[L2, B2]
        PROVE V1 = V2
    BY DEF Safety
<1>1. CASE \E p \in Proposer : ProposerSendAction(p)
      BY <1>1 DEF ProposerSendAction, Send1a, Safety
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
      BY <1>2 DEF Process1a, Safety
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Safety
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
      BY <1>4 DEF Process2a, Safety
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv, Safety
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, BVal >>
      BY <1>7, Zenon DEF LearnerDecide
  <2> CASE V1 # V2
    <3>1. CASE val # V1 /\ val # V2 BY <3>1 DEF Safety, TypeOK
    <3>2. CASE val = V1
      <4> V2 \in decision[L2, B2] BY <3>2 DEF TypeOK
      <4> ChosenIn(L2, B2, V2) BY DEF DecisionSpec
      <4>2. CASE V1 \in decision[L1, B1] BY <4>2 DEF Safety
      <4>3. CASE V1 \notin decision[L1, B1]
        <5> lrn = L1 /\ bal = B1 BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L1, B1, V1) BY <3>2
        <5> QED BY ChosenSafe, AllProvers
      <4> QED BY <4>2, <4>3
    <3>3. CASE val = V2
      <4> V1 \in decision[L1, B1] BY <3>3 DEF TypeOK
      <4> ChosenIn(L1, B1, V1) BY DEF DecisionSpec
      <4>2. CASE V2 \in decision[L2, B2] BY <4>2 DEF Safety
      <4>3. CASE V2 \notin decision[L2, B2]
        <5> lrn = L2 /\ bal = B2 BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L2, B2, V2) BY <3>3
        <5> QED BY ChosenSafe
      <4> QED BY <4>2, <4>3
    <3> QED BY <3>1, <3>2, <3>3
  <2>10. QED OBVIOUS
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Safety
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
          DEF NextTLA, AcceptorProcessAction, LearnerAction

FullSafetyInvariant ==
    /\ TypeOK
    /\ KnownMsgsSpec
    /\ SafeAcceptorPrevSpec1
    /\ SafeAcceptorPrevSpec2
    /\ MsgsSafeAcceptorPrevTranLinearSpec
    /\ MsgsSafeAcceptorSpec3
    /\ MsgsSafeAcceptorPrevRefSpec
    /\ MsgsSafeAcceptorPrevTranSpec
    /\ DecisionSpec
    /\ Safety

LEMMA TypeOKInit == Init => TypeOK
PROOF BY DEF Init, TypeOK

LEMMA KnownMsgsSpecInit == Init => KnownMsgsSpec
PROOF BY DEF Init, KnownMsgsSpec, Acceptor

LEMMA SafeAcceptorPrevSpec1Init == Init => SafeAcceptorPrevSpec1
PROOF BY DEF Init, SafeAcceptorPrevSpec1, Acceptor, SentBy

LEMMA SafeAcceptorPrevSpec2Init == Init => SafeAcceptorPrevSpec2
PROOF BY DEF Init, SafeAcceptorPrevSpec2, Acceptor

LEMMA MsgsSafeAcceptorSpec1Init == Init => MsgsSafeAcceptorPrevTranLinearSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevTranLinearSpec, SentBy

LEMMA MsgsSafeAcceptorSpec3Init == Init => MsgsSafeAcceptorSpec3
PROOF BY DEF Init, MsgsSafeAcceptorSpec3, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecInit == Init => MsgsSafeAcceptorPrevRefSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevRefSpec, SentBy

LEMMA MsgsSafeAcceptorPrevTranSpecInit == Init => MsgsSafeAcceptorPrevTranSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevTranSpec, SentBy

LEMMA DecisionSpecInit == Init => DecisionSpec
PROOF BY DEF Init, DecisionSpec

LEMMA SafetyInit == Init => Safety
PROOF BY DEF Init, Safety

LEMMA FullSafetyInvariantInit == Init => FullSafetyInvariant
PROOF BY TypeOKInit,
         KnownMsgsSpecInit,
         SafeAcceptorPrevSpec1Init,
         SafeAcceptorPrevSpec2Init,
         MsgsSafeAcceptorSpec1Init,
         MsgsSafeAcceptorSpec3Init,
         MsgsSafeAcceptorPrevRefSpecInit,
         MsgsSafeAcceptorPrevTranSpecInit,
         DecisionSpecInit,
         SafetyInit
      DEF FullSafetyInvariant

LEMMA TypeOKStutter ==
    TypeOK /\ vars = vars' => TypeOK'
PROOF BY DEF TypeOK, vars

LEMMA KnownMsgsSpecStutter ==
    KnownMsgsSpec /\ vars = vars' => KnownMsgsSpec'
PROOF BY Isa DEF KnownMsgsSpec, vars, WellFormed, WellFormed1b, WellFormed2a,
                 SameBallot, q, Fresh, Con, ConByQuorum, Con2as, Buried,
                 V, B, Get1a, SameBallot, ChainRef, KnownRefs,
                 Caught, CaughtMsg

LEMMA SafeAcceptorPrevSpec1Stutter ==
    SafeAcceptorPrevSpec1 /\ vars = vars' => SafeAcceptorPrevSpec1'
PROOF BY DEF SafeAcceptorPrevSpec1, vars, SentBy

LEMMA SafeAcceptorPrevSpec2Stutter ==
    SafeAcceptorPrevSpec2 /\ vars = vars' => SafeAcceptorPrevSpec2'
PROOF BY DEF SafeAcceptorPrevSpec2, vars, SentBy

LEMMA MsgsSafeAcceptorSpec1Stutter ==
    MsgsSafeAcceptorPrevTranLinearSpec /\ vars = vars' => MsgsSafeAcceptorPrevTranLinearSpec'
PROOF BY DEF MsgsSafeAcceptorPrevTranLinearSpec, vars, SentBy

LEMMA MsgsSafeAcceptorSpec3Stutter ==
    MsgsSafeAcceptorSpec3 /\ vars = vars' => MsgsSafeAcceptorSpec3'
PROOF BY DEF MsgsSafeAcceptorSpec3, vars, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecStutter ==
    MsgsSafeAcceptorPrevRefSpec /\ vars = vars' => MsgsSafeAcceptorPrevRefSpec'
PROOF BY DEF MsgsSafeAcceptorPrevRefSpec, vars, SentBy

LEMMA MsgsSafeAcceptorPrevTranSpecStutter ==
    MsgsSafeAcceptorPrevTranSpec /\ vars = vars' => MsgsSafeAcceptorPrevTranSpec'
PROOF BY DEF MsgsSafeAcceptorPrevTranSpec, vars, SentBy

LEMMA DecisionSpecStutter ==
    DecisionSpec /\ vars = vars' => DecisionSpec'
PROOF BY Isa DEF DecisionSpec, vars, ChosenIn, Known2a, B, V, Get1a

LEMMA SafetyStutter ==
    Safety /\ vars = vars' => Safety'
PROOF BY DEF Safety, vars

LEMMA FullSafetyInvariantNext ==
    FullSafetyInvariant /\ [NextTLA]_vars => FullSafetyInvariant'
PROOF
<1> SUFFICES ASSUME FullSafetyInvariant, [NextTLA]_vars PROVE FullSafetyInvariant' OBVIOUS
<1>1. CASE NextTLA
      BY <1>1,
         TypeOKInvariant,
         KnownMsgsSpecInvariant,
         MsgsSafeAcceptorSpecImpliesCaughtSpec,
         SafeAcceptorPrevSpec1Invariant,
         SafeAcceptorPrevSpec2Invariant,
         MsgsSafeAcceptorPrevTranLinearSpecInvariant,
         MsgsSafeAcceptorSpec3Invariant,
         MsgsSafeAcceptorPrevRefSpecInvariant,
         MsgsSafeAcceptorPrevTranSpecInvariant,
         DecisionSpecInvariant,
         SafetyStep
      DEF FullSafetyInvariant
<1>2. CASE vars = vars'
      BY <1>2,
         TypeOKStutter,
         KnownMsgsSpecStutter,
         SafeAcceptorPrevSpec1Stutter,
         SafeAcceptorPrevSpec2Stutter,
         MsgsSafeAcceptorSpec1Stutter,
         MsgsSafeAcceptorSpec3Stutter,
         MsgsSafeAcceptorPrevRefSpecStutter,
         MsgsSafeAcceptorPrevTranSpecStutter,
         DecisionSpecStutter,
         SafetyStutter
      DEF FullSafetyInvariant
<1>3. QED BY <1>1, <1>2

THEOREM SafetyResult == Spec => []Safety
PROOF BY PTL, FullSafetyInvariantInit, FullSafetyInvariantNext, NextDef
      DEF Spec, FullSafetyInvariant

=============================================================================
\* Modification History
\* Last modified Wed May 15 18:43:42 CEST 2024 by karbyshev
\* Created Tue Jun 20 00:28:26 CEST 2023 by karbyshev
