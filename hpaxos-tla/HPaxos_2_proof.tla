-------------------------- MODULE HPaxos_2_proof ----------------------------
EXTENDS HPaxos_2, HMessage_proof, HLearnerGraph_proof,
        Sequences, SequenceTheorems,
        FiniteSets, FiniteSetTheorems,
        WellFoundedInduction, 
        TLAPS

-----------------------------------------------------------------------------
LEMMA CaughtMsgSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg(M) \in SUBSET Message
           /\ \A X \in CaughtMsg(M) : ~Proposal(X)
BY Tran_Message DEF CaughtMsg, Proposal

-----------------------------------------------------------------------------
LEMMA ReplyTypeSpec ==
    ASSUME NEW m \in Message,
           NEW t \in {"1b", "2a", "2b"},
           ReplyType(m, t)
    PROVE  ~TwoB(m)
PROOF BY MessageTypeSpec DEF ReplyType, TwoB

-----------------------------------------------------------------------------
(* Facts about Get1a, B and V relations *)

LEMMA Get1a_TypeOK ==
    ASSUME NEW m \in Message
    PROVE  /\ Get1a(m) \subseteq Message
           /\ \A x \in Get1a(m) : x.bal \in Ballot
PROOF BY Tran_Message, MessageSpec DEF Get1a, OneA

LEMMA Get1a_correct ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m), NEW y \in Get1a(m)
    PROVE  x.bal = y.bal
PROOF BY Tran_Message, MessageSpec DEF Get1a, OneA, Ballot

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
    ASSUME NEW m \in Message, OneA(m)
    PROVE  B(m, m.bal)
PROOF BY MessageSpec, Tran_1a DEF B, Get1a, OneA, Ballot

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

\* TODO remove if not used
LEMMA SameBallot_sym ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           SameBallot(x, y)
    PROVE  SameBallot(y, x)
BY DEF SameBallot

\* TODO remove if not used
LEMMA SameValue_sym ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           SameValue(x, y)
    PROVE  SameValue(y, x)
BY DEF SameValue

LEMMA SameBallotValue ==
    ASSUME BVal \in [Ballot -> Value],
           NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot, B(x, bal),
           SameBallot(x, y)
    PROVE  SameValue(x, y)
PROOF
<1> QED BY V_func, V_def DEF SameBallot, SameValue

LEMMA TranBallot ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           NEW b1 \in Ballot, NEW b2 \in Ballot,
           B(m1, b1), B(m2, b2)
    PROVE  b2 <= b1
PROOF BY Tran_trans DEF B, Get1a

\*    Latest(P) ==
\*        { x \in P :
\*            \A bx \in Ballot :
\*                B(x, bx) =>
\*                \A y \in P, by \in Ballot :
\*                    B(y, by) => by <= bx }

\* TODO

LEMMA LatestSubset ==
    ASSUME NEW P \in SUBSET Message
    PROVE  Latest(P) \in SUBSET P
PROOF BY DEF Latest

\* TODO fix: requires IsFinite(P)
LEMMA LatestNonEmpty ==
    ASSUME NEW P \in SUBSET { m \in Message : WellFormed(m) },
           P # {}
    PROVE  Latest(P) # {}
PROOF
<1> QED

SmallestIndex(seq, P(_), k) ==
    P(seq[k]) /\ \A i \in 1..(k-1) : ~P(seq[i])

LEMMA SmallestIndexExists ==
    ASSUME NEW S, NEW P(_),
           NEW n \in Nat, NEW seq \in [1..n -> S],
           NEW n0 \in 1..n,
           P(seq[n0])
    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)
PROOF
<1> DEFINE A(x) == x \in 0..n - 1 /\ P(seq[x + 1])
<1>1. SUFFICES \E k \in Nat :
                /\ A(k)
                /\ k = 0 \/ \A i \in 0 .. (k - 1) : ~A(i)
  <2> PICK k \in Nat :
            /\ A(k)
            /\ k = 0 \/ \A i \in 0 .. (k - 1) : ~A(i)
      BY <1>1
  <2> WITNESS k + 1 \in 1..n
  <2>1. P(seq[k + 1])
        OBVIOUS
  <2>2. ASSUME NEW i \in 1..k PROVE ~P(seq[i])
    <3> CASE k = 0 OBVIOUS
    <3> CASE k > 0
      <4> i - 1 \in 0..n - 1
          OBVIOUS
      <4> QED OBVIOUS
    <3> QED OBVIOUS
  <2> QED BY <2>1, <2>2 DEF SmallestIndex
<1> n0 - 1 \in Nat
    OBVIOUS
<1> A(n0 - 1)
    OBVIOUS
<1> HIDE DEF A
<1> QED BY <1>1, SmallestNatural, IsaM("blast")

-----------------------------------------------------------------------------
\* Check equivalence of two well-formedness conditions

LEMMA WellFormedCondition1 ==
    ASSUME NEW m \in Message, OneB(m),
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y)
    PROVE  \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m)
PROOF
<1> SUFFICES ASSUME NEW y \in Tran(m), m # y, SameBallot(m, y)
             PROVE  y \in Get1a(m)
    OBVIOUS
<1> OneA(y) OBVIOUS
<1> y \in Message BY Tran_Message
<1> y.bal \in Ballot BY MessageSpec DEF OneA
<1> B(y, y.bal) BY B_1a
<1> SUFFICES ASSUME NEW z \in Tran(m), OneA(z)
             PROVE  z.bal =< y.bal
    BY DEF Get1a, OneA
<1> z \in Message BY Tran_Message
<1> z.bal \in Ballot BY MessageSpec DEF OneA
<1> B(z, z.bal) BY B_1a
<1> QED BY TranBallot DEF SameBallot

\* Equivalence of two well-formedness conditions
LEMMA WellFormedConditionEquiv1 ==
    ASSUME NEW m \in Message, OneB(m)
    PROVE  (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m))
           <=>
           (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y))
PROOF BY WellFormedCondition1 DEF Get1a, OneA

LEMMA WellFormedCondition2 ==
    ASSUME NEW m \in Message, OneB(m),
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y)
    PROVE  \A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
PROOF BY Tran_Message, B_func DEF SameBallot, OneA

LEMMA WellFormedConditionEquiv2 ==
    ASSUME NEW m \in Message, OneB(m)
    PROVE (\A y \in Tran(m) :
            m # y /\
            (\E bm \in Ballot : B(m, bm)) /\
            (\E by \in Ballot : B(y, by)) /\
            SameBallot(m, y) => OneA(y))
          <=>
          (\A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
PROOF BY Tran_Message, B_func DEF SameBallot, OneA

LEMMA WellFormedCondition3 ==
    ASSUME NEW m \in Message, OneB(m),
           \A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
    PROVE  \A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
PROOF BY TranBallot DEF Ballot

LEMMA WellFormedConditionEquiv3 ==
    ASSUME NEW m \in Message, OneB(m)
    PROVE (\A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
          <=>
          (\A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm)
PROOF BY TranBallot DEF Ballot

LEMMA WellFormedCondition111 ==
    ASSUME NEW m \in Message,
           WellFormed(m),
           OneB(m)
    PROVE  \A y \in Tran(m) : m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm

-----------------------------------------------------------------------------
MaxDepthSpec ==
    \A alpha \in Learner: maxDepth(alpha) \in Nat /\ maxDepth(alpha) >= 1

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor -> SUBSET Message]
    /\ prev_msg \in [Acceptor -> Message \cup {NoMessage}]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]
    /\ BVal \in [Ballot -> Value]

-----------------------------------------------------------------------------
SentBy(acc) == { mm \in msgs : ~OneA(mm) /\ mm.acc = acc }

Sent1bBy(acc) == { mm \in msgs : OneB(mm) /\ mm.acc = acc }

\* TODO not used (remove?)
RecentMsgsSpec1 ==
    \A A \in SafeAcceptor :
        \A x \in recent_msgs[A] :
            x.acc = A => x \in SentBy(A)

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

MsgsSafeAcceptorSpec3 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1.prev = m2.prev => m1 = m2

MsgsSafeAcceptorPrevRefSpec ==
    \A A \in SafeAcceptor :
        \A m \in SentBy(A) :
            m.prev # NoMessage => m.prev \in m.refs

\* TODO replace it with the following below
MsgsSafeAcceptorPrevTranSpec ==
    \A A \in SafeAcceptor :
        \A m1 \in SentBy(A) :
            \A m2 \in PrevTran(m1) :
                m2 \in Tran(m1)

KnownMsgsPrevTranSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A m1 \in known_msgs[AL] :
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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> [type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> {}] \in Message
      BY Message_spec, MessageRec_eq0 DEF MessageRec0
  <2> QED BY DEF SendProposal, Send, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> acc \in Acceptor BY DEF Acceptor
  <2> m \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage DEF Process, Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Process, Recv, TypeOK
  <2> recent_msgs' \in [Acceptor -> SUBSET Message]
    <4> PICK ll \in SUBSET Learner,
             t \in {"1b", "2a", "2b"} :
        LET new == [type |-> t,
                    acc  |-> acc,
                    prev |-> prev_msg[acc],
                    refs |-> recent_msgs[acc] \cup {m},
                    lrns |-> ll] IN
        /\ new \in Message
        /\ \/ /\ ReplyType(m, t)
              /\ WellFormed(new)
              /\ Send(new)
              /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
              /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
           \/ /\ ReplyType(m, t)
              /\ ~WellFormed(new)
              /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
           \/ /\ TwoB(m)
              /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
        BY DEF Process
    <4> DEFINE new == [type |-> t,
                       acc  |-> acc,
                       prev |-> prev_msg[acc],
                       refs |-> recent_msgs[acc] \cup {m},
                       lrns |-> ll]
    <4> new \in Message
        OBVIOUS
    <4> recent_msgs[acc] \cup {m} \in SUBSET Message
        BY DEF TypeOK
    <4> QED BY DEF TypeOK
  <2> prev_msg' \in [Acceptor -> Message \cup {NoMessage}]
      BY DEF Process, TypeOK
  <2> decision' \in [Learner \X Ballot -> SUBSET Value]
      BY DEF Process, TypeOK
  <2> BVal' \in [Ballot -> Value]
      BY DEF Process, TypeOK
  <2> QED BY DEF TypeOK
<1>7. CASE \E l \in Learner : LearnerAction(l)
      BY <1>7 DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8, WellFormedMessage
      DEF FakeAcceptorAction, FakeSendControlMessage, Send, TypeOK
<1>9. QED BY <1>1, <1>3, <1>7, <1>8
          DEF NextTLA, SafeAcceptorAction

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> QED BY DEF Process, Send
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage, Send
<1>9. QED BY <1>1, <1>3, <1>6, <1>7, <1>8
          DEF NextTLA, SafeAcceptorAction, LearnerAction

LEMMA Qd_monotone ==
    ASSUME NEW alpha \in Learner,
           NEW m \in Message,
           NEW d \in Nat,
           BVal' = BVal
    PROVE  qd(alpha, m, d) = qd(alpha, m, d)'
PROOF BY Isa DEF V, qd, Fresh000, SameValue, V

LEMMA WellFormed_monotone ==
    ASSUME BVal' = BVal
    PROVE  \A m \in Message : WellFormed(m) <=> WellFormed(m)'
PROOF BY Qd_monotone DEF WellFormed

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
      BY <1>3 DEF Process, Recv, TypeOK, Acceptor
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, Recv, TypeOK, Acceptor
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9 DEF FakeAcceptorAction, FakeSendControlMessage, TypeOK
<1>10. QED BY <1>1, <1>3, <1>7, <1>8, <1>9
           DEF NextTLA, SafeAcceptorAction, LearnerAction

LEMMA Decision_monotone ==
    TypeOK /\ NextTLA =>
    \A LB \in Learner \X Ballot :
        decision[LB] \subseteq decision[LB]'
PROOF
<1> QED

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY KnownMsgMonotone DEF SendProposal, V, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> QED BY KnownMsgMonotone DEF Process, V, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, KnownMsgMonotone DEF LearnerRecv, V, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8, KnownMsgMonotone DEF LearnerDecide, V, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, KnownMsgMonotone
      DEF FakeAcceptorAction, FakeSendControlMessage, V, TypeOK
<1>10. QED BY <1>1, <1>3, <1>7, <1>8, <1>9
          DEF NextTLA, SafeAcceptorAction, LearnerAction

LEMMA RecentMsgsSpec1Invariant ==
    TypeOK /\ RecentMsgsSpec1 /\ NextTLA =>
    RecentMsgsSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, RecentMsgsSpec1, NextTLA,
                    NEW A \in SafeAcceptor,
                    NEW M \in recent_msgs[A]',
                    M.acc = A
             PROVE  M \in SentBy(A)'
    BY DEF RecentMsgsSpec1
<1> TypeOK' BY TypeOKInvariant
<1> SafeAcceptor \in SUBSET Acceptor
    BY DEF Acceptor
<1> A \in Acceptor
    OBVIOUS
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF RecentMsgsSpec1, SendProposal, SentBy, Send, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> m \in Message BY DEF TypeOK
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new == [type |-> t,
                  acc  |-> acc,
                  prev |-> prev_msg[acc],
                  refs |-> recent_msgs[acc] \cup {m},
                  lrns |-> ll] IN
      \/ /\ ReplyType(m, t)
         /\ WellFormed(new)
         /\ Send(new)
         /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
      \/ /\ ReplyType(m, t)
         /\ ~WellFormed(new)
         /\ ~OneA(m)
         /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
         /\ UNCHANGED << msgs >>
      \/ /\ TwoB(m)
         /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
         /\ UNCHANGED << msgs >>
      BY DEF Process
  <2> QED BY MessageTypeSpec DEF RecentMsgsSpec1, ReplyType, Recv, Send, SentBy, OneA, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, msg \in msgs : LearnerRecv(lrn, msg)
      BY <1>7
  <2> QED BY DEF RecentMsgsSpec1, LearnerRecv, SentBy, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF RecentMsgsSpec1, LearnerDecide, SentBy, TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9 DEF RecentMsgsSpec1, FakeAcceptorAction, FakeSendControlMessage, SentBy, Send, TypeOK
<1>10. QED BY <1>1, <1>3, <1>7, <1>8, <1>9
           DEF NextTLA, SafeAcceptorAction, LearnerAction

LEMMA DecisionSpecInvariant ==
    BVal' = BVal /\ TypeOK /\ NextTLA /\
    KnownMsgsSpec /\
    MaxDepthSpec /\ DecisionSpec => DecisionSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA, DecisionSpec,
                    MaxDepthSpec,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    BVal' = BVal,
                    VV \in decision[L, BB]'
             PROVE  ChosenIn(L, BB, VV)'
    BY DEF DecisionSpec
<1> TypeOK' BY TypeOKInvariant
<1> Known2a(L, BB, VV) \subseteq Message
    BY DEF Known2a, KnownMsgsSpec, TypeOK
<1> USE DEF DecisionSpec
<1> USE DEF ChosenIn
<1> USE DEF MaxDepthSpec
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> UNCHANGED decision
      BY DEF SendProposal
  <2> QED BY Qd_monotone, Known2aMonotone
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> UNCHANGED decision
      BY DEF Process
  <2> QED BY Qd_monotone, Known2aMonotone
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, Qd_monotone, Known2aMonotone DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, BVal >>
      BY <1>8 DEF LearnerDecide
  <2> QED BY Qd_monotone, Known2aMonotone DEF TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, Qd_monotone, Known2aMonotone
      DEF FakeAcceptorAction, FakeSendControlMessage
<1>10. QED BY <1>1, <1>3, <1>7, <1>8, <1>9
           DEF NextTLA, SafeAcceptorAction, LearnerAction

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, SentBy, Send, OneA
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> m \in Message BY DEF TypeOK
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
        LET new == [type |-> t,
                    acc |-> acc,
                    prev |-> prev_msg[acc],
                    refs |-> recent_msgs[acc] \cup {m},
                    lrns |-> ll] IN
        /\ new \in Message
        /\ \/ /\ ReplyType(m, t)
              /\ WellFormed(new)
              /\ Send(new)
              /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
           \/ /\ ReplyType(m, t)
              /\ ~WellFormed(new)
              /\ ~OneA(m)
              /\ UNCHANGED << prev_msg, msgs >>
           \/ /\ TwoB(m)
              /\ UNCHANGED << prev_msg, msgs >>
      BY DEF Process
  <2> DEFINE new == [type |-> t,
                     acc |-> acc,
                     prev |-> prev_msg[acc],
                     refs |-> recent_msgs[acc] \cup {m},
                     lrns |-> ll]
  <2> new \in Message
      OBVIOUS
  <2> CASE WellFormed(new) /\ ~TwoB(m)
    <3> prev_msg' = [prev_msg EXCEPT ![acc] = new]
        OBVIOUS
    <3> new \in msgs'
        BY DEF Send
    <3> new.acc = acc
        OBVIOUS
    <3> CASE acc # A
        BY NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
    <3> QED BY NoMessageIsNotAMessage DEF SentBy, Send, OneA, TypeOK
  <2> CASE ~WellFormed(new)
      BY DEF SentBy
  <2> CASE TwoB(m)
      BY MessageTypeSpec, ReplyTypeSpec DEF SentBy
  <2> QED OBVIOUS
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send, SentBy
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, SentBy, Send, OneA
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new == [type |-> t,
                  acc  |-> acc,
                  prev |-> prev_msg[acc],
                  refs |-> recent_msgs[acc] \cup {m},
                  lrns |-> ll] IN
      /\ new \in Message
      /\ \/ /\ ReplyType(m, t)
            /\ WellFormed(new)
            /\ Send(new)
            /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
            /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
         \/ /\ ReplyType(m, t)
            /\ ~WellFormed(new)
            /\ ~OneA(m)
            /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
            /\ UNCHANGED << prev_msg, msgs >>
         \/ /\ TwoB(m)
            /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m}]
            /\ UNCHANGED << prev_msg, msgs >>
      BY DEF Process
  <2> DEFINE new == [type |-> t,
                     acc  |-> acc,
                     prev |-> prev_msg[acc],
                     refs |-> recent_msgs[acc] \cup {m},
                     lrns |-> ll]
  <2> new \in Message
      OBVIOUS
  <2> CASE acc = A
    <3> CASE WellFormed(new) /\ ~TwoB(m)
      <4> msgs' = msgs \cup {new}
          BY DEF Send, OneA
      <4> new # NoMessage
          BY NoMessageIsNotAMessage
      <4> new.prev = prev_msg[A]
          OBVIOUS
      <4> SentBy(A)' = SentBy(A) \cup {new}
          BY DEF Send, SentBy, OneA
      <4> prev_msg[A]' = new
          BY DEF Send, TypeOK
      <4> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in PrevTran(new)
          BY Message_prev_PrevTran DEF SafeAcceptorPrevSpec1
      <4> prev_msg[A]' \in SentBy(A)'
          OBVIOUS
      <4> prev_msg[A]' \in recent_msgs[A]'
          BY DEF TypeOK
      <4> HIDE DEF new
      <4> QED BY PrevTran_trans, PrevTran_refl DEF SafeAcceptorPrevSpec1      
    <3> CASE ~WellFormed(new)
        BY DEF SentBy, TypeOK
    <3> CASE TwoB(m)
        BY MessageTypeSpec, ReplyTypeSpec DEF SentBy, TypeOK
    <3> QED OBVIOUS
  <2> CASE acc # A
      BY DEF SentBy, Send, TypeOK
  <2> QED OBVIOUS
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send, SentBy
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction

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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> USE DEF SendProposal
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
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> known_msgs[AL]' \in SUBSET msgs'
     BY DEF Process, Send, Recv
  <2> KnownRefs(AL, M)'
      BY DEF Process, KnownRefs, Recv
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Process, Recv, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> USE DEF Process
      <4> M = m BY DEF Recv
      <4> AL = acc BY DEF Recv
      <4> M \in Message BY DEF WellFormed
      <4> QED BY Tran_eq, KnownMsgMonotone DEF Recv, KnownRefs
    <3> QED BY DEF Process, Recv
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
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
<1>8. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>8
  <2> USE DEF FakeSendControlMessage
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
<1> QED BY <1>1, <1>3, <1>6, <1>7, <1>8
        DEF NextTLA, SafeAcceptorAction, LearnerRecv,
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
                    ~Proposal(m1),
                    ~Proposal(m2),
                    m1.acc = A, m2.acc = A
             PROVE  m1 \in PrevTran(m2)
    BY UniqueMessageSent, PrevTran_refl
       DEF MsgsSafeAcceptorPrevTranLinearSpec, SentBy, Proposal, OneA, TypeOK
<1> m1 \in SentBy(A)
    BY DEF SentBy, Proposal, OneA
<1> prev_msg[A] # NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1>1. CASE \E p \in Proposer : ProposerAction(p)
      BY <1>1 DEF ProposerAction, SendProposal, Send, Proposal, OneA
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new2a == [type |-> t,
                    acc  |-> acc,
                    prev |-> prev_msg[acc],
                    refs |-> recent_msgs[acc] \cup {msg},
                    lrns |-> ll] IN
      /\ new2a \in Message
      /\ Send(new2a)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
      BY DEF Process, TypeOK
  <2> DEFINE new2a == [type |-> t,
                       acc  |-> acc,
                       prev |-> prev_msg[acc],
                       refs |-> recent_msgs[acc] \cup {msg},
                       lrns |-> ll]
  <2> m2 = new2a BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[A] \in PrevTran(m2)
      BY Message_prev_PrevTran
  <2> QED BY PrevTran_trans DEF SentBy
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSendControlMessage(acc)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction,
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
                    m1.acc = A,
                    m2.acc = A,
                    ~Proposal(m1),
                    ~Proposal(m2),
                    m1.prev = m2.prev
             PROVE  m1 = m2 
    BY UniqueMessageSent
       DEF MsgsSafeAcceptorSpec3, SentBy, OneA, Proposal, TypeOK
<1> m1 \in Message
    BY DEF TypeOK
<1> SentBy(A) # {}
    BY DEF SentBy, Send, Proposal, OneA, TypeOK
<1> prev_msg[A] # NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1>1. CASE \E p \in Proposer : ProposerAction(p)
      BY <1>1 DEF ProposerAction, SendProposal, Proposal, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new == [type |-> t,
                  acc  |-> acc,
                  prev |-> prev_msg[acc],
                  refs |-> recent_msgs[acc] \cup {msg},
                  lrns |-> ll] IN
      /\ Send(new)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
      BY DEF Process, TypeOK
  <2> DEFINE new == [type |-> t,
                     acc  |-> acc,
                     prev |-> prev_msg[acc],
                     refs |-> recent_msgs[acc] \cup {msg},
                     lrns |-> ll]
  <2> m2 = new
      BY DEF Send, TypeOK
  <2> acc = A
      BY DEF Send, SentBy, TypeOK
  <2> prev_msg[A] \in Message
      BY DEF TypeOK
  <2> prev_msg[A] \in m1.refs
      BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy, Proposal, OneA
  <2> m1 \notin Tran(prev_msg[A])
      BY Tran_ref_acyclic
  <2> m1 \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2, MsgsSafeAcceptorPrevTranSpec, SentBy, Proposal, OneA
  <2> QED OBVIOUS
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSendControlMessage(acc)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction,
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
                    mm.acc = A,
                    ~Proposal(mm),
                    mm.prev # NoMessage
             PROVE  mm.prev \in mm.refs
    BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy, Send, Proposal, OneA
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF MsgsSafeAcceptorPrevRefSpec
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, SentBy, Send
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new == [type |-> t,
                  acc  |-> acc,
                  prev |-> prev_msg[acc],
                  refs |-> recent_msgs[acc] \cup {msg},
                  lrns |-> ll] IN
      /\ Send(new)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
      BY DEF Process, TypeOK
  <2> DEFINE new == [type |-> t,
                     acc  |-> acc,
                     prev |-> prev_msg[acc],
                     refs |-> recent_msgs[acc] \cup {msg},
                     lrns |-> ll]
  <2> mm = new
      BY DEF Send, TypeOK
  <2> QED BY DEF SafeAcceptorPrevSpec2, Recv, SentBy, Send, TypeOK
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send, SentBy
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction

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
                    m1.acc = A,
                    ~Proposal(m1),
                    NEW m2 \in PrevTran(m1), m2 # m1
             PROVE  m2 \in Tran(m1)
    BY Tran_refl
       DEF MsgsSafeAcceptorPrevTranSpec, SentBy, Send, Proposal, OneA, TypeOK
<1> m1 \in Message
    BY DEF TypeOK
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF MsgsSafeAcceptorPrevTranSpec
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, SentBy, Send, Proposal
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            Process(acc, msg)
      BY <1>3
  <2> PICK ll \in SUBSET Learner,
           t \in {"1b", "2a", "2b"} :
      LET new == [type |-> t,
                  acc  |-> acc,
                  prev |-> prev_msg[acc],
                  refs |-> recent_msgs[acc] \cup {msg},
                  lrns |-> ll] IN
      /\ Send(new)
      /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
      BY DEF Process, TypeOK
  <2> DEFINE new == [type |-> t,
                     acc  |-> acc,
                     prev |-> prev_msg[acc],
                     refs |-> recent_msgs[acc] \cup {msg},
                     lrns |-> ll]
  <2> m1 = new
      BY DEF Send, TypeOK
  <2> new.prev = prev_msg[acc]
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
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send, SentBy
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction

\* TODO
LEMMA KnownMsgsPrevTranSpecInvariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsPrevTranSpec =>
    KnownMsgsPrevTranSpec'
PROOF
<1> QED

\* TODO
LEMMA VisibleFromOneB ==
    ASSUME NEW x \in Message,
           WellFormed(x),
           OneB(x),
           NEW Bx \in Ballot,
           B(x, Bx),
           NEW y \in Tran(x),
           ~Proposal(y),
           NEW By \in Ballot,
           B(y, By)
    PROVE  By < Bx
PROOF
<1> QED

\* TODO rename Quorum -> LiveQuorum
LEMMA EntQuorumIntersection ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW Qalpha \in SUBSET Message, NEW Qbeta \in SUBSET Message,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive
    PROVE  \E p \in SafeAcceptor, ma \in Qalpha, mb \in Qbeta :
            /\ ma.acc = p
            /\ mb.acc = p
BY TrustLiveAssumption, LearnerGraphAssumptionValidity DEF Ent

LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK, KnownMsgsSpec, MsgsSafeAcceptorSpec3
    PROVE  CaughtSpec
PROOF BY MessageSpec
      DEF MsgsSafeAcceptorSpec3, CaughtSpec, Caught, CaughtMsg,
          KnownMsgsSpec, SentBy, Proposal, OneA, TypeOK

\* TODO check and clean
LEMMA LiveQuorumConIntersection ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           NEW M \in Message,
           NEW Qalpha \in SUBSET Message, NEW Qbeta \in SUBSET Message,
           NEW S \in ByzQuorum,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive,
           ConByQuorum(alpha, beta, M, S)
    PROVE  \E p \in S, ma \in Qalpha, mb \in Qbeta :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
PROOF
<1> /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
    /\ S \cap Caught(M) = {}
    BY DEF ConByQuorum
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qalpha }
                     /\ acc \in { mm.acc : mm \in Qbeta }
    BY TrustLiveAssumption, LearnerGraphAssumptionValidity
<1> QED BY BQAssumption

\* TODO rename Ent -> ""
LEMMA EntLiveQuorumConIntersection ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           NEW M \in Message,
           NEW Qalpha \in SUBSET Tran(M), NEW Qbeta \in SUBSET Tran(M),
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive,
           beta \in Con(alpha, M)
    PROVE  \E p \in Acceptor, ma \in Qalpha, mb \in Qbeta :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
PROOF
<1> PICK S \in ByzQuorum : ConByQuorum(alpha, beta, M, S)
    BY DEF Con
<1> Qalpha \in SUBSET Message
    BY Tran_Message
<1> Qbeta \in SUBSET Message
    BY Tran_Message
<1> PICK p \in S, ma \in Qalpha, mb \in Qbeta :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
    BY LiveQuorumConIntersection
<1> QED BY BQAssumption

LEMMA LiveQuorumConIntersectionBis ==
    ASSUME TypeOK,
           NEW alpha \in Learner, NEW beta \in Learner,
           NEW M \in Message,
           NEW Qalpha \in SUBSET Message, NEW Qbeta \in SUBSET Message,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive,
           beta \in Con(alpha, M)
    PROVE  \E p \in Acceptor, ma \in Qalpha, mb \in Qbeta :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
PROOF
<1> PICK S \in ByzQuorum : ConByQuorum(alpha, beta, M, S)
    BY DEF Con
<1> /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
    /\ S \cap Caught(M) = {}
    BY DEF ConByQuorum
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qalpha }
                     /\ acc \in { mm.acc : mm \in Qbeta }
    BY TrustLiveAssumption, LearnerGraphAssumptionValidity
<1> QED BY BQAssumption

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  ConByQuorum(alpha, beta, m, SafeAcceptor)
PROOF BY BQAssumption DEF ConByQuorum, Ent, CaughtSpec

\*LEMMA ConnectedTrans ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW beta \in Learner,
\*           NEW gamma \in Learner,
\*           NEW m \in Message,
\*           alpha \in Con(beta, m),
\*           beta \in Con(gamma, m)
\*    PROVE  alpha \in Con(gamma, m)
\*PROOF BY LearnerGraphAssumptionTransitivity DEF Con, ConByQuorum

LEMMA ConnectedSym ==
    ASSUME NEW alpha \in Learner,
           NEW beta \in Learner,
           NEW m \in Message,
           alpha \in Con(beta, m)
    PROVE  beta \in Con(alpha, m)
PROOF BY LearnerGraphAssumptionSymmetry DEF Con, ConByQuorum

LEMMA CaughtTran ==
    ASSUME NEW y \in Message,
           NEW x \in Tran(y)
    PROVE  Caught(x) \in SUBSET Caught(y)
PROOF
<1> QED

LEMMA ConTran ==
    ASSUME NEW y \in Message,
           NEW alpha \in Learner,
           NEW x \in Tran(y)
    PROVE  Con(alpha, y) \in SUBSET Con(alpha, x)
PROOF
<1> QED

LEMMA NotCaughtXXX ==
    ASSUME KnownMsgsPrevTranSpec,
           KnownMsgsSpec,
           TypeOK,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW a \in Acceptor,
           NEW M \in known_msgs[AL],
           NEW x \in Tran(M), NEW y \in Tran(M),
           x.acc = a,
           y.acc = a,
           ~Proposal(x),
           ~Proposal(y),
           a \notin Caught(M)
    PROVE  x \in Tran(y) \/ y \in Tran(x)
PROOF
<1> SUFFICES ASSUME x # y PROVE x \in Tran(y) \/ y \in Tran(x)
    BY Tran_refl DEF KnownMsgsSpec, TypeOK
<1> x \in known_msgs[AL] /\ y \in known_msgs[AL]
    BY DEF KnownMsgsSpec
<1> QED BY DEF KnownMsgsPrevTranSpec, Caught, CaughtMsg

-----------------------------------------------------------------------------
ConnectednessSpec(bal) ==
    TRUE


-----------------------------------------------------------------------------
HeterogeneousSpecTry1(bal) ==
    \A L0, L1, L2, L3 \in Learner :
        <<L1, L3>> \in Ent =>
        \A V1, V2 \in Value :
        \A B1 \in Ballot :
            ChosenIn(L1, B1, V1) =>
            \A M \in known_msgs[L0] :
                TwoA(M) /\
                L3 \in M.lrns /\
                B(M, bal) /\
                B1 < bal /\
                \* "least" condition?
                V1 # V2 /\
                V(M, V2) => TRUE
\*                \E X \in known_msgs[L0] :
\*                    TwoA(X) /\
\*                    B(X) >= bal - Z /\
\*                    B(X) >= B1 /\
\*                    size(Con(L1, X)) >= Z /\
\*                    L2 \in X.lrns /\
\*                    Y \in Tran(X) /\
\*                    B(Y) = B1 /\
\*                    depth(L1, Y) = maxDepth(L1) - Z /\
\*                    L1 \notin Con(L3, X)

-----------------------------------------------------------------------------

\*LEMMA XXX ==
\*    ASSUME NEW alpha \in Learner, NEW beta \in Learner, NEW L0 \in Learner,
\*           NEW bal \in Ballot,
\*           NEW val \in Value
\*    PROVE HeterogeneousSpecBase(alpha, beta, L0, bal, bal)
\*PROOF
\*<1> QED

\*HeterogeneousSpecCond(x, alpha, gamma, gamma_prev, bal, V_M, m, B_m, r, s, B_m_prev, r_prev, s_prev) ==
\*        \* auxiliary:
\*        /\ B(m, B_m)
\*        \* cond 1:
\*        /\ (x = 0 => <<alpha, gamma>> \in Ent)
\*        \* cond 2:
\*        /\ bal < B_m
\*        \* cond 3:
\*        /\ (x > 0 => B_m < B_m_prev[x - 1])
\*        \* cond 4:
\*        /\ (x > 0 => m \in Tran(r_prev[x - 1]))
\*        \* cond 5:
\*        /\ (x > 0 => gamma \in Con(alpha, r_prev[x - 1]))
\*        \* cond 6:
\*        /\ (x > 1 => gamma \notin Con(alpha, r_prev[x - 2]))
\*        \* cond 7:
\*        /\ depth(gamma, m) = 1
\*        \* cond 8:
\*        /\ r \in q(gamma, m)
\*        \* cond 9:
\*        /\ s \in Tran(r)
\*        \* cond 10:
\*        /\ (x > 0 => s \in Tran(s_prev[x - 1]))
\*        \* cond 11:
\*        /\ r.acc = s.acc
\*        \* cond 12:
\*        /\ depth(alpha, s) = maxDepth(alpha) - x
\*        \* cond 13:
\*        /\ B(s, bal)
\*        \* cond 14:
\*        /\ V(m, V_M)

\*HeterogeneousSpecBase(alpha, beta, L0, bal, val) ==
\*        <<alpha, beta>> \in Ent /\
\*        ChosenIn(alpha, bal, val) =>
\*        \A M \in known_msgs[L0], B_M \in Ballot, V_M \in Value :
\*            B(M, B_M) /\
\*            bal < B_M /\
\*            V(M, V_M) =>
\*            \E m_0 \in Tran(M) :
\*            \E B_m_0 \in Ballot:
\*            \E r_0, s_0 \in Tran(M) :
\*            \E gamma_0 \in Learner :
\*                /\ HeterogeneousSpecCond(0, alpha, gamma_0, {}, bal, V_M, m_0, B_m_0, r_0, s_0, {}, {}, {})
\*                /\ \A m1 \in Tran(M), B_m1 \in Ballot, r1 \in Tran(M), s1 \in Tran(M), gamma1 \in Learner:
\*                    B(m1, B_m1) /\ HeterogeneousSpecCond(0, alpha, gamma1, {}, bal, V_M, m1, B_m1, r1, s1, {}, {}, {}) =>
\*                    B_m_0 <= B_m1

\* TODO RENAME
Whatever == [m : Message, B_m : Ballot, r : Message, s : Message, gamma : Learner]

LEMMA WhateverSpec ==
    ASSUME NEW w \in Whatever
    PROVE  /\ w.m \in Message
           /\ w.B_m \in Ballot
           /\ w.r \in Message
           /\ w.s \in Message
           /\ w.gamma \in Learner
PROOF BY DEF Whatever

WhateverOrder == { ww \in Whatever \X Whatever : ww[1].B_m < ww[2].B_m }

LEMMA WhateverOrderWellFounded ==
    IsWellFoundedOn(WhateverOrder, Whatever)
PROOF
<1> SUFFICES ASSUME NEW f \in [Nat -> Whatever],
                    \A n \in Nat : <<f[n + 1], f[n]>> \in WhateverOrder
             PROVE FALSE
    BY DEF IsWellFoundedOn
<1> DEFINE g[n \in Nat] == f[n].B_m
<1> ASSUME NEW n \in Nat PROVE g[n] \in Nat
    BY DEF Whatever, Ballot
<1> g \in [Nat -> Nat] OBVIOUS
<1> ASSUME NEW n \in Nat
    PROVE  <<g[n + 1], g[n]>> \in OpToRel(<, Nat)
    BY DEF WhateverOrder, OpToRel
<1> QED BY NatLessThanWellFounded DEF IsWellFoundedOn

LEMMA WhateverMin ==
    ASSUME NEW T \in SUBSET Whatever, T # {}
    PROVE  \E w \in T : \A z \in T : w.B_m =< z.B_m
PROOF
<1> ASSUME NEW x \in T, NEW y \in T PROVE x.B_m < y.B_m <=> <<x, y>> \in WhateverOrder
    BY DEF WhateverOrder
<1> PICK w0 \in T : \A z \in T : ~(z.B_m < w0.B_m)
    BY WFMin, WhateverOrderWellFounded
<1> QED BY WhateverSpec DEF Ballot

\* seq \in Seq(Whatever)
HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x) ==
    LET m == seq[x].m
        B_m == seq[x].B_m
        r == seq[x].r
        s == seq[x].s
        gamma == seq[x].gamma
    IN
        \* auxiliary:
        /\ B(m, B_m)
        \* cond 1:
        /\ x = 1 => <<alpha, gamma>> \in Ent
        \* cond 2:
        /\ bal < B_m
        \* cond 3:
        /\ x > 1 => \A i \in 1..(x - 1) : B_m < seq[i].B_m
        \* cond 4:
        /\ \A i \in 1..(x - 1) : m \in Tran(seq[i].r)
\*        /\ x > 1 => m \in Tran(seq[x - 1].r)
        \* cond 5:
        /\ x > 1 => gamma \in Con(alpha, seq[x - 1].r)
        \* cond 6:
        /\ x > 2 => gamma \notin Con(alpha, seq[x - 2].r)
        \* cond 7:
        /\ gamma \in m.lrns
        \* cond 8:
        /\ r \in qd(gamma, m, 1)
\*        /\ r \in q(gamma, m)
        \* cond 9:
        /\ s \in Tran(r)
        \* cond 10:
        /\ x > 1 => s \in Tran(seq[x - 1].s)
        \* cond 11:
        /\ r.acc = s.acc
        \* cond 12:
\*        /\ depth(alpha, s) = maxDepth(alpha) - x
        /\ x =< maxDepth(alpha) =>
            [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, s, maxDepth(alpha) - x + 1) }] \in TrustLive
        \* cond 13:
        /\ B(s, bal)
        \* cond 14:
        /\ V(m, V_M)
        \* cond 15:
        /\ x = 1 => m \in Tran(M)

HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x) ==
    /\ HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
    /\ \A z \in Whatever:
        LET seq1 == [seq EXCEPT ![x] = z] IN
        HeterogeneousSpecCond(alpha, bal, M, V_M, seq1, x) =>
        seq[x].B_m <= seq1[x].B_m

LEMMA HeterogeneousSpecCondCongr ==
    ASSUME NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           NEW m \in Message,
           NEW k \in Nat,
           NEW seq1 \in Seq(Whatever),
           NEW seq2 \in Seq(Whatever),
           \A i \in 1..k : seq1[i] = seq2[i]
    PROVE  \A j \in 1..k :
            HeterogeneousSpecCond(alpha, bal, m, val, seq1, j) =>
            HeterogeneousSpecCond(alpha, bal, m, val, seq2, j)
PROOF
<1> SUFFICES ASSUME NEW j \in 1..k,
                    HeterogeneousSpecCond(alpha, bal, m, val, seq1, j)
             PROVE  HeterogeneousSpecCond(alpha, bal, m, val, seq2, j)
    OBVIOUS
<1> j \in Nat
    OBVIOUS
<1>12. j =< maxDepth(alpha) =>
        [lr |-> alpha,
         q |-> {z.acc : z \in qd(alpha, seq2[j].s, maxDepth(alpha) - j + 1)}]
        \in TrustLive
      BY DEF HeterogeneousSpecCond
<1> QED BY <1>12 DEF HeterogeneousSpecCond

LEMMA HeterogeneousSpecCondMinCongr ==
    ASSUME NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW m \in Message,
           NEW val \in Value,
           NEW k \in Nat,
           NEW seq1 \in Seq(Whatever),
           NEW seq2 \in Seq(Whatever),
           k =< Len(seq1),
           k =< Len(seq2),
           \A i \in 1..k : seq1[i] = seq2[i]
    PROVE  \A j \in 1..k :
            HeterogeneousSpecCondMin(alpha, bal, m, val, seq1, j) =>
            HeterogeneousSpecCondMin(alpha, bal, m, val, seq2, j)
PROOF
<1> SUFFICES ASSUME NEW j \in 1..k,
                    HeterogeneousSpecCondMin(alpha, bal, m, val, seq1, j)
             PROVE  HeterogeneousSpecCondMin(alpha, bal, m, val, seq2, j)
    OBVIOUS
<1> HeterogeneousSpecCond(alpha, bal, m, val, seq2, j)
    BY HeterogeneousSpecCondCongr DEF HeterogeneousSpecCondMin
<1> SUFFICES ASSUME NEW z \in Whatever,
                        HeterogeneousSpecCond(alpha, bal, m, val, [seq2 EXCEPT ![j] = z], j)
             PROVE  seq2[j].B_m =< [seq2 EXCEPT ![j] = z][j].B_m
    BY DEF HeterogeneousSpecCondMin
<1> DEFINE seq2_1 == [seq2 EXCEPT ![j] = z]
<1> seq2_1 \in Seq(Whatever)
    OBVIOUS
<1> DEFINE seq1_1 == [seq1 EXCEPT ![j] = z]
<1> seq1_1 \in Seq(Whatever)
    OBVIOUS
<1> \A i \in 1..k : seq1_1[i] = seq2_1[i]
    OBVIOUS
<1> QED BY HeterogeneousSpecCondCongr DEF HeterogeneousSpecCondMin

\*LEMMA TEST ==
\*    ASSUME NEW S \in SUBSET Nat,
\*           S # {},
\*           NEW foo \in Nat,
\*           foo = (CHOOSE x \in S : TRUE)
\*    PROVE  foo \in S
\*\*        (\lambda x. x \in S) foo
\*OBVIOUS
\*
\*LEMMA TEST2 ==
\*    ASSUME NEW P(_),
\*           NEW N \in Nat,
\*           NEW S \in SUBSET 1..N,
\*           S # {},
\*           NEW foo \in Nat,
\*           \E bar \in S : P(bar),
\*           foo = CHOOSE x \in {0} \cup S : P(x),
\*           foo > 0
\*    PROVE  foo \in S
\*OBVIOUS

LEMMA NatFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Nat,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)
PROOF
<1> DEFINE P(X) ==
            X \in SUBSET Nat /\ X # {} => \E max \in X : IsMax(max, X)
<1> SUFFICES ASSUME NEW S, IsFiniteSet(S) PROVE P(S)
    OBVIOUS
<1>0. P({}) OBVIOUS
<1>1. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
    BY <1>1 DEF IsMax
<1> HIDE DEF P
<1>3. QED BY <1>0, <1>1, FS_Induction, IsaM("blast")

LEMMA MaxUnique ==
    ASSUME NEW A \in SUBSET Nat,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y
PROOF
<1> QED BY DEF IsMax

\* TODO rename
LEMMA PPP ==
    ASSUME NEW alpha \in Learner,
           NEW m \in Message
    PROVE LET S == {0} \cup depthIdx(alpha, m) IN \E d \in S : IsMax(d, S)
PROOF
<1> depthIdx(alpha, m) \in SUBSET Nat
    BY DEF depthIdx
<1> depthIdx(alpha, m) \in SUBSET 0..N_L
    BY DEF depthIdx
<1> IsFiniteSet(0..N_L)
    BY FS_Interval, LearnerGraphSize
<1> IsFiniteSet(depthIdx(alpha, m))
    BY FS_Subset
<1> IsFiniteSet({0} \cup depthIdx(alpha, m))
    BY FS_AddElement
<1> QED BY NatFiniteSetMaxExists

LEMMA KnownDepthPlusOne ==
    ASSUME NEW LA \in Learner \cup SafeAcceptor,
           NEW alpha \in Learner,
           NEW M \in known_msgs[LA],
           NEW k \in Nat,
           k + 1 <= N_L,
           depth(alpha, M) = k + 1,
           \* TODO
\*           \A l \in Learner, x \in Message : depthIdx(l, x) \in SUBSET 1..N_L,
           KnownMsgsSpec,
           TypeOK
    PROVE  \E X \in Tran(M) :
            /\ depth(alpha, X) = k
            /\ SameBallot(X, M)
PROOF
<1> M \in Message
    BY DEF KnownMsgsSpec, TypeOK
\*<1> PICK d0 \in {0} \cup depthIdx(alpha, M) : IsMax(d0, {0} \cup depthIdx(alpha, M))
\*    BY PPP
\*<1> depth(alpha, M) = d0
\*    BY MaxUnique DEF depth, Max
<1> k + 1 \in depthIdx(alpha, M)
    BY PPP, MaxUnique DEF depth, Max
<1> [lr |-> alpha, q |-> {m.acc : m \in qd(alpha, M, k + 1)}] \in TrustLive
    BY DEF depthIdx


\*qd(alpha, x, d) ==
\*        LET helper[i \in Nat] ==
\*            IF i = 0 THEN [y \in Message |-> {}]
\*            ELSE
\*                (IF i = 1 THEN
\*                    [y \in Tran(x) |->
\*                        { m \in Tran(y) :
\*                            /\ SameBallot(m, y)
\*                            /\ OneB(m)
\*                            /\ Fresh000(alpha, m) }
\*                    ]
\*                ELSE [y \in Tran(x) |->
\*                    { m \in Tran(y) :
\*                        /\ SameBallot(m, y)
\*                        /\ [lr |-> alpha, q |-> { z.acc : z \in helper[i - 1][y] }] \in TrustLive }]
\*                )
\*        IN helper[d][x]

\*    depthIdx(alpha, x) ==
\*        {d \in 1..N_L : [lr |-> alpha, q |-> {m.acc : m \in qd(alpha, x, d)}] \in TrustLive }
\*    
\*    depth(alpha, x) ==
\*        Max({0} \cup depthIdx(alpha, x))
\*  <2> 
\*    BY DEF Max, depth, KnownMsgsSpec, TypeOK
<1> QED BY DEF TypeOK

\* TODO depends on KnownDepthPlusOne
LEMMA KnownDepthGtOneAux ==
    ASSUME NEW LA \in Learner \cup SafeAcceptor,
           NEW alpha \in Learner,
           KnownMsgsSpec,
           TypeOK
    PROVE  \A n \in Nat : \A M \in known_msgs[LA] :
             n = depth(alpha, M) /\ n >= 1 =>
             \E X \in Tran(M) :
                /\ depth(alpha, X) = 1
                /\ SameBallot(X, M)
PROOF
<1> DEFINE P(n) == \A M \in known_msgs[LA] :
             n = depth(alpha, M) /\ n >= 1 =>
             \E X \in Tran(M) :
                /\ depth(alpha, X) = 1
                /\ SameBallot(X, M)
<1> SUFFICES ASSUME NEW n \in Nat PROVE P(n) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME NEW M \in known_msgs[LA],
                      k + 1 = depth(alpha, M)
               PROVE \E X \in Tran(M) :
                        /\ depth(alpha, X) = 1
                        /\ SameBallot(X, M)
      OBVIOUS
  <2> CASE k = 0
      BY Tran_refl DEF KnownMsgsSpec, TypeOK, SameBallot
  <2> CASE k > 0
    <3> PICK X_1 \in Tran(M) :
            /\ depth(alpha, X_1) = k
            /\ SameBallot(X_1, M)
        BY KnownDepthPlusOne DEF KnownMsgsSpec, TypeOK
    <3> QED BY <1>1, Tran_trans DEF KnownMsgsSpec, TypeOK, SameBallot
  <2> QED OBVIOUS
<1> HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA KnownDepthGtOne ==
    ASSUME NEW LA \in Learner \cup SafeAcceptor,
           NEW alpha \in Learner,
           NEW M \in known_msgs[LA],
           depth(alpha, M) >= 1
    PROVE  \E X \in Tran(M) : depth(alpha, X) = 1
PROOF
<1> QED

\*LEMMA TEST3 ==
\*    [x \in Nat |-> 1] \in [Nat -> Nat]
\*OBVIOUS
\*
\*LEMMA TEST4 ==
\*    [x \in Nat |-> [RRR |-> 42]] \in [Nat -> [RRR : Nat]]
\*OBVIOUS
\*
\*LEMMA TEST5 ==
\*    [x \in 0..0 |-> [RRR |-> 42]] \in [{0} -> [RRR : Nat]]
\*OBVIOUS
\*
\*LEMMA TEST6 ==
\*    [x \in 0..0 |-> [RRR |-> 42]] \in [0..0 -> [RRR : Nat]]
\*OBVIOUS
\*
\*LEMMA TEST7 ==
\*    [x \in 0..0 |-> [RRR |-> 42]] \in [Nat -> [RRR : Nat]]
\*OBVIOUS

\* TODO
LEMMA QuorumZero ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  qd(alpha, x, 0) = {}
PROOF BY \*NatInductiveDef
<1> QED

\* TODO useful lemma
LEMMA QuorumProperty1 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  \A y \in qd(alpha, x, d) :
            /\ y \in Tran(x)
            /\ ~Proposal(y)
PROOF
<1> QED

\* TODO join with Property1
LEMMA QuorumProperty2 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW bal \in Ballot,
           B(x, bal),
           NEW d \in Nat
    PROVE  \A m \in qd(alpha, x, d) :
                /\ B(m, bal)
                /\ d = 1 => OneB(m) /\ Fresh000(alpha, m)
\*            /\ qd(alpha, x, 1) \in SUBSET { mm \in Tran(x) : Fresh000(alpha, mm) }
PROOF
<1> DEFINE P(n) ==
            /\ \A m \in qd(alpha, x, n) :
                /\ ~OneA(m)
                /\ B(m, bal)
                /\ d = 1 => OneB(m) /\ Fresh000(alpha, m)
<1> SUFFICES \A n \in Nat : P(n)
    OBVIOUS
<1>0. P(0)
  <2> QED BY DEF qd
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
<1> HIDE DEF P
<1> QED BY <1>0, <1>1, NatInduction, Isa
\*<1> QED \*BY Tran_trans, Tran_Message DEF qd

LEMMA QuorumProperty3 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW x1 \in Message,
           NEW bal \in Ballot,
           B(x, bal),
           NEW d \in Nat, 0 < d,
           NEW d1 \in Nat, d < d1,
           x \in qd(alpha, x1, d1)
    PROVE  [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, x, d) }] \in TrustLive
OBVIOUS

\*LEMMA WTF0 == FALSE
\*PROOF
\*<1> DEFINE seq == [x \in 1..1 |-> 42]
\*<1> seq \in Seq(Nat) BY SeqDef
\*<1> QED OBVIOUS
\*
\*LEMMA WTF ==
\*    ASSUME NEW N \in Nat,
\*           NEW seq \in [1..N -> Nat]
\*    PROVE  FALSE
\*PROOF
\*<1> seq \in Seq(Nat) BY SeqDef
\*<1> QED OBVIOUS

LEMMA INDUCTION_SCHEME ==
    ASSUME NEW P(_),
           P(0),
           \A k \in Nat : k > 0 /\ P(k - 1) => P(k)
    PROVE  \A n \in Nat : P(n)
PROOF
<1> DEFINE Q(x) == x > 0 => P(x - 1)
<1> SUFFICES \A n \in Nat : Q(n)
    OBVIOUS
<1>0. Q(0)
    OBVIOUS
<1>1. ASSUME NEW m \in Nat, Q(m) PROVE Q(m + 1)
      BY <1>1
<1> HIDE DEF Q
<1> QED BY <1>0, <1>1, NatInduction, Isa

LEMMA QdEq0 ==
    ASSUME NEW alpha \in Learner,
           NEW y \in Message,
           NEW d \in Nat,
           ~TwoA(y)
    PROVE  qd(alpha, y, d) = {}
PROOF
<1> QED

LEMMA QdEq1 ==
    ASSUME NEW alpha \in Learner,
           NEW y \in Message,
           TwoA(y)
    PROVE  qd(alpha, y, 1) = { m \in Tran(y) :
                            /\ SameBallot(m, y)
                            /\ OneB(m)
                            /\ Fresh000(alpha, m) }
PROOF
<1> QED

LEMMA YYY ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner, NEW L0 \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           <<alpha, beta>> \in Ent,
           ChosenIn(alpha, bal, val),
           NEW M \in known_msgs[L0],
           NEW B_M \in Ballot,
           NEW V_M \in Value,
           bal < B_M,
           B(M, B_M),
           V(M, V_M),
           beta \in M.lrns,
           \* TODO
           MaxDepthSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           KnownMsgsPrevTranSpec,
           KnownMsgsSpec,
           TypeOK
    PROVE  \A i \in 0..maxDepth(alpha) :
            \E seq \in [1 .. i + 1 -> Whatever] :
                \A x \in 1 .. i + 1 :
                    HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x)
PROOF
<1> DEFINE P(n) ==
            n \in 0 .. maxDepth(alpha) =>
            \E seq \in [1 .. n + 1 -> Whatever] :
                \A x \in 1 .. n + 1:
                    HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x)
<1> SUFFICES ASSUME NEW n \in Nat PROVE P(n)
    OBVIOUS
<1> M \in Message
    BY DEF KnownMsgsSpec, TypeOK
<1> WellFormed(M)
    BY DEF KnownMsgsSpec
<1> maxDepth(alpha) \in Nat
    BY DEF MaxDepthSpec

\***** BASE CASE
<1>0. P(0)
  <2> DEFINE S ==
        { w \in Whatever :
            HeterogeneousSpecCond(alpha, bal, M, V_M, [x \in 1..1 |-> w], 1) }
  <2> S # {}
\*    ChosenIn(alpha, b, v) ==
\*        \E S \in SUBSET Known2a(alpha, b, v) :
\*            /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
\*            /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive
    <3>21. PICK Q1 \in SUBSET Known2a(alpha, bal, val) :
            /\ \A x \in Q1 :
                [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
            /\ [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
        BY DEF ChosenIn
    <3> Q1 \in SUBSET msgs
        BY DEF Known2a, KnownMsgsSpec
    <3> Q1 \in SUBSET Message
        BY DEF TypeOK
    <3> [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
        BY <3>21
    <3> \A x \in Q1 :
            [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
        BY <3>21
\*        From WellFormedness we have
\*                /\ m.lrns = { alpha \in Learner : [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, 1) }] \in TrustLive }
    <3>22. M.lrns = { l \in Learner : [lr |-> l, q |-> { mm.acc : mm \in qd(l, M, 1) }] \in TrustLive }
        BY DEF WellFormed
    <3> DEFINE Q2 == qd(beta, M, 1)
    <3> [lr |-> beta, q |-> { mm.acc : mm \in Q2 }] \in TrustLive
        BY <3>22
    <3> Q2 \in SUBSET Tran(M)
        BY QuorumProperty1
    <3> Q2 \in SUBSET Message
        BY Tran_Message
    <3> Q2 \in SUBSET known_msgs[L0]
        BY DEF KnownMsgsSpec
    <3> PICK p \in SafeAcceptor, ma \in Q1, mb \in Q2 :
            /\ ma.acc = p
            /\ mb.acc = p
      <4> HIDE DEF Q2
      <4> QED BY EntQuorumIntersection
    <3> B(ma, bal)
        BY DEF Known2a
    <3> B(mb, B_M)
        BY QuorumProperty2
    <3> ma \in known_msgs[alpha]
        BY DEF Known2a
    <3> mb \in known_msgs[L0]
        OBVIOUS
    <3> ma \in msgs
        BY DEF KnownMsgsSpec
    <3> mb \in msgs
        BY DEF KnownMsgsSpec
    <3> ~OneA(ma)
         BY MessageTypeSpec DEF Known2a
    <3> ~OneA(mb)
\*        BY QuorumProperty2 \* TODO fix
    <3> ma \in Tran(mb)
      <4> ma \in Tran(mb) \/ mb \in Tran(ma)
          BY DEF MsgsSafeAcceptorPrevTranLinearSpec, KnownMsgsPrevTranSpec, SentBy
      <4> QED BY TranBallot DEF Ballot
    <3> DEFINE w0 == [m |-> M, B_m |-> B_M, r |-> mb, s |-> ma, gamma |-> beta]
    <3> w0 \in Whatever
        BY DEF Whatever
    <3> w0.B_m \in Ballot
        OBVIOUS
    <3> SUFFICES HeterogeneousSpecCond(alpha, bal, M, V_M, [x \in 1..1 |-> w0], 1)
        OBVIOUS
    <3> QED BY Tran_refl DEF HeterogeneousSpecCond, MaxDepthSpec
  <2> PICK w0 \in S : \A z \in S : w0.B_m =< z.B_m
      BY WhateverMin
  <2> HeterogeneousSpecCondMin(alpha, bal, M, V_M, [x \in 1..1 |-> w0], 1)
      BY WhateverSpec DEF HeterogeneousSpecCondMin
  <2> SUFFICES \E seq \in [1..1 -> Whatever] :
                \A x \in 1..1 : HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x)
      OBVIOUS
  <2> QED OBVIOUS

\***** INDUCTION STEP
<1>1. \A k \in Nat : k > 0 /\ P(k - 1) => P(k)
  <2>0. SUFFICES ASSUME NEW k \in Nat, k > 0, P(k - 1) PROVE P(k)
      OBVIOUS
  <2> SUFFICES ASSUME k \in 0..maxDepth(alpha), P(k - 1) PROVE P(k)
        BY <2>0
  <2> k > 0
      BY <2>0
  <2> (k - 1) + 1 = k
      OBVIOUS
  <2> (k + 1) - 1 = k
      OBVIOUS
  <2> PICK seq \in [1 .. k -> Whatever]:
            \A x \in 1 .. k:
                HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x)
      OBVIOUS
  <2> seq \in Seq(Whatever)
      BY SeqDef
  <2> DEFINE S ==
        { w \in Whatever : HeterogeneousSpecCond(alpha, bal, M, V_M, Append(seq, w), k + 1) }
  <2> S # {}
    <3> \A x \in 1 .. k : HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
        BY DEF HeterogeneousSpecCondMin
    <3> seq[k] \in Whatever
        OBVIOUS
    <3> \A x \in 1..k :
         /\ seq[x].m \in Message
         /\ seq[x].B_m \in Ballot
         /\ seq[x].r \in Message
         /\ seq[x].s \in Message
         /\ seq[x].gamma \in Learner
        BY WhateverSpec
    <3> \A x \in 1..k : B(seq[x].m, seq[x].B_m)
        BY DEF HeterogeneousSpecCond
    \* BY IH, cond 8, we have
    <3> \A x \in 1..k :
            /\ OneB(seq[x].r)
            /\ B(seq[x].r, seq[x].B_m)
            /\ Fresh000(seq[x].gamma, seq[x].r)
        BY QuorumProperty2 DEF HeterogeneousSpecCond
    <3> \A x \in 1..k :
            /\ seq[x].m \in Tran(M)
            /\ seq[x].r \in Tran(M)
            /\ seq[x].s \in Tran(M)
    \* From the previous, we conclude
    <3> \A x \in 1..k : WellFormed(seq[x].r)
    <3> \A x \in 1..k : V(seq[x].m, V_M)
        BY DEF HeterogeneousSpecCond
    <3> V(seq[k].m, V_M)
        OBVIOUS
    <3> B(seq[k].s, bal)
        BY DEF HeterogeneousSpecCond
    <3> V(seq[k].s, val)
        \* we have that s is of ballot "bal", which is a solution ballot for the value "val"
        \* BY SameBallotValue DEF ChosenIn, HeterogeneousSpecCond, SameValue, SameBallot
    <3> seq[k].r \in known_msgs[L0]
    <3> V(seq[k].r, V_M)
        \* r is from quorum of m, therefore r is of the same ballot as m, therefore the value of r equals that of m (which is V_M)
\*        BY SameBallotValue, QuorumProperties DEF HeterogeneousSpecCond
    \* goal: to show V(s_k) # V(r_k)
    <3> seq[k].s \in Tran(seq[k].r)
        BY DEF HeterogeneousSpecCond
    <3> alpha \in seq[k].s.lrns
\*    <3> val # V(r)
    <3> \A i \in 1..k : seq[i].r \in Tran(seq[i].m)
      <4> SUFFICES ASSUME NEW i \in 1..k PROVE seq[i].r \in Tran(seq[i].m)
          OBVIOUS
      <4> seq[i].r \in qd(seq[i].gamma, seq[i].m, 1)
          BY DEF HeterogeneousSpecCond
      <4> qd(seq[i].gamma, seq[i].m, 1) \in SUBSET Tran(seq[i].m)
          BY QuorumProperty1
      <4> QED OBVIOUS
    \* By definition of fresh'ness
    <3>10. {mm \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, mm)} # {}
       \* <4> \* gamma is connected to alpha as of r :   BY ConTran
       <4> CASE k = 1
          \* This follows from Ent(alpha, seq[0].gamma)
          <5> QED
       <4> CASE k > 1
         <5> seq[k - 1].r \in Message
             BY WhateverSpec
\*         <5> k - 1 \in Nat
\*             BY <4>1
       \* We have: m_k \in Tran(r_{k-1}) and r_k \in Tran(m_k) from QuorumProperties and (8)
       \* Hence: r_k \in Tran(r_{k-1})
       \* Therefore: Con(alpha, r_{k-1}) \in SUBSET Con(alpha, r_k) BY ConTran
       \* Since we have by (5) gamma_{k} \in Con(alpha, r_{k-1}), conclude the goal
         <5> seq[k].m \in Tran(seq[k - 1].r)
             BY DEF HeterogeneousSpecCond
         <5> seq[k].r \in Tran(seq[k - 1].r)
             BY Tran_trans
         <5> seq[k].gamma \in Con(alpha, seq[k - 1].r)
             BY DEF HeterogeneousSpecCond
         <5> seq[k].gamma \in Con(alpha, seq[k].r)
             BY ConTran
       \* we conclude that ..
         <5> alpha \in Con(seq[k].gamma, seq[k].r)
             BY ConnectedSym
         <5> QED BY DEF D
      <4> QED OBVIOUS

\*KnownMsgsSpec ==
\*    \A AL \in SafeAcceptor \cup Learner :
\*        /\ known_msgs[AL] \in SUBSET msgs
\*        /\ \A M \in known_msgs[AL] :
\*            /\ KnownRefs(AL, M)
\*            /\ WellFormed(M)
\*            /\ Tran(M) \in SUBSET known_msgs[AL]
\*            /\ \E b \in Ballot : B(M, b)

    <3>11. \A x \in {mm \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, mm)} : WellFormed(x)
           BY DEF KnownMsgsSpec
    <3>12. {mm \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, mm)} \in SUBSET Message
           BY DEF KnownMsgsSpec, TypeOK
    <3>13. Latest({mm \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, mm)}) # {}
          BY <3>10, <3>11, <3>12, LatestNonEmpty
    \* Below, we construct m0, B_m0, gamma0, r0, s0 which are fields of seq[k+1]
    <3> PICK m0 \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, m0)
        BY <3>13, LatestSubset
    <3> WellFormed(m0)
        BY DEF KnownMsgsSpec
    <3> m0 \in Message
        BY DEF KnownMsgsSpec, TypeOK
    <3> m0 \in known_msgs[L0]
        BY DEF KnownMsgsSpec
    \* TODO define lrns() function that returns {} for Proposal messages
    <3> ~Proposal(m0)
    <3> m0.lrns \cap Con(seq[k].gamma, seq[k].r) # {}
        BY DEF D
    \* That concludes the definition of m[k + 1]
    \* m0 has a ballot number:
    <3> PICK B_m0 \in Ballot : B(m0, B_m0)
        BY DEF WellFormed

    <3>cond4. \A i \in 1..k : m0 \in Tran(seq[i].r)
      \* By construction of m0,
      <4> SUFFICES \A i \in 1..k - 1 : m0 \in Tran(seq[i].r)
          OBVIOUS
      \* By IH, we have
      <4> \A i \in 1..k - 1 : seq[k].m \in Tran(seq[i].r)
          BY DEF HeterogeneousSpecCond
      \* First,
      <4> m0 \in Tran(seq[k].m)
        \* By construction of m0 and the fact that seq[k].r \in Tran(seq[k].m), we conclude
          BY Tran_trans
      \* which by transitivity of Tran and the fact that all are soundly typed
      <4> \A i \in 1..k - 1 : seq[i].r \in Message
          BY WhateverSpec
      \* gives
      <4> QED BY Tran_trans

    \* Now define gamma[k + 1]:
    <3> PICK gamma0 \in m0.lrns \cap Con(seq[k].gamma, seq[k].r) : TRUE
        OBVIOUS
    <3> gamma0 \in Learner
        BY DEF WellFormed

    \* Now define r[k + 1]:
    \* First, show that there exists an acceptor a0
    \* that sent r0 from the quorum Q(m0, 1) and s0 from Q(s_k, maxDepth(alpha) - k)
    \* and is not Caught in r_k
    \* Therefore, similar, to the base case s_0 \in Tran(r_0)
    <3>20. m0.lrns = { l \in Learner : [lr |-> l, q |-> { mm.acc : mm \in qd(l, m0, 1) }] \in TrustLive }
        BY DEF WellFormed
    <3> DEFINE Q2 == qd(gamma0, m0, 1)
    <3> [lr |-> gamma0, q |-> { mm.acc : mm \in Q2 }] \in TrustLive
        BY <3>20
    <3> Q2 \in SUBSET Tran(m0)
        BY QuorumProperty1
    <3> Q2 \in SUBSET Message
        BY Tran_Message
    <3> Q2 \in SUBSET known_msgs[L0]
        BY DEF KnownMsgsSpec
    <3> Q2 \in SUBSET Tran(seq[k].r)
        BY Tran_trans
    <3> Q2 # {}
        BY TrustLiveNonEmpty
    \* Therefore,
    <3> TwoA(m0)
        BY QdEq0, MessageTypeSpec

    <3>cond3. \A i \in 1..k : B_m0 < seq[i].B_m
      \* First, by cond 4 proven above,
      <4> \A i \in 1..k : m0 \in Tran(seq[i].r)
          BY <3>cond4
      \* Moreover, as shown above,
      <4> \A i \in 1..k : B(seq[i].r, seq[i].B_m) /\ OneB(seq[i].r)
          OBVIOUS
      \* Moreover,
      <4> \A i \in 1..k : m0 # seq[i].r
          BY MessageTypeSpec
      \* Therefore,
      <4> QED BY WellFormedCondition111 DEF OneA, Proposal

\*LEMMA QuorumProperty1 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message,
\*           NEW d \in Nat
\*    PROVE  \A y \in qd(alpha, x, d) :
\*            /\ y \in Tran(x)
\*            /\ ~Proposal(y)
\*PROOF
\*<1> QED

    \* Using, Q2 defined above, we now define s0 and r0    
    \* Define Q1 as a quorum of s[k] depth (maxDepth(alpha) - k)
    <3> maxDepth(alpha) - k \in Nat
        OBVIOUS
    <3> DEFINE Q1 == qd(alpha, seq[k].s, (maxDepth(alpha) - k))
    <3> [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
\*       BY QuorumProperty3
    <3> Q1 \in SUBSET Tran(seq[k].r)
    <3> gamma0 \in Con(alpha, seq[k].r)
    <3> PICK p \in Acceptor, s0 \in Q1, r0 \in Q2 :
            /\ p \notin Caught(seq[k].r)
            /\ s0.acc = p
            /\ r0.acc = p
      <4> HIDE DEF Q2, Q1
      <4> QED BY EntLiveQuorumConIntersection
    <3> r0 \in Message /\ s0 \in Message
    <3> ~Proposal(s0)
    \* BY qd Property1
    <3> ~Proposal(r0)
    <3> B(r0, B_m0)
        BY QuorumProperty2
    <3> B(s0, bal)
        BY QuorumProperty2
    \* we need to show that:
    <3> /\ bal < B_m0 \* 1)
        /\ B_m0 < seq[k].B_m \* 2)

\*LEMMA TranBallot ==
\*    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
\*           NEW b1 \in Ballot, NEW b2 \in Ballot,
\*           B(m1, b1), B(m2, b2)
\*    PROVE  b2 <= b1

\*LEMMA NotCaughtXXX ==
\*    ASSUME KnownMsgsPrevTranSpec,
\*           KnownMsgsSpec,
\*           TypeOK,
\*           NEW AL \in SafeAcceptor \cup Learner,
\*           NEW a \in Acceptor,
\*           NEW M \in known_msgs[AL],
\*           NEW x \in Tran(M), NEW y \in Tran(M),
\*           x.acc = a,
\*           y.acc = a,
\*           ~Proposal(x),
\*           ~Proposal(y),
\*           a \notin Caught(M)
\*    PROVE  x \in Tran(y) \/ y \in Tran(x)

    <3> s0 \in Tran(r0)
        \* From 1), we conclude
        BY NotCaughtXXX, TranBallot DEF Ballot \* TODO avoid unfolding Ballot here and elsewhere by formulating that the order is total
    <3> DEFINE w0 == [m |-> m0, B_m |-> B_m0, r |-> r0, s |-> s0, gamma |-> gamma0]
    <3> w0 \in Whatever
        BY DEF Whatever
    <3> w0.B_m \in Ballot
        OBVIOUS
    <3> DEFINE seq0 == Append(seq, w0)
    <3>100. HeterogeneousSpecCond(alpha, bal, M, V_M, seq0, k + 1)

\*        \* auxiliary:
\*        /\ B(m, B_m)
\*        \* cond 1:
\*        /\ x = 1 => <<alpha, gamma>> \in Ent
\*        \* cond 2:
\*        /\ bal < B_m
\*        \* cond 3:
\*        /\ x > 1 => \A i \in 1..(x - 1) : B_m < seq[i].B_m
\*        \* cond 4:
\*        /\ x > 1 => m \in Tran(seq[x - 1].r)
\*        \* cond 5:
\*        /\ x > 1 => gamma \in Con(alpha, seq[x - 1].r)
\*        \* cond 6:
\*        /\ x > 2 => gamma \notin Con(alpha, seq[x - 2].r)

      <4> (k + 1) - 1 = k
          OBVIOUS
      <4>0. B(seq0[k + 1].m, seq0[k + 1].B_m)
            OBVIOUS
      <4>1. k + 1 # 0
            OBVIOUS
      <4>2. bal < seq0[k + 1].B_m \* property 1) above
            OBVIOUS
      <4>3. \A i \in 1..((k + 1) - 1) : seq0[k + 1].B_m < seq0[i].B_m \* property 2) above
            OBVIOUS
      <4>4. seq0[k + 1].m \in Tran(seq0[(k + 1) - 1].r)
            OBVIOUS
      <4>5. seq0[k + 1].gamma \in Con(alpha, seq0[(k + 1) - 1].r)
            OBVIOUS
      <4>6. k + 1 > 2 => seq0[k + 1].gamma \notin Con(alpha, seq0[(k + 1) - 2].r)
        <5> SUFFICES ASSUME k > 1, gamma0 \in Con(alpha, seq[k - 1].r) PROVE FALSE
            OBVIOUS
        <5> HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, k)
            OBVIOUS
        \* We need to construct new pair of (r, s), say (r_bad, s_bad), such that
        \* seq_bad defined as seq[k* |-> w_bad], for some k*, still satisfies HeterogeneousSpecCond(..., seq_bad)
        \* with
        \* w_bad == [m |-> m0, B_m |-> B_m0, r |-> r_bad, s |-> s_bad, gamma |-> gamma0]
        \* Then we conclude that, by construction, seq[k].B_m <= B_m0 which contradicts <4>3
        \* Isaac: we need to find the earliest k such that
        \* gamma0 \in Con(alpha, seq[k].r)
        \* Denote it k*.
        \* CASE k* = k: implies <4>6 directly.
        \* CASE k* < k: we prove FALSE.
        \* We construct seq_bad as seq[k* + 1 |-> w_bad], with w_bad defined as above.
        \* We prove then that HeterogeneousSpecCond(..., seq_bad), which implies that
        \* seq[k* + 1].B_m <= B_m0
        \* The latter contradicts with B_m0 < seq[i].B_m, forall i, by cond 3


\*LEMMA SmallestIndexExists ==
\*    ASSUME NEW S, NEW P(_),
\*           NEW n \in Nat, NEW seq \in [1..n -> S],
\*           NEW n0 \in 1..n,
\*           P(seq[n0])
\*    PROVE  \E i \in 1..n : SmallestIndex(seq, P, i)

        <5> DEFINE R(w) == gamma0 \in Con(alpha, w.r)
        <5> PICK k_star \in 1..k : SmallestIndex(seq, R, k_star)
          <6> R(seq[k])
              OBVIOUS
          <6> k \in 1..k
              OBVIOUS
          <6> HIDE DEF R
          <6> QED BY SmallestIndexExists, Isa
        <5>1. CASE k_star = k
              BY <5>1 DEF SmallestIndex
        <5>2. CASE k_star < k
          <6> k_star + 1 =< k
              BY <5>2
          <6> k_star + 1 > 1
              OBVIOUS
          <6> (k_star + 1) - 1 = k_star
              OBVIOUS
          <6> seq[k_star].r \in Message
          <6> DEFINE Q1_star == qd(alpha, seq[k_star].s, (maxDepth(alpha) - k_star))
          <6> [lr |-> alpha, q |-> { mm.acc : mm \in Q1_star }] \in TrustLive
          <6> Q1_star \in SUBSET Tran(seq[k_star].r)
          <6> gamma0 \in Con(alpha, seq[k_star].r)
              BY DEF SmallestIndex
          <6> Q2 \in SUBSET Tran(seq[k_star].r)    
          <6> PICK p_star \in Acceptor, s_star \in Q1_star, r_star \in Q2 :
                /\ p_star \notin Caught(seq[k_star].r)
                /\ s_star.acc = p_star
                /\ r_star.acc = p_star
            <7> HIDE DEF Q2, Q1_star
            <7> QED BY EntLiveQuorumConIntersection
          <6> s_star \in Message
          <6> r_star \in Message
          <6> DEFINE w_star == [m |-> m0, B_m |-> B_m0, r |-> r_star, s |-> s_star, gamma |-> gamma0]
          <6> w_star \in Whatever
              BY DEF Whatever
          \* Sufficient to build a sequence of 1..k*+1
          <6> DEFINE seq_sub == SubSeq(seq, 1, k_star)
          <6> DEFINE seq_star == Append(seq_sub, w_star)
          <6> seq_star \in Seq(Whatever)
              BY SubSeqProperties
          <6> seq_star[k_star + 1] = w_star
              BY AppendProperties
          <6> Len(seq_star) = k_star + 1
              BY SubSeqProperties, AppendProperties
          <6> \A i \in 1..k_star : seq[i] = seq_sub[i]
              BY <5>2, SubSeqProperties
          <6> \A i \in 1..k_star : seq[i] = seq_star[i]
              BY <5>2, AppendProperties

\*LEMMA HeterogeneousSpecCondCongr ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW bal \in Ballot,
\*           NEW val \in Value,
\*           NEW k \in Nat,
\*           NEW seq1 \in Seq(Whatever),
\*           NEW seq2 \in Seq(Whatever),
\*           \A i \in 1..k : seq1[i] = seq2[i]
\*    PROVE  \A j \in 1..k :
\*            HeterogeneousSpecCond(alpha, bal, val, seq1, j) =>
\*            HeterogeneousSpecCond(alpha, bal, val, seq2, j)

          <6>1. \A x \in 1..k_star : HeterogeneousSpecCond(alpha, bal, M, V_M, seq_star, x)
                BY HeterogeneousSpecCondCongr
          <6>2. HeterogeneousSpecCond(alpha, bal, M, V_M, seq_star, k_star + 1)

\*          <6> DEFINE w_star == [m |-> m0, B_m |-> B_m0, r |-> r_star, s |-> s_star, gamma |-> gamma0]

            <7>0. B(seq_star[k_star + 1].m, seq_star[k_star + 1].B_m)
                  OBVIOUS
\*            <7>1.
            <7>2. bal < seq_star[k_star + 1].B_m
                  OBVIOUS
            <7>3. \A i \in 1..(k_star + 1) - 1 : seq_star[k_star + 1].B_m < seq_star[i].B_m
                  OBVIOUS
            <7>4. seq_star[k_star + 1].m \in Tran(seq_star[k_star].r)
            <7>5. seq_star[k_star + 1].gamma \in Con(alpha, seq_star[k_star].r)
                  OBVIOUS
            <7>6. k_star + 1 > 2 => seq_star[k_star + 1].gamma \notin Con(alpha, seq_star[k_star - 1].r)
            <7>7. seq_star[k_star + 1].gamma \in seq_star[k_star + 1].m.lrns
                  OBVIOUS
            <7>8. seq_star[k_star + 1].r \in qd(seq_star[k_star + 1].gamma, seq_star[k_star + 1].m, 1)
                  OBVIOUS
            <7>9. seq_star[k_star + 1].s \in Tran(seq_star[k_star + 1].r)
            <7>10. seq_star[k_star + 1].s \in Tran(seq_star[k_star].s)
            <7>11. seq_star[k_star + 1].r.acc = seq_star[k_star + 1].s.acc
            <7>12. k_star + 1 =< maxDepth(alpha) =>
                    [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq_star[k_star + 1].s, maxDepth(alpha) - (k_star + 1) + 1) }] \in TrustLive
            <7>13. B(seq_star[k_star + 1].s, bal)
            <7>14. V(seq_star[k_star + 1].m, V_M)
            <7> HIDE DEF seq_star
            <7> QED BY  <7>0
                       , <7>2
                       , <7>3
                       , <7>4
                       , <7>5
                       , <7>6
                       , <7>7
                       , <7>8
                       , <7>9
                       , <7>10
                       , <7>11
                       , <7>12
                       , <7>13
                       , <7>14
                    DEF HeterogeneousSpecCond

          \* We get a contradiction:
          \* <6> seq[k_star + 1] was supposed to have a minimal ballot number s.t. HeterogeneousSpecCondMin(seq, k_star + 1)
          \* However, we have proven that HeterogeneousSpecCond(seq_star, k_star + 1), and w_star.B, which equals B_m0, is smaller than the ballot of seq[k_star + 1].

          <6>3. seq_star[k_star + 1].B_m < seq[k_star + 1].B_m
                OBVIOUS
          <6>4. HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, k_star + 1)
                OBVIOUS
          <6> HIDE DEF w_star
          <6> DEFINE seq1 == [seq EXCEPT ![k_star + 1] = w_star]
          <6> seq1 \in Seq(Whatever)
              OBVIOUS
          <6> \A i \in 1..k_star + 1 : seq1[i] = seq_star[i]
              OBVIOUS
          <6>5. HeterogeneousSpecCond(alpha, bal, M, V_M, seq1, k_star + 1)
            <7> HIDE DEF seq1
            <7> HIDE DEF seq_star
            <7> QED BY <6>2, HeterogeneousSpecCondCongr
          <6>6. seq[k_star + 1].B_m =< seq1[k_star + 1].B_m
                BY <6>4, <6>5 DEF HeterogeneousSpecCondMin
          <6>7. seq_star[k_star + 1] = seq1[k_star + 1]
                OBVIOUS
          <6> HIDE DEF seq1
          <6> HIDE DEF seq_star
          <6> QED BY <6>7, <6>6, <6>3, WhateverSpec DEF Ballot
        <5> QED BY <5>1, <5>2

\*HeterogeneousSpecCond(alpha, bal, V_M, seq, x) ==
\*    LET m == seq[x].m
\*        B_m == seq[x].B_m
\*        r == seq[x].r
\*        s == seq[x].s
\*        gamma == seq[x].gamma
\*    IN
\*        \* auxiliary:
\*        /\ B(m, B_m)
\*        \* cond 1:
\*        /\ x = 1 => <<alpha, gamma>> \in Ent
\*        \* cond 2:
\*        /\ bal < B_m
\*        \* cond 3:
\*        /\ x > 1 => \A i \in 1..(x - 1) : B_m < seq[i].B_m
\*        \* cond 4:
\*        /\ x > 1 => m \in Tran(seq[x - 1].r)
\*        \* cond 5:
\*        /\ x > 1 => gamma \in Con(alpha, seq[x - 1].r)
\*        \* cond 6:
\*        /\ x > 2 => gamma \notin Con(alpha, seq[x - 2].r)
\*        \* cond 7:
\*        /\ gamma \in m.lrns
\*        \* cond 8:
\*        /\ r \in qd(gamma, m, 1)
\*\*        /\ r \in q(gamma, m)
\*        \* cond 9:
\*        /\ s \in Tran(r)
\*        \* cond 10:
\*        /\ x > 1 => s \in Tran(seq[x - 1].s)
\*        \* cond 11:
\*        /\ r.acc = s.acc
\*        \* cond 12:
\*\*        /\ depth(alpha, s) = maxDepth(alpha) - x
\*        /\ x =< maxDepth(alpha) =>
\*            [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, s, maxDepth(alpha) - x + 1) }] \in TrustLive
\*        \* cond 13:
\*        /\ B(s, bal)
\*        \* cond 14:
\*        /\ V(m, V_M)


      <4>7. seq0[k + 1].gamma \in seq0[k + 1].m.lrns
            OBVIOUS
      <4>8. seq0[k + 1].r \in qd(seq0[k + 1].gamma, seq0[k + 1].m, 1)
            OBVIOUS
      <4>9. seq0[k + 1].s \in Tran(seq0[k + 1].r)
            OBVIOUS
      <4>10. seq0[k + 1].s \in Tran(seq0[(k + 1) - 1].s)
      <4>11. seq0[k + 1].r.acc = seq0[k + 1].s.acc
             OBVIOUS
      <4>12. k + 1 =< maxDepth(alpha) =>
                [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq0[k + 1].s, maxDepth(alpha) - (k + 1) + 1) }] \in TrustLive
      <4>13. B(seq0[k + 1].s, bal)
      <4>14. V(seq0[k + 1].m, V_M)
      <4> HIDE DEF seq0
      <4> QED BY <4>0, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF HeterogeneousSpecCond
    <3> QED BY <3>100

\* TODO RENAME
\*Whatever == [m : Message, B_m : Ballot, r : Message, s : Message, gamma : Learner]
\*
\*LEMMA WhateverSpec ==
\*    ASSUME NEW w \in Whatever
\*    PROVE  /\ w.m \in Message
\*           /\ w.B_m \in Ballot
\*           /\ w.r \in Message
\*           /\ w.s \in Message
\*           /\ w.gamma \in Learner

  <2> PICK w0 \in S : \A z \in S : w0.B_m =< z.B_m
      BY WhateverMin
  <2> DEFINE seq0 == Append(seq, w0)
  <2> seq0[k + 1] = w0
      OBVIOUS
  <2> seq0 \in [1..k + 1 -> Whatever]
      BY AppendProperties 
  <2> ASSUME NEW x \in 0..k PROVE seq0[k] = seq[k]
      BY AppendProperties
  <2> HeterogeneousSpecCond(alpha, bal, M, V_M, seq0, k + 1)
      OBVIOUS
  <2> HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq0, k + 1)
      BY WhateverSpec DEF HeterogeneousSpecCondMin, Ballot
  <2> \A i \in 1..k : HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq0, i)
      BY HeterogeneousSpecCondMinCongr
  <2> SUFFICES
        \E seq_1 \in [1..k + 1 -> Whatever] :
              \A x \in 1..k + 1 :
                     HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq_1, x)
      OBVIOUS
  <2> WITNESS seq0 \in [1..k + 1 -> Whatever]
  <2> QED OBVIOUS
<1> HIDE DEF P
<1>3. QED BY <1>0, <1>1, INDUCTION_SCHEME, IsaM("blast")


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
                      TwoA(M),
                      L2 \in M.lrns,
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
      BY <2>1, IsaM("blast") DEF WellFormed
  <2> DEFINE Q2 == { m \in Tran(M) :
                        /\ OneB(m)
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
    <3> QED BY LiveQuorumConIntersection, BQAssumption
  <2> TwoA(m2a)
      BY <2>8 DEF Known2a
  <2> L1 \in m2a.lrns
      BY <2>8 DEF Known2a
  <2> m2a \in msgs
      OBVIOUS
  <2> B(m2a, B1)
      BY <2>8 DEF Known2a
  <2> V(m2a, V1)
      BY <2>8 DEF Known2a
  <2> OneB(m1b)
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
  <2>13. \A y \in Tran(m1b) :
            m1b # y /\ ~OneA(y) =>
            \A b1, b2 \in Ballot : B(m1b, b1) /\ B(y, b2) => b2 < b1
    <3> SUFFICES
        \A y \in Tran(m1b) :
            m1b # y /\ ~OneA(y) =>
            \A b1, b2 \in Ballot : B(m1b, b1) /\ B(y, b2) => b2 # b1
        BY WellFormedCondition3
    <3> SUFFICES \A y \in Tran(m1b) : m1b # y /\ SameBallot(m1b, y) => OneA(y)
        BY WellFormedCondition2
    <3> QED BY DEF WellFormed, WellFormed1b, OneA, SameBallot
  <2>14. m2a \in Tran(m1b)
    <3> m1b \notin Tran(m2a)
        BY TranBallot DEF Ballot
    <3> QED BY MessageTypeSpec
            DEF MsgsSafeAcceptorPrevTranLinearSpec, MsgsSafeAcceptorPrevTranSpec, SentBy
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
    <3> PICK r \in Tran(m1b) :
            /\ TwoA(r)
            /\ L1 \in r.lrns
            /\ \A b2a, br \in Ballot :
                B(m2a, b2a) /\ B(r, br) => b2a < br
            /\ \A v2a, vr \in Value :
                V(m2a, v2a) /\ V(r, vr) => v2a # vr
        BY <2>16 DEF Buried
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
        BY <2>13, MessageTypeSpec
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
    BY TrustLiveAssumption
<1> PICK S2 \in SUBSET Known2a(L2, BB, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY DEF ChosenIn
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption
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
           ChosenIn(L1, B1, V1),
           ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET Known2a(L1, B1, V1) :
        [lr |-> L1, q |-> { m.acc : m \in S1 }] \in TrustLive
    BY DEF ChosenIn
<1> DEFINE Q1 == { m.acc : m \in S1 }
<1> Q1 \in ByzQuorum
    BY TrustLiveAssumption
<1> PICK S2 \in SUBSET Known2a(L2, B2, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY DEF ChosenIn
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption
<1> <<L2, L2>> \in Ent
    BY EntanglementSelf, EntanglementSym
<1> PICK A \in Q2 : TRUE
    BY EntaglementTrustLiveNonEmpty
<1> PICK M \in known_msgs[L2] :
        /\ TwoA(M)
        /\ L2 \in M.lrns
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
<1>1. CASE \E p \in Proposer : ProposerAction(p)
      BY <1>1 DEF ProposerAction, SendProposal, Safety
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
      BY <1>3 DEF Process, Safety
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv, Safety
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, BVal >>
      BY <1>7 DEF LearnerDecide
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
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage, Safety
<1>9. QED BY <1>1, <1>3, <1>6, <1>7, <1>8
          DEF NextTLA, SafeAcceptorAction, LearnerAction

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
PROOF BY Isa DEF KnownMsgsSpec, vars, WellFormed, WellFormed1b,
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
\* Last modified Mon Dec 09 16:10:41 CET 2024 by karbyshev
\* Created Tue Jun 20 00:28:26 CEST 2023 by karbyshev
