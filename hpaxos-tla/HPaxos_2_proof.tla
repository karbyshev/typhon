-------------------------- MODULE HPaxos_2_proof ----------------------------
EXTENDS HPaxos_2, HMessage_proof, HLearnerGraph_proof, Lib,
        SequenceTheorems, TLAPS

-----------------------------------------------------------------------------
\* TODO move to separate file
LEMMA MaxUnique ==
    ASSUME NEW S,
           \A x, y \in S : x =< y /\ y =< x => x = y,
           NEW A \in SUBSET S,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y
PROOF BY DEF IsMax

LEMMA BallotFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Ballot,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)
PROOF BY NatFiniteSetMaxExists DEF Ballot

LEMMA BallotMaxUnique ==
    ASSUME NEW A \in SUBSET Ballot,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y
PROOF BY MaxUnique DEF Ballot

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

LEMMA SameBallot_B ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot,
           B(x, bal),
           B(y, bal)
    PROVE  SameBallot(x, y)
PROOF BY B_func DEF SameBallot

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
    PROVE  b2 =< b1
PROOF BY Tran_trans DEF B, Get1a

LEMMA LatestSubset ==
    ASSUME NEW P \in SUBSET Message
    PROVE  Latest(P) \in SUBSET P
PROOF BY DEF Latest

LEMMA LatestNonEmpty ==
    ASSUME NEW P \in SUBSET { m \in Message : WellFormed(m) },
           P # {},
           IsFiniteSet(P)
    PROVE  Latest(P) # {}
PROOF
<1> DEFINE f_bis == [ m \in P |-> CHOOSE bal \in Ballot : B(m, bal) ]
<1> f_bis \in [ P -> Ballot ]
    BY DEF WellFormed
<1> DEFINE Q == Range(f_bis)
<1> Q \in SUBSET Ballot
    BY DEF WellFormed, Range
<1> Q # {}
    BY B_func DEF WellFormed, Range
<1> f_bis \in Surjection(P, Q)
    BY Fun_RangeProperties
<1> IsFiniteSet(Q)
    BY Zenon, FS_Surjection
<1> PICK bal1 \in Q : IsMax(bal1, Q)
    BY BallotFiniteSetMaxExists
<1> bal1 \in Ballot
    BY DEF Range
<1> PICK m1 \in P : f_bis[m1] = bal1
    BY DEF Surjection
<1> m1 \in Latest(P)
    BY B_func DEF Latest, WellFormed, IsMax, Range
<1> QED OBVIOUS

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
<1> QED BY <1>1, SmallestNatural, Blast

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

\* TODO rename
LEMMA WellFormedCondition111 ==
    ASSUME NEW m \in Message,
           WellFormed(m),
           OneB(m)
    PROVE  \A y \in Tran(m) : m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
PROOF BY WellFormedCondition2, WellFormedCondition3
      DEF WellFormed, WellFormed1b, Proposal, OneA

-----------------------------------------------------------------------------
\* TODO convert to a lemma
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

KnownMsgsSpec1 ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ known_msgs[AL] \in SUBSET msgs
        /\ IsFiniteSet(known_msgs[AL])

KnownMsgsSpec2 ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ \A M \in known_msgs[AL] :
            /\ KnownRefs(AL, M)
            /\ WellFormed(M)
            /\ Tran(M) \in SUBSET known_msgs[AL]
            /\ \E b \in Ballot : B(M, b)

\* TODO rename
KnownMsgsSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ known_msgs[AL] \in SUBSET msgs
        /\ IsFiniteSet(known_msgs[AL])
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

\* TODO not used with the current definition of Caught
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
      BY MessageRec_spec, MessageRec_eq0 DEF MessageRec0
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

LEMMA Sent_monotone ==
    TypeOK /\ NextTLA => msgs \in SUBSET msgs'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA
             PROVE  msgs \in SUBSET msgs'
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

LEMMA UniqueMessageSent ==
    TypeOK /\ NextTLA =>
    \A m1, m2 \in msgs' \ msgs : m1 = m2
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
    ASSUME UNCHANGED BVal
    PROVE  \A m \in Message : WellFormed(m) <=> WellFormed(m)'
PROOF BY Qd_monotone DEF WellFormed

LEMMA KnownMsgMonotone ==
    TypeOK /\ NextTLA =>
    \A AL \in SafeAcceptor \cup Learner :
        known_msgs[AL] \in SUBSET known_msgs[AL]'
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

LEMMA Known2aMonotone ==
    TypeOK /\ NextTLA =>
    \A L \in Learner, bal \in Ballot, val \in Value :
        Known2a(L, bal, val) \in SUBSET Known2a(L, bal, val)'
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
    UNCHANGED BVal /\ MaxDepthSpec /\
    TypeOK /\ NextTLA /\
    KnownMsgsSpec2 /\
    DecisionSpec => DecisionSpec'
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
    BY DEF Known2a, KnownMsgsSpec2, TypeOK
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

LEMMA KnownMsgsSpec1Invariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 =>
    KnownMsgsSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    KnownMsgsSpec1
             PROVE  KnownMsgsSpec1'
    OBVIOUS
<1> TypeOK'
    BY TypeOKInvariant
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner
             PROVE  /\ known_msgs[AL]' \in SUBSET msgs'
                    /\ IsFiniteSet(known_msgs[AL]')
    BY DEF KnownMsgsSpec1
<1> USE DEF KnownMsgsSpec1
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> Recv(acc, m)
      BY DEF Process
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY Sent_monotone DEF Recv, TypeOK, Acceptor
  <2> IsFiniteSet(known_msgs[AL]')
    <3> IsFiniteSet(known_msgs[acc] \cup {m})
        BY FS_Singleton, FS_Union
    <3> QED BY DEF Recv, TypeOK, Acceptor
  <2> QED OBVIOUS
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, m \in msgs : LearnerRecv(lrn, m)
      BY <1>6
  <2> Recv(lrn, m)
      BY DEF LearnerRecv
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY Sent_monotone DEF Recv, TypeOK, Acceptor
  <2> IsFiniteSet(known_msgs[AL]')
    <3> IsFiniteSet(known_msgs[lrn] \cup {m})
        BY FS_Singleton, FS_Union
    <3> QED BY DEF Recv, TypeOK, Acceptor
  <2> QED OBVIOUS
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7
  <2> USE DEF LearnerDecide
  <2> QED OBVIOUS
<1>8. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>8
  <2> USE DEF FakeSendControlMessage
  <2> QED BY DEF Send
<1> QED BY <1>1, <1>3, <1>6, <1>7, <1>8
        DEF NextTLA, SafeAcceptorAction, LearnerRecv,
            LearnerAction, FakeAcceptorAction

LEMMA KnownMsgsSpec2Invariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 /\
    KnownMsgsSpec2 =>
    KnownMsgsSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    KnownMsgsSpec1,
                    KnownMsgsSpec2
             PROVE  KnownMsgsSpec2'
    OBVIOUS
<1> TypeOK'
    BY TypeOKInvariant
<1> KnownMsgsSpec1'
    BY KnownMsgsSpec1Invariant
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL]'
             PROVE  /\ KnownRefs(AL, M)'
                    /\ WellFormed(M)'
                    /\ Tran(M) \in SUBSET known_msgs[AL]'
                    /\ \E b \in Ballot : B(M, b)
    BY DEF KnownMsgsSpec2
<1> USE DEF KnownMsgsSpec1, KnownMsgsSpec2
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> USE DEF SendProposal
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> Recv(acc, m)
      BY DEF Process
  <2> UNCHANGED BVal
      BY DEF Process
  <2> WellFormed(m)
      BY DEF Process
  <2> m \in Message
      BY DEF WellFormed
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv, TypeOK, Acceptor
  <2> WellFormed(M)'
    <3> CASE M \in known_msgs[AL]
        BY WellFormed_monotone DEF TypeOK
    <3> CASE M \notin known_msgs[AL]
      <4> M = m
          BY DEF Recv, TypeOK, Acceptor
      <4> QED BY WellFormed_monotone DEF TypeOK
    <3> QED OBVIOUS
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \in known_msgs[AL]
        BY DEF Recv, TypeOK, Acceptor
    <3> CASE M \notin known_msgs[AL]
      <4> M = m
          BY DEF Recv, TypeOK, Acceptor
      <4> QED BY Tran_eq, KnownMsgMonotone DEF Recv, KnownRefs, TypeOK, Acceptor
    <3> QED OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, m \in msgs : LearnerRecv(lrn, m)
      BY <1>6
  <2> Recv(lrn, m)
      BY DEF LearnerRecv
  <2> UNCHANGED BVal
      BY DEF LearnerRecv
  <2> WellFormed(m)
      BY DEF LearnerRecv
  <2> m \in Message
      BY DEF WellFormed
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv, TypeOK, Acceptor
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK, Recv, Acceptor
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \in known_msgs[AL]
        BY DEF Recv, TypeOK, Acceptor
    <3> CASE M \notin known_msgs[AL]
        BY Tran_eq DEF Recv, KnownRefs, TypeOK, Acceptor
    <3> QED OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7
  <2> USE DEF LearnerDecide
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
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner
             PROVE  /\ known_msgs[AL]' \in SUBSET msgs'
                    /\ IsFiniteSet(known_msgs[AL]')
                    /\ \A M \in known_msgs[AL]' :
                        /\ KnownRefs(AL, M)'
                        /\ WellFormed(M)'
                        /\ Tran(M) \in SUBSET known_msgs[AL]'
                        /\ \E b \in Ballot : B(M, b)
    BY DEF KnownMsgsSpec
<1> DEFINE K == known_msgs[AL]'
<1> SUFFICES /\ K \in SUBSET msgs'
             /\ IsFiniteSet(K)
             /\ \A M \in K :
                /\ KnownRefs(AL, M)'
                /\ WellFormed(M)'
                /\ Tran(M) \in SUBSET K
                /\ \E b \in Ballot : B(M, b)
    OBVIOUS
<1> SUFFICES /\ K \in SUBSET msgs'
             /\ \A M \in K :
                /\ IsFiniteSet(K)
                /\ /\ KnownRefs(AL, M)'
                   /\ WellFormed(M)'
                   /\ Tran(M) \in SUBSET K
                   /\ \E b \in Ballot : B(M, b)
  \*<2> HIDE DEF K
  <2> QED BY DEF TypeOK, Acceptor
<1> SUFFICES ASSUME NEW M \in K
             PROVE  /\ K \in SUBSET msgs'
                    /\ IsFiniteSet(K)
                    /\ KnownRefs(AL, M)'
                    /\ WellFormed(M)'
                    /\ Tran(M) \in SUBSET K
                    /\ \E b \in Ballot : B(M, b)
  <2> HIDE DEF K
  <2> QED OBVIOUS
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
  <2> Recv(acc, m)
      BY DEF Process
  <2> BVal' = BVal
      BY DEF Process
  <2> WellFormed(m)
      BY DEF Process
  <2> m \in Message
      BY DEF WellFormed
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY Sent_monotone DEF Recv, TypeOK, Acceptor
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv, TypeOK, Acceptor
  <2> WellFormed(M)'
    <3> CASE M \in known_msgs[AL]
        BY WellFormed_monotone DEF TypeOK
    <3> CASE M \notin known_msgs[AL]
      <4> M = m
          BY DEF Recv, TypeOK, Acceptor
      <4> QED BY WellFormed_monotone DEF TypeOK
    <3> QED OBVIOUS
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \in known_msgs[AL]
        BY DEF Recv, TypeOK, Acceptor
    <3> CASE M \notin known_msgs[AL]
      <4> M = m
          BY DEF Recv, TypeOK, Acceptor
      <4> QED BY Tran_eq, KnownMsgMonotone DEF Recv, KnownRefs, TypeOK, Acceptor
    <3> QED OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, m \in msgs : LearnerRecv(lrn, m)
      BY <1>6
  <2> Recv(lrn, m)
      BY DEF LearnerRecv
  <2> BVal' = BVal
      BY DEF LearnerRecv
  <2> WellFormed(m)
      BY DEF LearnerRecv
  <2> m \in Message
      BY DEF WellFormed
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY Sent_monotone DEF Recv, TypeOK, Acceptor
  <2> KnownRefs(AL, M)'
      BY DEF KnownRefs, Recv, TypeOK, Acceptor
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK, Recv, Acceptor
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \in known_msgs[AL]
        BY DEF Recv, TypeOK, Acceptor
    <3> CASE M \notin known_msgs[AL]
        BY Tran_eq DEF Recv, KnownRefs, TypeOK, Acceptor
    <3> QED OBVIOUS
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
    <2> SUFFICES ASSUME NEW A \in SafeAcceptor,
                        NEW m1 \in SentBy(A)',
                        NEW m2 \in SentBy(A)'
                 PROVE  m1 \in PrevTran(m2) \/ m2 \in PrevTran(m1)
        BY DEF MsgsSafeAcceptorPrevTranLinearSpec
    <2> USE DEF MsgsSafeAcceptorPrevTranLinearSpec
    <2> m1 \in Message /\ m2 \in Message
        BY DEF SentBy, TypeOK 
    <2> CASE m1 \in msgs /\ m2 \in msgs
        BY DEF SentBy, OneA, Proposal
    <2> CASE m1 \in msgs' \ msgs /\ m2 \in msgs' \ msgs
        BY UniqueMessageSent, PrevTran_refl DEF SentBy, OneA, Proposal
    <2> QED BY DEF SentBy, OneA, Proposal
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
    MsgsSafeAcceptorPrevRefSpec /\
    MsgsSafeAcceptorPrevTranSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorSpec3 => MsgsSafeAcceptorSpec3'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
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
      BY DEF TypeOK, Acceptor
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
    ASSUME TypeOK, KnownMsgsSpec2, MsgsSafeAcceptorPrevTranLinearSpec
    PROVE  CaughtSpec
PROOF
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL],
                    Caught(M) \cap SafeAcceptor # {}
             PROVE  FALSE
    BY DEF CaughtSpec
<1> PICK acc \in Caught(M) \cap SafeAcceptor : TRUE
    OBVIOUS
<1> PICK msg \in CaughtMsg(M) :
            /\ ~Proposal(msg)
            /\ msg.acc = acc
    BY DEF Caught, CaughtMsg
<1> msg \in Tran(M)
    BY DEF CaughtMsg
<1> PICK msg1 \in Tran(M) :
            /\ ~Proposal(msg1)
            /\ msg.acc = msg1.acc
            /\ msg # msg1
            /\ msg \notin PrevTran(msg1)
            /\ msg1 \notin PrevTran(msg)
    BY DEF CaughtMsg
<1> QED BY MessageSpec
        DEF MsgsSafeAcceptorPrevTranLinearSpec, KnownMsgsSpec2, SentBy, Proposal, OneA

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
<1> QED BY ByzQuorumProperties

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
<1> QED BY ByzQuorumProperties

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
<1> QED BY ByzQuorumProperties

LEMMA EntConnectedByQuorum ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  ConByQuorum(alpha, beta, m, SafeAcceptor)
PROOF BY ByzQuorumProperties DEF ConByQuorum, Ent, CaughtSpec

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  beta \in Con(alpha, m)
PROOF BY EntConnectedByQuorum, ByzQuorumProperties DEF Con

LEMMA ConnectedXXX ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW m \in Message,
           Caught(m) \cap SafeAcceptor = {}
    PROVE  beta \in Con(alpha, m)
PROOF
<1> SUFFICES ConByQuorum(alpha, beta, m, SafeAcceptor)
    BY DEF Con, Acceptor, ByzQuorum
<1> QED BY ByzQuorumProperties DEF ConByQuorum, Ent

LEMMA ConnectedLearner ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message
    PROVE  Con(alpha, x) \in SUBSET Learner
PROOF BY DEF Con 

\* TODO unify naming
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
PROOF BY Tran_trans DEF Caught, CaughtMsg

LEMMA ConTran ==
    ASSUME NEW y \in Message,
           NEW alpha \in Learner,
           NEW x \in Tran(y)
    PROVE  Con(alpha, y) \in SUBSET Con(alpha, x)
PROOF BY CaughtTran DEF Con, ConByQuorum

LEMMA Con_compat ==
    ASSUME NEW x \in Message
    PROVE  \A alpha, beta \in Learner :
            beta \in Con(alpha, x) => Con(alpha, x) = Con(beta, x)
PROOF
<1> SUFFICES ASSUME NEW alpha \in Learner,
                    NEW beta \in Con(alpha, x),
                    NEW gamma \in Con(beta, x)
             PROVE  gamma \in Con(alpha, x)
    BY ConnectedSym, ConnectedLearner
<1> PICK Sbeta \in ByzQuorum : ConByQuorum(alpha, beta, x, Sbeta)
    BY DEF Con
<1> PICK Sgamma \in ByzQuorum : ConByQuorum(beta, gamma, x, Sgamma)
    BY DEF Con
<1> DEFINE Q == Sbeta \cup Sgamma
<1> Q \in ByzQuorum
    BY DEF ByzQuorum
<1> SUFFICES ConByQuorum(alpha, gamma, x, Q)
    BY DEF Con
<1> QED BY LearnerGraphAssumptionTransitivity, LearnerGraphAssumptionClosure DEF ConByQuorum 

LEMMA NotCaughtXXX ==
    ASSUME KnownMsgsPrevTranSpec,
           KnownMsgsSpec1,
           KnownMsgsSpec2,
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
    BY Tran_refl DEF KnownMsgsSpec1, KnownMsgsSpec2, TypeOK
<1> x \in known_msgs[AL] /\ y \in known_msgs[AL]
    BY DEF KnownMsgsSpec2
<1> QED BY DEF KnownMsgsPrevTranSpec, Caught, CaughtMsg

LEMMA ConAllCaught ==
    ASSUME NEW alpha \in Learner,
           NEW beta \in Learner,
           NEW x \in Message,
           beta \in Con(alpha, x),
           FakeAcceptor \in SUBSET Caught(x)
    PROVE  <<alpha, beta>> \in Ent
PROOF BY LearnerGraphAssumptionClosure, EntanglementSym
      DEF Con, ConByQuorum, Ent, Acceptor, ByzQuorum

-----------------------------------------------------------------------------

\*ConSeq(alpha) ==
\*        { seq \in Seq(Message) :
\*            /\ Len(seq) > 0
\*            /\ \A i, j \in 1..Len(seq) : i < j =>
\*                /\ seq[i] \in Tran(seq[j])
\*                /\ Con(alpha, seq[i]) # Con(alpha, seq[j])
\*        }
\*
\*
\*maxDepth(alpha) ==
\*        LET I == { n \in Nat :
\*                    \E seq \in ConSeq(alpha) :
\*                        /\ n = Len(seq)
\*                        /\ alpha \in Con(alpha, seq[n]) }
\*        IN Max(I)

LEMMA ConSeqContainsEmpty ==
    ASSUME NEW alpha \in Learner
    PROVE  << >> \in ConSeq(alpha)
PROOF BY DEF ConSeq

LEMMA ConSeqNonTrivial ==
    ASSUME NEW alpha \in Learner,
           <<alpha, alpha>> \in Ent
    PROVE  \E seq \in ConSeq(alpha) :
            /\ Len(seq) > 0
            /\ alpha \in Con(alpha, seq[Len(seq)])
PROOF
<1> PICK bal \in Ballot : TRUE
    BY DEF Ballot
<1> DEFINE val == BVal[bal]

<1> DEFINE p == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> {} ]
<1> p \in Message /\ OneA(p) /\ p.bal = bal
    BY OneA_Message
<1> Proposal(p)
    BY DEF OneA, Proposal
<1> B(p, bal)
    BY B_1a
<1> Tran(p) = {p}
    BY Tran_1a
<1> PrevTran(p) = {p}
    BY PrevTran_eq

<1> PICK safe \in SafeAcceptor : TRUE
    BY SafeAcceptorNonTrivial
<1> safe \in Acceptor
    BY DEF Acceptor

<1> oneb == [ type |-> "1b", acc |-> safe, prev |-> p, refs |-> {p}, lrns |-> {} ]
<1> oneb \in Message /\ OneB(oneb)
    BY OneB_Message
<1> ~Proposal(oneb)
    BY DEF OneB, Proposal
<1> Tran(oneb) = {oneb, p}
    BY Isa, Tran_eq

<1> alpha \in Con(alpha, oneb)
  <2> Caught(oneb) = {}
      BY DEF Caught, CaughtMsg
  <2> QED BY SafeAcceptorIsByzQuorum DEF Con, ConByQuorum, Ent

<1> [x \in 1..1 |-> oneb] \in ConSeq(alpha)
    BY SeqDef DEF ConSeq
<1> QED OBVIOUS

\*THEOREM SequencesInductionAppend ==
\*  ASSUME NEW P(_), NEW S,
\*         P(<< >>),
\*         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
\*  PROVE  \A seq \in Seq(S) : P(seq)

\*THEOREM SequencesInductionTail ==
\*  ASSUME NEW S,  NEW P(_),
\*         P(<< >>),
\*         \A s \in Seq(S) : (s # << >>) /\ P(Tail(s)) => P(s)
\*  PROVE  \A s \in Seq(S) : P(s)

\*LEMMA ConnectedLearner ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message
\*    PROVE  Con(alpha, x) \in SUBSET Learner

\*ASSUME LearnerGraphCard ==
\*    Cardinality(Learner) = N_L

LEMMA ConSeqBound ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in ConSeq(alpha)
    PROVE  Len(seq) =< N_L
PROOF
<1> DEFINE P(s) ==
        s # << >> /\
        (\A i, j \in 1..Len(s) : i < j =>
            /\ s[i] \in Tran(s[j])
            /\ Con(alpha, s[i]) # Con(alpha, s[j])) =>
        Len(s) =< Cardinality(Con(alpha, Head(s)))
<1> SUFFICES ASSUME NEW s1 \in Seq(Message) PROVE P(s1)
  <2> seq \in Seq(Message)
      BY DEF ConSeq
  <2> CASE seq # << >>
    <3> Len(seq) \in Nat
        OBVIOUS
    <3> Len(seq) =< Cardinality(Con(alpha, Head(seq)))
        BY DEF ConSeq
    <3> Head(seq) \in Message
        BY HeadTailProperties
    <3> Con(alpha, Head(seq)) \in SUBSET Learner
        BY ConnectedLearner
    <3> /\ IsFiniteSet(Con(alpha, Head(seq)))
        /\ Cardinality(Con(alpha, Head(seq))) =< Cardinality(Learner)
        BY FS_Subset, LearnerGraphCard
    <3> Cardinality(Con(alpha, Head(seq))) =< N_L
        BY LearnerGraphCard
    <3> QED BY LearnerGraphSize, FS_CardinalityType
  <2> QED BY LearnerGraphSize
<1>0. P(<< >>)
      OBVIOUS
<1>1. \A s \in Seq(Message) : (s # << >>) /\ P(Tail(s)) => P(s)
  <2> SUFFICES ASSUME NEW s \in Seq(Message),
                      s # << >>,
                      P(Tail(s)),
                      (\A i, j \in 1..Len(s) : i < j =>
                        /\ s[i] \in Tran(s[j])
                        /\ Con(alpha, s[i]) # Con(alpha, s[j]))
               PROVE  Len(s) =< Cardinality(Con(alpha, Head(s)))
      OBVIOUS
  <2> s = Cons(Head(s), Tail(s))
      BY ConsHeadTail
  <2> CASE Tail(s) = << >>
    <3> s = << Head(s) >>
        BY ConsEmpty
    <3> Len(s) = 1
        OBVIOUS
    <3> 
    <3> QED
  <2> QED
<1> HIDE DEF P
<1> QED BY <1>0, <1>1, SequencesInductionTail, Blast

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
\*                    B_m_0 =< B_m1

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
<1> WITNESS w0 \in T
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
        seq[x].B_m =< seq1[x].B_m

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

\*LEMMA KnownDepthPlusOne ==
\*    ASSUME NEW LA \in Learner \cup SafeAcceptor,
\*           NEW alpha \in Learner,
\*           NEW M \in known_msgs[LA],
\*           NEW k \in Nat,
\*           k + 1 =< N_L,
\*           depth(alpha, M) = k + 1,
\*           \* TODO
\*\*           \A l \in Learner, x \in Message : depthIdx(l, x) \in SUBSET 1..N_L,
\*           KnownMsgsSpec,
\*           TypeOK
\*    PROVE  \E X \in Tran(M) :
\*            /\ depth(alpha, X) = k
\*            /\ SameBallot(X, M)
\*PROOF
\*<1> M \in Message
\*    BY DEF KnownMsgsSpec, TypeOK
\*\*<1> PICK d0 \in {0} \cup depthIdx(alpha, M) : IsMax(d0, {0} \cup depthIdx(alpha, M))
\*\*    BY PPP
\*\*<1> depth(alpha, M) = d0
\*\*    BY MaxUnique DEF depth, Max
\*<1> k + 1 \in depthIdx(alpha, M)
\*    BY PPP, MaxUnique DEF depth, Max
\*<1> [lr |-> alpha, q |-> {m.acc : m \in qd(alpha, M, k + 1)}] \in TrustLive
\*    BY DEF depthIdx
\*
\*
\*\*qd(alpha, x, d) ==
\*\*        LET helper[i \in Nat] ==
\*\*            IF i = 0 THEN [y \in Message |-> {}]
\*\*            ELSE
\*\*                (IF i = 1 THEN
\*\*                    [y \in Tran(x) |->
\*\*                        { m \in Tran(y) :
\*\*                            /\ SameBallot(m, y)
\*\*                            /\ OneB(m)
\*\*                            /\ Fresh000(alpha, m) }
\*\*                    ]
\*\*                ELSE [y \in Tran(x) |->
\*\*                    { m \in Tran(y) :
\*\*                        /\ SameBallot(m, y)
\*\*                        /\ [lr |-> alpha, q |-> { z.acc : z \in helper[i - 1][y] }] \in TrustLive }]
\*\*                )
\*\*        IN helper[d][x]
\*
\*\*    depthIdx(alpha, x) ==
\*\*        {d \in 1..N_L : [lr |-> alpha, q |-> {m.acc : m \in qd(alpha, x, d)}] \in TrustLive }
\*\*
\*\*    depth(alpha, x) ==
\*\*        Max({0} \cup depthIdx(alpha, x))
\*\*  <2> 
\*\*    BY DEF Max, depth, KnownMsgsSpec, TypeOK
\*<1> QED BY DEF TypeOK

\* TODO remove if not used; depends on KnownDepthPlusOne
\*LEMMA KnownDepthGtOneAux ==
\*    ASSUME NEW LA \in Learner \cup SafeAcceptor,
\*           NEW alpha \in Learner,
\*           KnownMsgsSpec,
\*           TypeOK
\*    PROVE  \A n \in Nat : \A M \in known_msgs[LA] :
\*             n = depth(alpha, M) /\ n >= 1 =>
\*             \E X \in Tran(M) :
\*                /\ depth(alpha, X) = 1
\*                /\ SameBallot(X, M)
\*PROOF
\*<1> DEFINE P(n) == \A M \in known_msgs[LA] :
\*             n = depth(alpha, M) /\ n >= 1 =>
\*             \E X \in Tran(M) :
\*                /\ depth(alpha, X) = 1
\*                /\ SameBallot(X, M)
\*<1> SUFFICES ASSUME NEW n \in Nat PROVE P(n) OBVIOUS
\*<1>0. P(0) OBVIOUS
\*<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
\*  <2> SUFFICES ASSUME NEW M \in known_msgs[LA],
\*                      k + 1 = depth(alpha, M)
\*               PROVE \E X \in Tran(M) :
\*                        /\ depth(alpha, X) = 1
\*                        /\ SameBallot(X, M)
\*      OBVIOUS
\*  <2> CASE k = 0
\*      BY Tran_refl DEF KnownMsgsSpec, TypeOK, SameBallot
\*  <2> CASE k > 0
\*    <3> PICK X_1 \in Tran(M) :
\*            /\ depth(alpha, X_1) = k
\*            /\ SameBallot(X_1, M)
\*        BY KnownDepthPlusOne DEF KnownMsgsSpec, TypeOK
\*    <3> QED BY <1>1, Tran_trans DEF KnownMsgsSpec, TypeOK, SameBallot
\*  <2> QED OBVIOUS
\*<1> HIDE DEF P
\*<1>3. QED BY <1>0, <1>1, NatInduction, Isa

\*LEMMA KnownDepthGtOne ==
\*    ASSUME NEW LA \in Learner \cup SafeAcceptor,
\*           NEW alpha \in Learner,
\*           NEW M \in known_msgs[LA],
\*           depth(alpha, M) >= 1
\*    PROVE  \E X \in Tran(M) : depth(alpha, X) = 1
\*PROOF
\*<1> QED

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

LEMMA QuorumNonTwoA ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           ~TwoA(x),
           NEW d \in Nat
    PROVE  qd(alpha, x, d) = {}
PROOF BY DEF qd

LEMMA QuorumCaseZero ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message
    PROVE  qd(alpha, x, 0) = {}
PROOF
<1> CASE TwoA(x)
  <2> DEFINE helper[i \in 0..0] == [y \in Message |-> {}]
  <2> 0 .. 0 = {0}
      OBVIOUS
  <2> qd(alpha, x, 0) = helper[0][x]
      BY DEF qd
  <2> QED OBVIOUS
<1> QED BY DEF qd

LEMMA QuorumCaseOne ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           TwoA(x)
    PROVE  qd(alpha, x, 1) = { y \in Tran(x) : /\ SameBallot(y, x)
                                               /\ OneB(x)
                                               /\ Fresh000(alpha, x) }
PROOF
<1> DEFINE helper[i \in 0..1] ==
        IF i = 0 THEN [y \in Message |-> {}]
        ELSE
            (IF i = 1 THEN
                [y \in Tran(x) |->
                    { m \in Tran(y) :
                        /\ SameBallot(m, y)
                        /\ OneB(m)
                        /\ Fresh000(alpha, m) }
                ]
            ELSE [y \in Tran(x) |->
                { m \in Tran(y) :
                    /\ SameBallot(m, y)
                    /\ [lr |-> alpha,
                        q |-> { z.acc : z \in helper[i - 1][m] }] \in TrustLive }]
            )
<1> qd(alpha, x, 1) = helper[1][x]
    BY DEF qd
<1> 1 \in 0..1
    OBVIOUS
<1> 0..1 = {0, 1}
    OBVIOUS
<1> helper[1] = [y \in Tran(x) |->
                                  {m \in Tran(y) :
                                     /\ SameBallot(m, y)
                                     /\ OneB(m)
                                     /\ Fresh000(alpha, m)}]
 OBVIOUS
<1> QED OBVIOUS

LEMMA QuorumProperty0 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           Proposal(x),
           NEW d \in Nat
    PROVE  qd(alpha, x, d) = {}
PROOF BY DEF qd, Proposal, OneA, TwoA

\* TODO useful lemma
LEMMA QuorumProperty1 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  \A y \in qd(alpha, x, d) :
            /\ y \in Tran(x)
            /\ ~Proposal(y)
PROOF
<1> CASE TwoA(x)
  <2> DEFINE helper[i \in 0..d] ==
        IF i = 0 THEN [y \in Message |-> {}]
        ELSE
            (IF i = 1 THEN
                [y \in Tran(x) |->
                    { m \in Tran(y) :
                        /\ SameBallot(m, y)
                        /\ OneB(m)
                        /\ Fresh000(alpha, m) }
                ]
            ELSE [y \in Tran(x) |->
                { m \in Tran(y) :
                    /\ SameBallot(m, y)
                    /\ [lr |-> alpha,
                        q |-> { z.acc : z \in helper[i - 1][m] }] \in TrustLive }]
            )
  <2> qd(alpha, x, d) = helper[d][x]
      BY DEF qd
  <2> CASE d = 0
      BY QuorumCaseZero
  <2> CASE d = 1
    <3> QED
  <2> SUFFICES ASSUME NEW y \in helper[d][x]
               PROVE  /\ y \in Tran(x)
                      /\ ~Proposal(y)
      OBVIOUS
  <2> CASE d = 1
      BY DEF Proposal, OneB
  <2> QED OBVIOUS
<1> QED BY DEF qd

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

\* TODO
\*LEMMA QuorumProperty3 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message,
\*           NEW x1 \in Message,
\*           NEW bal \in Ballot,
\*           B(x, bal),
\*           NEW d \in Nat, 0 < d,
\*           NEW d1 \in Nat, d < d1,
\*           x \in qd(alpha, x1, d1)
\*    PROVE  [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, x, d) }] \in TrustLive
\*PROOF
\*<1> QED

\* TODO
LEMMA QuorumProperty4 ==
    ASSUME NEW alpha \in Learner,
           NEW m \in Message,
           NEW d \in Nat, d >= 1,
           NEW d1 \in Nat, d1 >= d
    PROVE  [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, d1) }] \in TrustLive =>
           [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, d) }] \in TrustLive
PROOF
<1> QED

\* TODO
LEMMA QuorumProperty5 ==
    ASSUME NEW alpha \in Learner,
           NEW y \in Message,
           NEW d \in Nat, d >= 1,
           NEW x \in qd(alpha, y, d + 1)
    PROVE  [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, x, d)}] \in TrustLive
\* follows somehow from the definition:
\*                ELSE [y \in Tran(x) |->
\*                    { m \in Tran(y) :
\*                        /\ SameBallot(m, y)
\*                        /\ [lr |-> alpha,
\*                            q |-> { z.acc : z \in helper[i - 1][y] }] \in TrustLive }]

\* TODO move up
LEMMA HeterogeneousSpecCondProperties ==
    ASSUME NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW M \in Message,
           NEW V_M \in Value,
           NEW seq \in Seq(Whatever),
           NEW K \in Nat,
           K =< Len(seq),
           \A i \in 1..K : HeterogeneousSpecCond(alpha, bal, M, V_M, seq, i)
    PROVE  /\ \A i \in 1..K :
            /\ seq[i].m \in Tran(M)
            /\ seq[i].r \in Tran(M)
            /\ seq[i].s \in Tran(M)
           /\ \A i, j \in 1..K : i < j =>
                seq[j].r \in Tran(seq[i].r)
           /\ \A i, j \in 1..K : i < j /\ j < K =>
                /\ Con(alpha, seq[i].r) \in SUBSET Con(alpha, seq[j].r)
                /\ Con(alpha, seq[i].r) # Con(alpha, seq[j].r)
PROOF
<1> CASE K # 0
  <2> 1 \in 1..K
      OBVIOUS
  <2>1. seq[1].m \in Tran(M)
        BY DEF HeterogeneousSpecCond
  \* from cond 8
  <2>2. \A i \in 1..K :
            seq[i].r \in Tran(seq[i].m)
        BY WhateverSpec, QuorumProperty1 DEF HeterogeneousSpecCond
  \* from cond 4
  <2>3. \A i \in 2..K :
            seq[i].m \in Tran(seq[1].r)
        BY DEF HeterogeneousSpecCond
  \* from cond 9
  <2>4. \A i \in 1..K :
            seq[i].s \in Tran(seq[i].r)
        BY DEF HeterogeneousSpecCond
  <2>5. \A i, j \in 1..K : i < j => seq[j].r \in Tran(seq[i].r)
    <3> SUFFICES ASSUME NEW i \in 1..K,
                        NEW j \in 1..K,
                        i < j
                 PROVE seq[j].r \in Tran(seq[i].r)
        OBVIOUS
    <3> QED BY Tran_trans, WhateverSpec, QuorumProperty1 DEF HeterogeneousSpecCond
  <2>6. \A i, j \in 1..K : i < j =>
            Con(alpha, seq[i].r) \in SUBSET Con(alpha, seq[j].r)
        BY <2>5, WhateverSpec, ConTran
  <2>7. \A i, j \in 1..K : i < j /\ j < K =>
            Con(alpha, seq[i].r) # Con(alpha, seq[j].r)
    <3> SUFFICES ASSUME NEW i \in 1..K,
                        NEW j \in 1..K,
                        i < j /\ j < K
                 PROVE  Con(alpha, seq[i].r) # Con(alpha, seq[j].r)
        OBVIOUS
    <3> j - 1 \in 1..K
        OBVIOUS
    <3> j + 1 \in 1..K
        OBVIOUS
    <3> i =< j - 1
        OBVIOUS
    <3> Con(alpha, seq[j - 1].r) # Con(alpha, seq[j].r)
        BY DEF HeterogeneousSpecCond
    <3> Con(alpha, seq[j - 1].r) \in SUBSET Con(alpha, seq[j].r)
        BY <2>6
    <3> Con(alpha, seq[i].r) \in SUBSET Con(alpha, seq[j - 1].r)
        BY <2>6
    <3> QED BY Zenon
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Tran_trans
<1> QED OBVIOUS

\* TODO
LEMMA LearnersWellFormed ==
    ASSUME NEW m \in Message,
           WellFormed(m)
    PROVE  m.lrns # {} <=> TwoA(m)

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

\* TODO
\*LEMMA QdEq0 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW y \in Message,
\*           NEW d \in Nat,
\*           ~TwoA(y)
\*    PROVE  qd(alpha, y, d) = {}
\*PROOF
\*<1> QED BY DEF qd

\*LEMMA QdEq1 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW y \in Message,
\*           TwoA(y)
\*    PROVE  qd(alpha, y, 1) = { m \in Tran(y) :
\*                            /\ SameBallot(m, y)
\*                            /\ OneB(m)
\*                            /\ Fresh000(alpha, m) }
\*PROOF
\*<1> QED

LEMMA ChosenBalVal ==
    ASSUME BVal \in [Ballot -> Value],
           KnownMsgsSpec1,
           TypeOK,
           NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           ChosenIn(alpha, bal, val)
    PROVE  \A x \in Message : B(x, bal) => V(x, val)
PROOF
<1>1. PICK Q \in SUBSET Known2a(alpha, bal, val) :
        [lr |-> alpha, q |-> { mm.acc : mm \in Q }] \in TrustLive
    BY DEF ChosenIn
<1> PICK m \in Known2a(alpha, bal, val) : TRUE
    BY <1>1, TrustLiveNonEmpty
<1> m \in Message
    BY DEF KnownMsgsSpec1, TypeOK, Known2a
<1> B(m, bal) /\ V(m, val)
    BY DEF Known2a
<1> SUFFICES ASSUME NEW x \in Message, B(x, bal) PROVE V(x, val)
    OBVIOUS
<1> SameBallot(m, x)
    BY SameBallot_B
<1> QED BY SameBallotValue DEF SameValue

LEMMA YYY ==
    ASSUME BVal \in [Ballot -> Value],
           NEW alpha \in Learner, NEW beta \in Learner, NEW L0 \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           <<alpha, beta>> \in Ent,
           ChosenIn(alpha, bal, val),
           NEW M \in known_msgs[L0],
           NEW B_M \in Ballot,
           NEW V_M \in Value,
           bal < B_M,
           val # V_M,
           B(M, B_M),
           V(M, V_M),
           beta \in M.lrns,
           \* TODO
           MaxDepthSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           KnownMsgsPrevTranSpec,
           KnownMsgsSpec1,
           KnownMsgsSpec2,
           CaughtSpec,
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
    BY DEF KnownMsgsSpec2, TypeOK
<1> WellFormed(M)
    BY DEF KnownMsgsSpec2
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
        BY DEF Known2a, KnownMsgsSpec1
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
        BY DEF KnownMsgsSpec2
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
        BY DEF KnownMsgsSpec1
    <3> mb \in msgs
        BY DEF KnownMsgsSpec1
    <3> ~OneA(ma)
         BY MessageTypeSpec DEF Known2a
    <3> ~OneA(mb)
         BY QuorumProperty2, MessageTypeSpec
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
  <2> WITNESS [x \in 1..1 |-> w0] \in [1..1 -> Whatever]
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
  <2> k \in 1..k
      OBVIOUS
  <2> PICK seq \in [1 .. k -> Whatever]:
            \A x \in 1 .. k:
                HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x)
      OBVIOUS
  <2> seq \in Seq(Whatever)
      BY SeqDef
  <2> k =< Len(seq)
      OBVIOUS
  <2> DEFINE S ==
        { w \in Whatever : HeterogeneousSpecCond(alpha, bal, M, V_M, Append(seq, w), k + 1) }
  <2> S # {}
    <3> \A x \in 1 .. k : HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
        BY DEF HeterogeneousSpecCondMin
    <3> HeterogeneousSpecCond(alpha, bal, M, V_M, seq, k)
        OBVIOUS
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
        BY HeterogeneousSpecCondProperties
    \* From the previous, we conclude
    <3> \A x \in 1..k : WellFormed(seq[x].r)
        BY DEF KnownMsgsSpec2
    <3> \A x \in 1..k : V(seq[x].m, V_M)
        BY DEF HeterogeneousSpecCond
    <3> V(seq[k].m, V_M)
        OBVIOUS
    <3> WellFormed(seq[k].s)
        BY DEF KnownMsgsSpec2
    <3> B(seq[k].s, bal)
        BY DEF HeterogeneousSpecCond
    \* ..therefore
    <3> V(seq[k].s, val)
        BY ChosenBalVal
    <3> seq[k].r \in known_msgs[L0]
        BY DEF KnownMsgsSpec2
    <3> V(seq[k].r, V_M)
    \* Follows from
\*        \* cond 8:
\*        /\ r \in qd(gamma, m, 1)
\*        \* cond 14:
\*        /\ V(m, V_M)
      <4> B(seq[k].r, seq[k].B_m)
          OBVIOUS \* proven above
      <4> B(seq[k].m, seq[k].B_m)
          OBVIOUS
      <4> SameBallot(seq[k].r, seq[k].m)
          BY B_func DEF SameBallot
      \* r is from quorum of m, therefore r is of the same ballot as m, therefore the value of r equals that of m (which is V_M)
       <4> QED BY SameBallotValue DEF SameValue
    \* goal: to show V(s_k) # V(r_k)
    <3> seq[k].s \in Tran(seq[k].r)
        BY DEF HeterogeneousSpecCond

    <3> alpha \in seq[k].s.lrns
      \* By cond 12 we have
      <4> [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq[k].s, maxDepth(alpha) - k + 1) }] \in TrustLive
          BY DEF HeterogeneousSpecCond
      <4> maxDepth(alpha) - k + 1 >= 1
          OBVIOUS
      \* Therefore, by QuorumProperty4,
      <4> [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq[k].s, 1) }] \in TrustLive
          BY QuorumProperty4
      \* ..which by definition of WellFormed-ness for seq[k].s results in
      <4> QED BY DEF WellFormed

    <3> \A i \in 1..k : seq[i].r \in Tran(seq[i].m)
      <4> SUFFICES ASSUME NEW i \in 1..k PROVE seq[i].r \in Tran(seq[i].m)
          OBVIOUS
      <4> seq[i].r \in qd(seq[i].gamma, seq[i].m, 1)
          BY DEF HeterogeneousSpecCond
      <4> qd(seq[i].gamma, seq[i].m, 1) \in SUBSET Tran(seq[i].m)
          BY QuorumProperty1
      <4> QED OBVIOUS

    \* We prove the following useful property of alpha and gamma:
    <3>ag \A i \in 1..k :
            alpha \in Con(seq[k].gamma, seq[k].r)
      <4> CASE k = 1
        <5> <<alpha, seq[k].gamma>> \in Ent
            BY DEF HeterogeneousSpecCond
        <5> QED BY ConnectedSym, EntConnected
      <4> CASE k > 1
        <5> seq[k - 1].r \in Message
             BY WhateverSpec
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
         <5> QED BY ConnectedSym
\*         <5>1. alpha \in Con(seq[k].gamma, seq[k].r)
      <4> QED OBVIOUS

    \* We show that the set of 2a affecting the value of fresh r is non-empty, with s being its element
    <3> DEFINE r_fresh_set == { mm \in Tran(seq[k].r) : D(seq[k].gamma, seq[k].r, mm) }
    <3>9. seq[k].s \in r_fresh_set
      <4> SUFFICES D(seq[k].gamma, seq[k].r, seq[k].s)
          BY DEF HeterogeneousSpecCond
      <4> SUFFICES alpha \in Con(seq[k].gamma, seq[k].r)
          BY DEF D
      <4> QED BY <3>ag

    <3>10. r_fresh_set # {}
      BY <3>9

    \* Since r is known, all the elements of the fresh set are known messages
    <3>11. \A x \in r_fresh_set : WellFormed(x)
           BY DEF KnownMsgsSpec2
    <3>12. r_fresh_set \in SUBSET Message
           BY DEF KnownMsgsSpec2, TypeOK
    <3>13. r_fresh_set \in SUBSET known_msgs[L0]
           BY DEF KnownMsgsSpec2
    <3>14. IsFiniteSet(r_fresh_set)
      <4> IsFiniteSet(known_msgs[L0])
          BY DEF KnownMsgsSpec1
      <4> QED BY <3>13, FS_Subset
    <3>15. Latest(r_fresh_set) # {}
           BY <3>10, <3>11, <3>12, <3>14, LatestNonEmpty

    \* Below, we construct m0, B_m0, gamma0, r0, s0 which are fields of seq[k+1]
    \* Define m0 as a latest fresh message of r
    <3> PICK m0 \in Latest(r_fresh_set) : TRUE
        BY <3>15, LatestSubset

    \* m0 has the following properties
    <3> WellFormed(m0)
        BY LatestSubset, <3>11, <3>12
    <3> m0 \in Message
        BY LatestSubset, <3>12
    <3> m0 \in known_msgs[L0]
        BY LatestSubset, <3>12, <3>13
    <3> m0 \in Tran(seq[k].r)
        BY LatestSubset, <3>12
    <3> m0.lrns \cap Con(seq[k].gamma, seq[k].r) # {}
        BY LatestSubset DEF D, KnownMsgsSpec2, TypeOK
    <3> TwoA(m0)
        BY LearnersWellFormed
    <3> m0 # seq[k].r
        BY MessageTypeSpec
    <3> ~Proposal(m0)
        BY MessageTypeSpec DEF Proposal, OneA

    \* m0 has a ballot number:
    <3> PICK B_m0 \in Ballot : B(m0, B_m0)
        BY DEF WellFormed

    \* By construction of m0 and definition of Fresh000, m0 and r have the same value
    <3> SameValue(m0, seq[k].r)
        BY DEF Fresh000
    \* ..which is V_M
    <3> V(m0, V_M)
        BY DEF SameValue

    <3> bal < B_m0 \* Property (1)
      \* Since m0 is a latest message, we get non-strict inequality
      <4> bal =< B_m0
          BY <3>9 DEF Latest
      <4> SUFFICES ASSUME bal = B_m0 PROVE FALSE
          BY DEF Ballot
      \* now we use the facts that m0 is of value V_M and s has value val, which are not equal by the lemma assumption 
      <4> QED BY SameBallotValue, V_def, V_func DEF SameBallot, SameValue

    <3> B_m0 < seq[k].B_m \* Property (2)
        BY WellFormedCondition111 DEF OneA, Proposal

    \* Auxiliary clause that proves <4>4 below.
    <3>cond4. \A i \in 1..k : m0 \in Tran(seq[i].r)
      \* We have shown above that
      \* By construction of m0,
      <4> SUFFICES \A i \in 1..k - 1 : m0 \in Tran(seq[i].r)
          OBVIOUS
      \* By IH, we have
      <4> \A i \in 1..k - 1 : seq[k].m \in Tran(seq[i].r)
          BY DEF HeterogeneousSpecCond
      \* First,
      <4> m0 \in Tran(seq[k].m)
        \* By construction of m0 and the fact that seq[k].r \in Tran(seq[k].m), we conclude
          BY LatestSubset, Tran_trans, <3>12
      \* which by transitivity of Tran and the fact that all are soundly typed
      <4> \A i \in 1..k - 1 : seq[i].r \in Message
          BY WhateverSpec
      \* gives
      <4> QED BY Tran_trans

    \* By lemma about Con compatibility, we prove that the gamma and alpha Con-sets are equal
    <3> Con(seq[k].gamma, seq[k].r) = Con(alpha, seq[k].r)
        BY <3>ag, Con_compat, ConnectedSym

    \* Now define gamma[k + 1]:
    <3> PICK gamma0 \in m0.lrns \cap Con(alpha, seq[k].r) : TRUE
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
        BY DEF KnownMsgsSpec2
    <3> Q2 \in SUBSET Tran(seq[k].r)
        BY Tran_trans
    <3> Q2 # {}
        BY TrustLiveNonEmpty
    \* Therefore,
    <3> TwoA(m0)
        BY MessageTypeSpec DEF qd

    \* Auxiliary clause that proves <4>3 below.
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

    \* Using, Q2 defined above, we now define s0 and r0
    \* Define Q1 as a quorum of s[k] depth (maxDepth(alpha) - k + 1)
    <3> maxDepth(alpha) - k + 1 \in Nat
        OBVIOUS
    <3> DEFINE Q1 == qd(alpha, seq[k].s, maxDepth(alpha) - k + 1)
    <3> [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
        BY DEF HeterogeneousSpecCond \* cond 12
    <3> Q1 \in SUBSET Tran(seq[k].s)
        BY QuorumProperty1
    \* Therefore..
    <3> Q1 \in SUBSET Tran(seq[k].r)
        BY Tran_trans DEF HeterogeneousSpecCond \* cond 9

    <3> PICK p \in Acceptor, s0 \in Q1, r0 \in Q2 :
            /\ p \notin Caught(seq[k].r)
            /\ s0.acc = p
            /\ r0.acc = p
      <4> HIDE DEF Q2, Q1
      <4> QED BY EntLiveQuorumConIntersection
    <3> r0 \in Message /\ s0 \in Message
        BY DEF KnownMsgsSpec2, TypeOK
    <3> ~Proposal(s0)
        BY QuorumProperty1
    <3> ~Proposal(r0)
        BY QuorumProperty1
    <3> B(r0, B_m0)
        BY QuorumProperty2
    <3> B(s0, bal)
        BY QuorumProperty2

    <3> s0 \in Tran(r0)
        \* From bal < B_m0 (Property 1), we conclude
        BY NotCaughtXXX, TranBallot DEF Ballot \* TODO avoid unfolding Ballot here and elsewhere by formulating that the order is total
    <3> DEFINE w0 == [m |-> m0, B_m |-> B_m0, r |-> r0, s |-> s0, gamma |-> gamma0]
    <3> w0 \in Whatever
        BY DEF Whatever
    <3> w0.B_m \in Ballot
        OBVIOUS
    <3> DEFINE seq0 == Append(seq, w0)
    <3>100. HeterogeneousSpecCond(alpha, bal, M, V_M, seq0, k + 1)
      <4> (k + 1) - 1 = k
          OBVIOUS
      <4>0. B(seq0[k + 1].m, seq0[k + 1].B_m)
            OBVIOUS
      <4>1. k + 1 # 0
            OBVIOUS
      <4>2. bal < seq0[k + 1].B_m \* property bal < B_m0 above
            OBVIOUS
      <4>3. \A i \in 1..((k + 1) - 1) : seq0[k + 1].B_m < seq0[i].B_m
            BY <3>cond3, AppendProperties
      <4>4. \A i \in 1..(k + 1) - 1 : seq0[k + 1].m \in Tran(seq0[i].r)
            BY <3>cond4, AppendProperties
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
        \* Then we conclude that, by construction, seq[k].B_m =< B_m0 which contradicts <4>3
        \* Isaac: we need to find the earliest k such that
        \* gamma0 \in Con(alpha, seq[k].r)
        \* Denote it k*.
        \* CASE k* = k: implies <4>6 directly.
        \* CASE k* < k: we prove FALSE.
        \* We construct seq_bad as seq[k* + 1 |-> w_bad], with w_bad defined as above.
        \* We prove then that HeterogeneousSpecCond(..., seq_bad), which implies that
        \* seq[k* + 1].B_m =< B_m0
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
        <5> k_star \in Nat
            OBVIOUS
        <5>1. CASE k_star = k
              BY <5>1 DEF SmallestIndex
        <5>2. CASE k_star < k
          <6> k_star + 1 \in Nat
              OBVIOUS
          <6> k_star + 1 =< k
              BY <5>2
          <6> k_star + 1 > 1
              OBVIOUS
          <6> (k_star + 1) - 1 = k_star
              OBVIOUS
          <6> k_star \in 1..k
              OBVIOUS
          <6> 1..k_star \in SUBSET 1..k 
              OBVIOUS
          <6> seq[k_star].r \in Message
              BY DEF WhateverSpec
          <6> B(seq[k_star].s, bal)
              BY DEF HeterogeneousSpecCond
\*          <6> HeterogeneousSpecCond(alpha, bal, M, V_M, seq, k_star + 1)
\*              OBVIOUS
          <6> HeterogeneousSpecCond(alpha, bal, M, V_M, seq, k_star)
              OBVIOUS
\*          <6> maxDepth(alpha) - (k_star + 1) + 1 = maxDepth(alpha) - k_star
\*              OBVIOUS
          <6> k_star =< maxDepth(alpha)
              OBVIOUS
          <6> DEFINE Q1_star == qd(alpha, seq[k_star].s, (maxDepth(alpha) - k_star + 1))
          <6> [lr |-> alpha, q |-> { mm.acc : mm \in Q1_star }] \in TrustLive
              BY DEF HeterogeneousSpecCond
          <6> Q1_star \in SUBSET Tran(seq[k_star].s)
              BY QuorumProperty1
          \* ..from which we conclude
          <6> Q1_star \in SUBSET Tran(seq[k_star].r)
              BY Tran_trans DEF HeterogeneousSpecCond
          <6> gamma0 \in Con(alpha, seq[k_star].r)
              BY DEF SmallestIndex
          \* We DEFINE Q2 == qd(gamma0, m0, 1)
          \* and <3>cond4 \A i \in 1..k : m0 \in Tran(seq[i].r)
          <6> Q2 \in SUBSET Tran(seq[k_star].r)
              BY QuorumProperty1, <3>cond4, Tran_trans

          <6> PICK p_star \in Acceptor, s_star \in Q1_star, r_star \in Q2 :
                /\ p_star \notin Caught(seq[k_star].r)
                /\ s_star.acc = p_star
                /\ r_star.acc = p_star
            <7> HIDE DEF Q2, Q1_star
            <7> QED BY EntLiveQuorumConIntersection
          <6> s_star \in Message
              BY Tran_Message
          <6> r_star \in Message
              BY Tran_Message
          <6> B(r_star, B_m0)
              BY QuorumProperty2
          <6> B(s_star, bal)
              BY QuorumProperty2
          <6> ~Proposal(r_star)
              BY QuorumProperty1
          <6> ~Proposal(s_star)
              BY QuorumProperty1

          <6> seq[k_star].r \in known_msgs[L0]
              BY DEF KnownMsgsSpec2
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

          <6>0. \A x \in 1..k_star + 1 : HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
                OBVIOUS
          <6>1. \A x \in 1..k_star : HeterogeneousSpecCond(alpha, bal, M, V_M, seq_star, x)
            <7> HIDE DEF seq_star
            <7> QED BY <6>0, HeterogeneousSpecCondCongr
          <6>2. HeterogeneousSpecCond(alpha, bal, M, V_M, seq_star, k_star + 1)
            <7>0. B(seq_star[k_star + 1].m, seq_star[k_star + 1].B_m)
                  OBVIOUS
            <7>2. bal < seq_star[k_star + 1].B_m
                  OBVIOUS
                    \* cond 3:
\*        /\ x > 1 => \A i \in 1..(x - 1) : B_m < seq[i].B_m
            <7>3. \A i \in 1..(k_star + 1) - 1 : seq_star[k_star + 1].B_m < seq_star[i].B_m
                  BY <3>cond3
            <7>4. \A i \in 1..(k_star + 1) - 1 : seq_star[k_star + 1].m \in Tran(seq_star[i].r)
                  BY <3>cond4
            <7>5. seq_star[k_star + 1].gamma \in Con(alpha, seq_star[k_star].r)
                  OBVIOUS

            \* BY definition:
\*            <5> DEFINE R(w) == gamma0 \in Con(alpha, w.r)
\*            <5> PICK k_star \in 1..k : SmallestIndex(seq, R, k_star)
            \* Hence
            <7>6. k_star + 1 > 2 => seq_star[k_star + 1].gamma \notin Con(alpha, seq_star[k_star - 1].r)
                  BY DEF SmallestIndex
            <7>7. seq_star[k_star + 1].gamma \in seq_star[k_star + 1].m.lrns
                  OBVIOUS
            <7>8. seq_star[k_star + 1].r \in qd(seq_star[k_star + 1].gamma, seq_star[k_star + 1].m, 1)
                  OBVIOUS
            <7>9. seq_star[k_star + 1].s \in Tran(seq_star[k_star + 1].r)
                  BY NotCaughtXXX, TranBallot DEF Ballot
            <7>10. seq_star[k_star + 1].s \in Tran(seq_star[k_star].s)
                   OBVIOUS
            <7>11. seq_star[k_star + 1].r.acc = seq_star[k_star + 1].s.acc
                   OBVIOUS
            <7>12. k_star + 1 =< maxDepth(alpha) =>
                    [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq_star[k_star + 1].s, maxDepth(alpha) - (k_star + 1) + 1) }] \in TrustLive
              \* By definition of s_star, s_star \in Q1_star, with Q1_star == qd(alpha, seq[k_star].s, (maxDepth(alpha) - k_star + 1))
              <8> QED BY QuorumProperty5
            <7>13. B(seq_star[k_star + 1].s, bal)
                   OBVIOUS
            <7>14. V(seq_star[k_star + 1].m, V_M)
                   OBVIOUS
            <7>15. k_star + 1 = 1 => seq_star[k_star + 1].m \in Tran(M)
                   OBVIOUS
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
                BY <3>cond3
          <6>4. HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, k_star + 1)
                OBVIOUS
          <6>5. \A x \in 1..k_star + 1 : HeterogeneousSpecCond(alpha, bal, M, V_M, seq_star, x)
                BY <6>1, <6>2
          <6> HIDE DEF w_star
          <6> DEFINE seq1 == [seq EXCEPT ![k_star + 1] = w_star]
          <6> seq1 \in Seq(Whatever)
              OBVIOUS
          <6> \A i \in 1..k_star + 1 : seq1[i] = seq_star[i]
              OBVIOUS
          <6>6. HeterogeneousSpecCond(alpha, bal, M, V_M, seq1, k_star + 1)
            <7> HIDE DEF seq1
            <7> HIDE DEF seq_star
            <7> k_star + 1 \in 1..k_star + 1
                OBVIOUS
            <7> QED BY <6>5, HeterogeneousSpecCondCongr
          <6>7. seq[k_star + 1].B_m =< seq1[k_star + 1].B_m
                BY <6>4, <6>6 DEF HeterogeneousSpecCondMin
          <6>8. seq_star[k_star + 1] = seq1[k_star + 1]
                OBVIOUS
          <6> HIDE DEF seq1
          <6> HIDE DEF seq_star
          <6> QED BY <6>8, <6>7, <6>3, WhateverSpec DEF Ballot
        <5> QED BY <5>1, <5>2

      <4>7. seq0[k + 1].gamma \in seq0[k + 1].m.lrns
            OBVIOUS
      <4>8. seq0[k + 1].r \in qd(seq0[k + 1].gamma, seq0[k + 1].m, 1)
            OBVIOUS
      <4>9. seq0[k + 1].s \in Tran(seq0[k + 1].r)
            OBVIOUS
      <4>10. seq0[k + 1].s \in Tran(seq0[(k + 1) - 1].s)
             OBVIOUS
      <4>11. seq0[k + 1].r.acc = seq0[k + 1].s.acc
             OBVIOUS
      <4>12. k + 1 =< maxDepth(alpha) =>
                [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, seq0[k + 1].s, maxDepth(alpha) - (k + 1) + 1) }] \in TrustLive
             BY QuorumProperty5
      <4>13. B(seq0[k + 1].s, bal)
             OBVIOUS
      <4>14. V(seq0[k + 1].m, V_M)
             OBVIOUS
      <4> HIDE DEF seq0
      <4> QED BY <4>0, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF HeterogeneousSpecCond
    <3> QED BY <3>100

  <2> PICK w0 \in S : \A z \in S : w0.B_m =< z.B_m
      BY WhateverMin
  <2> DEFINE seq0 == Append(seq, w0)
  <2> seq0[k + 1] = w0
      OBVIOUS
  <2> seq0 \in [1..k + 1 -> Whatever]
      BY AppendProperties 
  <2> Len(seq0) = k + 1
      BY AppendProperties
  <2> ASSUME NEW x \in 0..k PROVE seq0[k] = seq[k]
      BY AppendProperties
  <2> \A z \in Whatever : [seq0 EXCEPT ![k + 1] = z] = Append(seq, z)
      BY Isa, AppendProperties
  <2> \A z \in Whatever : [seq0 EXCEPT ![k + 1] = z][k + 1] = z
      OBVIOUS
  <2> HeterogeneousSpecCond(alpha, bal, M, V_M, seq0, k + 1)
      OBVIOUS
  <2> HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq0, k + 1)
      BY DEF HeterogeneousSpecCondMin
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
<1>3. QED BY <1>0, <1>1, INDUCTION_SCHEME, Blast

\* TODO rename and prove
LEMMA maxDepth_XXX ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in Seq(Message),
           alpha \in Con(alpha, seq[Len(seq)]),
           \A i, j \in 1..Len(seq) : i < j =>
               /\ seq[i] \in Tran(seq[j])
               /\ Con(alpha, seq[i]) # Con(alpha, seq[j])
    PROVE  Len(seq) =< maxDepth(alpha)

\*    maxDepth(alpha) ==
\*        LET I == { n \in 1..N_L :
\*                    \E f \in [1..n -> Message] :
\*                        /\ alpha \in Con(alpha, f[n])
\*                        /\ \A i, j \in 1..n : i < j =>
\*                               /\ f[i] \in Tran(f[j])
\*                               /\ Con(alpha, f[i]) # Con(alpha, f[j]) }
\*        IN Max(I)

-----------------------------------------------------------------------------

\*LEMMA Union_cup ==
\*    ASSUME NEW F(_),
\*           NEW X,
\*           NEW Y,
\*           NEW Z
\*    PROVE  UNION {F(x) : x \in X \cup Y \cup Z} = (UNION {F(x) : x \in X}) \cup (UNION {F(y) : y \in Y}) \cup (UNION {F(z) : z \in Z})
\*PROOF BY Zenon

LEMMA ZZZ ==
    ASSUME BVal \in [Ballot -> Value],
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW bal \in Ballot,
           NEW val \in Value,
           ChosenIn(alpha, bal, val),
           NEW L0 \in Learner,
           NEW M \in known_msgs[L0],
           TwoA(M),
           NEW V_M \in Value,
           NEW seq \in [1 .. maxDepth(alpha) + 1 -> Whatever],
           \A x \in 1 .. maxDepth(alpha) + 1 :
            HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x),
           KnownMsgsSpec1,
           KnownMsgsSpec2,
           MaxDepthSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           KnownMsgsPrevTranSpec,
           CaughtSpec,
           TypeOK
    PROVE  FALSE
PROOF
<1> M \in Message
    BY DEF KnownMsgsSpec2, TypeOK
<1> WellFormed(M)
    BY DEF KnownMsgsSpec2
<1> ~OneA(M)
    BY MessageTypeSpec
<1> maxDepth(alpha) \in Nat
    BY DEF MaxDepthSpec
<1> maxDepth(alpha) + 1 > maxDepth(alpha)
    OBVIOUS
<1> maxDepth(alpha) + 1 \in 1..maxDepth(alpha) + 1
    OBVIOUS
<1> seq \in Seq(Whatever)
    BY SeqDef
<1> Len(seq) >= 2
    BY DEF MaxDepthSpec
<1> Len(seq) = maxDepth(alpha) + 1
    OBVIOUS
<1> Len(seq) \in Nat
    OBVIOUS
<1> \A x \in 1..maxDepth(alpha) + 1 :
        HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
    BY DEF HeterogeneousSpecCondMin
<1> HeterogeneousSpecCond(alpha, bal, M, V_M, seq, maxDepth(alpha) + 1)
    OBVIOUS

\*    maxDepth(alpha) ==
\*        LET I == { n \in 1..N_L :
\*                    \E f \in [1..n -> Message] :
\*                        \A i, j \in 1..n : i < j =>
\*                               /\ f[i] \in Tran(f[j])
\*                               /\ Con(alpha, f[i]) # Con(alpha, f[j])}
\*        IN Max(I)
\* mseq :
\* mseq[1] = ...
\* mseq[2] = seq[maxdep(alpha) + 1].m
\* mseq[3] = seq[maxdep(alpha) + 0].m

\*HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, x) ==
\*    /\ HeterogeneousSpecCond(alpha, bal, M, V_M, seq, x)
\*    /\ \A z \in Whatever:
\*        LET seq1 == [seq EXCEPT ![x] = z] IN
\*        HeterogeneousSpecCond(alpha, bal, M, V_M, seq1, x) =>
\*        seq[x].B_m =< seq1[x].B_m



\*************** PROOF SKETCH
\*<1> DEFINE mseq == Reverse([x \in 1..maxDepth(alpha) + 1 |-> seq[x].m])
\* Claim 1. seq[2].gamma is not entangled with alpha or beta
\* Follows from minimality of seq[2]
\* Claim 2. seq[2].gamma \in Con(alpha) in all the seq[x].m for x >= 2
\*
\* We need to create a message M0 such that:
\* 1) M \in Tran(M0)
\* 2) all the byzantine acceptors are caught as of M0

\* Then we append M0 to the sequence: seq[2].gamma \notin Con(alpha, M0), from Claim 1.
\* Using this fact and cond5 and cond6, we can prove that every message in mseq has a different set of learners connected to alpha,
\* and every element in the list mseq is in the transitive history of the next element
\* which contradicts the maximality of maxDepth.
<1> PICK safe \in SafeAcceptor : TRUE
    BY SafeAcceptorNonTrivial

<1> PICK bal1 \in Ballot, bal2 \in Ballot : bal1 # bal2
    BY DEF Ballot
<1> DEFINE v1 == BVal[bal1]
<1> v1 \in Value
    OBVIOUS
<1> DEFINE v2 == BVal[bal2]
<1> v2 \in Value
    OBVIOUS

<1> DEFINE p1 == [ type |-> "1a", bal |-> bal1, prev |-> NoMessage, refs |-> {} ]
<1> p1 \in Message /\ OneA(p1) /\ p1.bal = bal1
    BY OneA_Message
<1> B(p1, bal1)
    BY B_1a
<1> Tran(p1) = {p1}
    BY Tran_1a
<1> PrevTran(p1) = {p1}
    BY PrevTran_eq
<1> DEFINE p2 == [ type |-> "1a", bal |-> bal2, prev |-> NoMessage, refs |-> {} ]
<1> p2 \in Message /\ OneA(p2) /\ p2.bal = bal2
    BY OneA_Message
<1> B(p2, bal2)
    BY B_1a
<1> Tran(p2) = {p2}
    BY Tran_1a
<1> PrevTran(p2) = {p2}
    BY PrevTran_eq

<1> p1 # p2
    OBVIOUS
<1> HIDE DEF p1
<1> HIDE DEF p2

<1> DEFINE oneb_1 == {[ type |-> "1b", acc |-> fake, prev |-> p1, refs |-> {p1}, lrns |-> {} ] : fake \in FakeAcceptor }
<1> oneb_1 \in SUBSET { mm \in Message : OneB(mm) }
  <2> IsFiniteSet({p1})
      BY FS_Singleton
  <2> QED BY Isa, OneB_Message_bis DEF Acceptor
<1> IsFiniteSet(oneb_1)
  <2> PICK fseq \in Seq(FakeAcceptor) :
        \A f \in FakeAcceptor : \E n \in 1..Len(fseq) : fseq[n] = f
      BY FakeAcceptorFinite DEF IsFiniteSet
  <2> DEFINE mseq == [ x \in 1..Len(fseq) |->
                        [ type |-> "1b", acc |-> fseq[x], prev |-> p1, refs |-> {p1}, lrns |-> {} ]
                     ]
  <2> mseq \in Seq(oneb_1)
      OBVIOUS
  <2> Len(mseq) = Len(fseq)
      OBVIOUS
  <2> \A m \in oneb_1 : \E n \in 1..Len(mseq) : mseq[n] = m
      OBVIOUS
  <2> QED BY DEF IsFiniteSet
<1> \A m1 \in oneb_1 : B(m1, bal1)
  <2> SUFFICES ASSUME NEW f \in FakeAcceptor
               PROVE  B([ type |-> "1b", acc |-> f, prev |-> p1, refs |-> {p1}, lrns |-> {} ], bal1)
      OBVIOUS
  <2> DEFINE oneb_fake == [ type |-> "1b", acc |-> f, prev |-> p1, refs |-> {p1}, lrns |-> {} ]
  <2> oneb_fake \in oneb_1
      OBVIOUS
  <2> ~OneA(oneb_fake)
      BY MessageTypeSpec
  <2> Tran(oneb_fake) = {oneb_fake, p1}
      BY Tran_eq
  <2> Get1a(oneb_fake) = {p1}
    <3> HIDE DEF oneb_fake
    <3> QED BY DEF Get1a, Ballot
  <2> QED BY DEF B
<1> \A m1 \in oneb_1 : Tran(m1) = {m1, p1}
    BY Tran_eq, Tran_1a
<1> \A m1 \in oneb_1 : m1.acc \in FakeAcceptor
    OBVIOUS

\*<1> ASSUME NEW F(_),
\*           NEW X,
\*           NEW x \in X
\*    PROVE  (UNION {F(y) : y \in {x}}) = F(x)
\*    BY Zenon

\*<1> ASSUME NEW F(_),
\*           NEW X,
\*           NEW e \in X,
\*           NEW Y,
\*           NEW Z
\*    PROVE  UNION {F(x) : x \in {e} \cup Y \cup Z} = F(e) \cup (UNION {F(y) : y \in Y}) \cup (UNION {F(z) : z \in Z})
\*    BY SlowZenon

<1> DEFINE oneb_2 == {[ type |-> "1b", acc |-> fake, prev |-> p2, refs |-> {p2}, lrns |-> {} ] : fake \in FakeAcceptor }
<1> oneb_2 \in SUBSET { mm \in Message : OneB(mm) }
  <2> IsFiniteSet({p2})
      BY FS_Singleton
  <2> QED BY Isa, OneB_Message_bis DEF Acceptor
<1> IsFiniteSet(oneb_2)
  <2> PICK fseq \in Seq(FakeAcceptor) :
        \A f \in FakeAcceptor : \E n \in 1..Len(fseq) : fseq[n] = f
      BY FakeAcceptorFinite DEF IsFiniteSet
  <2> DEFINE mseq == [ x \in 1..Len(fseq) |->
                        [ type |-> "1b", acc |-> fseq[x], prev |-> p2, refs |-> {p2}, lrns |-> {} ]
                     ]
  <2> mseq \in Seq(oneb_2)
      OBVIOUS
  <2> Len(mseq) = Len(fseq)
      OBVIOUS
  <2> \A m \in oneb_2 : \E n \in 1..Len(mseq) : mseq[n] = m
      OBVIOUS
  <2> QED BY DEF IsFiniteSet
<1> \A m2 \in oneb_2 : B(m2, bal2)
  <2> SUFFICES ASSUME NEW f \in FakeAcceptor
               PROVE  B([ type |-> "1b", acc |-> f, prev |-> p2, refs |-> {p2}, lrns |-> {} ], bal2)
      OBVIOUS
  <2> DEFINE oneb_fake == [ type |-> "1b", acc |-> f, prev |-> p2, refs |-> {p2}, lrns |-> {} ]
  <2> oneb_fake \in oneb_2
      OBVIOUS
  <2> ~OneA(oneb_fake)
      BY MessageTypeSpec
  <2> Tran(oneb_fake) = {oneb_fake, p2}
      BY Tran_eq
  <2> Get1a(oneb_fake) = {p2}
    <3> HIDE DEF oneb_fake
    <3> QED BY DEF Get1a, Ballot
  <2> QED BY DEF B
<1> \A m2 \in oneb_2 : Tran(m2) = {m2, p2}
    BY Tran_eq, Tran_1a
<1> \A m2 \in oneb_2 : m2.acc \in FakeAcceptor
    OBVIOUS

<1> DEFINE M0 == [ type |-> "2a", acc |-> M.acc, prev |-> M, refs |-> {M} \cup oneb_1 \cup oneb_2, lrns |-> {} ]

<1> M0 \in Message /\ TwoA(M0)
  <2> M.acc \in Acceptor
      BY MessageSpec DEF TwoA
  <2> IsFiniteSet({M} \cup oneb_1 \cup oneb_2)
      BY FS_Union, FS_Singleton
  <2> HIDE DEF oneb_1, oneb_2
  <2> QED BY Zenon, TwoA_Message_bis
<1> M \in Tran(M0)
    BY Message_ref_Tran
<1> DEFINE SingletonM == {M}
<1> M0.acc = M.acc
    OBVIOUS
<1> M0.refs = SingletonM \cup oneb_1 \cup oneb_2
    OBVIOUS
<1> M0.prev = M
    OBVIOUS

<1>M0_tran. Tran(M0) \subseteq { M0, p1, p2 } \cup Tran(M) \cup oneb_1 \cup oneb_2
\*  <2> (UNION { Tran(r) : r \in M0.refs }) =
\*        (UNION { Tran(r) : r \in SingletonM }) \cup (UNION { Tran(x) : x \in oneb_1 }) \cup (UNION { Tran(y) : y \in oneb_2 })
\*    <3> HIDE DEF M0, oneb_1, oneb_2, SingletonM
\*    <3> QED OBVIOUS \*BY Union_cup \* TODO clean
  <2> HIDE DEF M0
  <2> Tran(M0) = {M0} \cup Tran(M) \cup (UNION { Tran(x) : x \in oneb_1 }) \cup (UNION { Tran(y) : y \in oneb_2 })
    <3> HIDE DEF oneb_1, oneb_2
    <3> QED BY Tran_eq
  <2> QED OBVIOUS

<1>M0_prevtran. PrevTran(M0) = {M0} \cup PrevTran(M)
  <2> HIDE DEF M0
  <2> QED BY PrevTran_eq, NoMessageIsNotAMessage

<1>caught_fake. FakeAcceptor \in SUBSET Caught(M0)
  <2> SUFFICES ASSUME NEW fake \in FakeAcceptor
               PROVE  fake \in Caught(M0)
      OBVIOUS
  <2> DEFINE proof1 == [ type |-> "1b", acc |-> fake, prev |-> p1, refs |-> {p1}, lrns |-> {} ]
  <2> DEFINE proof2 == [ type |-> "1b", acc |-> fake, prev |-> p2, refs |-> {p2}, lrns |-> {} ]
  <2> proof1 # proof2
      OBVIOUS
  <2> ~Proposal(proof1)
      BY DEF Proposal
  <2> ~Proposal(proof2)
      BY DEF Proposal
  <2> proof1 \in oneb_1
      OBVIOUS
  <2> proof2 \in oneb_2
      OBVIOUS
  <2> PrevTran(proof1) = { proof1, p1 }
      BY PrevTran_eq, NoMessageIsNotAMessage
  <2> PrevTran(proof2) = { proof2, p2 }
      BY PrevTran_eq, NoMessageIsNotAMessage
  <2> proof1 \in Tran(M0)
    <3> HIDE DEF oneb_1, oneb_2, proof2
    <3> QED BY Message_ref_Tran
  <2> proof2 \in Tran(M0)
    <3> HIDE DEF oneb_1, oneb_2, proof1
    <3> QED BY Message_ref_Tran
  <2> QED BY DEF Caught, CaughtMsg

<1>caught_safe. Caught(M0) \cap SafeAcceptor = {}
  <2> SUFFICES ASSUME NEW s \in SafeAcceptor, s \in Caught(M0)
               PROVE  s \in Caught(M)
      BY DEF CaughtSpec
  <2> PICK x1 \in Tran(M0), x2 \in Tran(M0) :
            /\ ~Proposal(x1)
            /\ ~Proposal(x2)
            /\ x1.acc = s
            /\ x2.acc = s
            /\ x1 # x2
            /\ x1 \notin PrevTran(x2)
            /\ x2 \notin PrevTran(x1)
      BY DEF Caught, CaughtMsg
  <2> SUFFICES x1 \in Tran(M) /\ x2 \in Tran(M)
      BY DEF Caught, CaughtMsg
  <2> SUFFICES x1 # M0 /\ x2 # M0
    <3> HIDE DEF oneb_1, oneb_2, M0
    <3> QED BY <1>M0_tran, AcceptorAssumption DEF Proposal, OneA
  <2> ASSUME x1 = M0 PROVE FALSE
    <3> HIDE DEF oneb_1, oneb_2, M0
    <3> M.acc = s
        OBVIOUS
    <3> M \in SentBy(s)
        BY DEF KnownMsgsSpec1, SentBy, Proposal, OneA
    <3> x2 \in Tran(M)
        BY <1>M0_tran, AcceptorAssumption DEF Proposal, OneA
    <3> x2 \in SentBy(s)
        BY DEF KnownMsgsSpec1, KnownMsgsSpec2, SentBy, Proposal, OneA
    <3> x2 \in known_msgs[L0]
        BY DEF KnownMsgsSpec2
    <3> x2 \in PrevTran(M)
      <4> x2 \in PrevTran(M) \/ M \in PrevTran(x2)
          BY DEF MsgsSafeAcceptorPrevTranLinearSpec
      <4> ASSUME M \in PrevTran(x2) PROVE FALSE
        <5> M \in Tran(x2)
            BY DEF KnownMsgsPrevTranSpec
        <5> M = x2
            BY Tran_acyclic
        <5> x2 \in PrevTran(x1)
            BY <1>M0_prevtran, PrevTran_refl
        <5> QED OBVIOUS
      <4> QED OBVIOUS
    <3> QED BY <1>M0_prevtran
  <2> ASSUME x2 = M0 PROVE FALSE
    <3> HIDE DEF oneb_1, oneb_2, M0
    <3> M.acc = s
        OBVIOUS
    <3> M \in SentBy(s)
        BY DEF KnownMsgsSpec1, SentBy, Proposal, OneA
    <3> x1 \in Tran(M)
        BY <1>M0_tran, AcceptorAssumption DEF Proposal, OneA
    <3> x1 \in SentBy(s)
        BY DEF KnownMsgsSpec1, KnownMsgsSpec2, SentBy, Proposal, OneA
    <3> x1 \in known_msgs[L0]
        BY DEF KnownMsgsSpec2
    <3> x1 \in PrevTran(M)
      <4> x1 \in PrevTran(M) \/ M \in PrevTran(x1)
          BY DEF MsgsSafeAcceptorPrevTranLinearSpec
      <4> ASSUME M \in PrevTran(x1) PROVE FALSE
        <5> M \in Tran(x1)
            BY DEF KnownMsgsPrevTranSpec
        <5> M = x1
            BY Tran_acyclic
        <5> x1 \in PrevTran(x2)
            BY <1>M0_prevtran, PrevTran_refl
        <5> QED OBVIOUS
      <4> QED OBVIOUS
    <3> QED BY <1>M0_prevtran
  <2> QED OBVIOUS

<1> DEFINE mseq == [x \in 1..maxDepth(alpha) + 1 |-> IF x = maxDepth(alpha) + 1 THEN M0 ELSE seq[maxDepth(alpha) - x + 1].r]

<1> Len(mseq) = maxDepth(alpha) + 1
    OBVIOUS
<1> Len(mseq) \in Nat
    OBVIOUS
<1> maxDepth(alpha) =< Len(mseq)
    OBVIOUS
<1> \A i \in 1..maxDepth(alpha) : mseq[i] = seq[maxDepth(alpha) - i + 1].r
    OBVIOUS
<1> mseq[maxDepth(alpha) + 1] = M0
    OBVIOUS
<1> mseq \in [1..maxDepth(alpha) + 1 -> Message]
    BY WhateverSpec
<1> mseq \in Seq(Message)
    BY SeqDef
<1>0. Len(mseq) = maxDepth(alpha) + 1
    OBVIOUS

<1>seq0. alpha \in Con(alpha, M0)
  <2> <<alpha, alpha>> \in Ent
      BY EntanglementSelf
  <2> QED BY <1>caught_safe, ConnectedXXX

\* We need to show that mseq \in I (see Def of maxDepth)
\* Since Length(mseq) = maxDepth(alpha) + 1, we get a contradiction with the definition of maxDepth.

<1>seq1. \A i, j \in 1..Len(mseq) : i < j => mseq[i] \in Tran(mseq[j])
  <2> HIDE DEF mseq
  <2>1. \A i, j \in 1..maxDepth(alpha) : i < j => mseq[i] \in Tran(mseq[j])
    <3> SUFFICES ASSUME NEW k \in 1..maxDepth(alpha),
                        NEW l \in 1..maxDepth(alpha),
                        k < l
                 PROVE  seq[maxDepth(alpha) - k + 1].r \in Tran(seq[maxDepth(alpha) - l + 1].r)
        OBVIOUS
    <3> DEFINE l0 == maxDepth(alpha) - l + 1
    <3> DEFINE k0 == maxDepth(alpha) - k + 1
    <3> l0 < k0
        OBVIOUS
    <3> k0 =< Len(seq)
        OBVIOUS
    <3> l0 =< Len(seq)
        OBVIOUS
    <3> k0 \in 1..Len(seq)
        OBVIOUS
    <3> l0 \in 1..Len(seq)
        OBVIOUS
    <3> SUFFICES seq[k0].r \in Tran(seq[l0].r)
        OBVIOUS
    <3> HIDE DEF k0, l0, oneb_1, oneb_2, M0
    <3> \A i \in 1..Len(seq) :
            HeterogeneousSpecCond(alpha, bal, M, V_M, seq, i)
        OBVIOUS
    <3> QED BY HeterogeneousSpecCondProperties
  <2>2. \A i \in 1..maxDepth(alpha) : mseq[i] \in Tran(mseq[maxDepth(alpha) + 1])
    <3> SUFFICES ASSUME NEW j \in 1..maxDepth(alpha)
                 PROVE  seq[j].r \in Tran(M0)
        OBVIOUS
    <3> HIDE DEF oneb_1, oneb_2
    <3> SUFFICES seq[j].r \in Tran(M)
        BY Tran_trans
    <3> QED BY HeterogeneousSpecCondProperties
  <2> QED BY <2>1, <2>2

\*        \* cond 5:
\*        /\ x > 1 => gamma \in Con(alpha, seq[x - 1].r)
\*        \* cond 6:
\*        /\ x > 2 => gamma \notin Con(alpha, seq[x - 2].r)
<1>seq2. \A i, j \in 1..Len(mseq) : i < j => Con(alpha, mseq[i]) # Con(alpha, mseq[j])
  <2> HIDE DEF mseq
  <2>1. \A i, j \in 1..maxDepth(alpha) : i < j => Con(alpha, mseq[i]) # Con(alpha, mseq[j])
    <3> SUFFICES ASSUME NEW k \in 1..maxDepth(alpha),
                        NEW l \in 1..maxDepth(alpha),
                        k < l
                 PROVE  Con(alpha, seq[maxDepth(alpha) - k + 1].r) # Con(alpha, seq[maxDepth(alpha) - l + 1].r)
        OBVIOUS
    <3> DEFINE l0 == maxDepth(alpha) - l + 1
    <3> DEFINE k0 == maxDepth(alpha) - k + 1
    <3> l0 < k0
        OBVIOUS
    <3> l0 \in 1..Len(seq)
        OBVIOUS
    <3> k0 \in 1..Len(seq)
        OBVIOUS
    <3> k0 < Len(seq)
        OBVIOUS
    <3> QED BY HeterogeneousSpecCondProperties

  <2>2. \A i \in 1..maxDepth(alpha) : Con(alpha, mseq[i]) # Con(alpha, mseq[maxDepth(alpha) + 1])
    <3> SUFFICES ASSUME NEW j0 \in 1..maxDepth(alpha)
                 PROVE  Con(alpha, seq[j0].r) # Con(alpha, M0)
        OBVIOUS
    <3> maxDepth(alpha) + 1 =< Len(seq)
        OBVIOUS
    <3> seq[2].gamma \in Con(alpha, seq[j0].r)
      <4> seq[2].gamma \in Con(alpha, seq[1].r)
          BY DEF HeterogeneousSpecCond
      <4> CASE j0 = 1
          OBVIOUS
      <4> CASE 1 < j0
        <5> j0 < maxDepth(alpha) + 1
            OBVIOUS
        <5> j0 < Len(seq)
            OBVIOUS
        <5> 1 \in 1..Len(seq)
            OBVIOUS
        <5> j0 \in 1..Len(seq)
            OBVIOUS
        <5> Len(seq) =< Len(seq)
            OBVIOUS
        <5> \A i \in 1..Len(seq) :
                HeterogeneousSpecCond(alpha, bal, M, V_M, seq, i)
            OBVIOUS
        <5> HIDE DEF M0, oneb_1, oneb_2
        <5>1. \A i, j \in 1..Len(seq) : i < j /\ j < Len(seq) =>
                /\ Con(alpha, seq[i].r) \in SUBSET Con(alpha, seq[j].r)
                /\ Con(alpha, seq[i].r) # Con(alpha , seq[j].r)
            BY HeterogeneousSpecCondProperties
        <5> Con(alpha, seq[1].r) \in SUBSET Con(alpha, seq[j0].r)
            BY <5>1
        <5> QED OBVIOUS
      <4> QED OBVIOUS
    <3> seq[2].gamma \notin Con(alpha, M0)
      <4> seq[2].gamma \in Learner
          BY WhateverSpec

\*Ent == { LL \in Learner \X Learner :
\*         [from |-> LL[1], to |-> LL[2], q |-> SafeAcceptor] \in TrustSafe }
      <4> <<alpha, seq[2].gamma>> \notin Ent
        <5> SUFFICES ASSUME <<alpha, seq[2].gamma>> \in Ent PROVE FALSE
            OBVIOUS
        \* Sketch: 1) assuming that alpha and seq[2].gamma are entangled, we construct w0 \in Whatever as
        \* w0 == [m |-> m0, B_m |-> B_m0, r |-> r0, s |-> s0, gamma |-> gamma0]
        \* such that it satisfies HeterogeneousSpecCond(alpha, bal, M, V_M, [1 |-> w0], 1)
        \* Then we compare the sequence with seq1 = [1 |-> seq[1]]
        \* For S, we have HeterogeneousSpecCondMin(alpha, bal, M, V_M, S, 1)



        \* We then show that B_m0 < seq1[1].B_m, which is a contradiction.

\*    ChosenIn(alpha, b, v) ==
\*        \E S \in SUBSET Known2a(alpha, b, v) :
\*            /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
\*            /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive
        <5>1. PICK Q1 \in SUBSET Known2a(alpha, bal, val) :
                /\ \A x \in Q1 :
                    [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
                /\ [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
              BY DEF ChosenIn
        <5> Q1 \in SUBSET msgs
            BY DEF Known2a, KnownMsgsSpec1
        <5> Q1 \in SUBSET Message
            BY DEF TypeOK
        <5> Q1 \in SUBSET known_msgs[alpha]
            BY DEF Zenon, Known2a, KnownMsgsSpec2
        <5> [lr |-> alpha, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
            BY <5>1
        <5> \A x \in Q1 :
                [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
            BY <5>1
        <5> \A x \in Q1 : B(x, bal)
            BY DEF Known2a
        <5> \A x \in Q1 : ~OneA(x)
            BY MessageTypeSpec DEF Known2a
\*\*        From WellFormedness we have
\*\*                /\ m.lrns = { alpha \in Learner : [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, 1) }] \in TrustLive }
        <5> seq[2].m \in Tran(M)
            BY HeterogeneousSpecCondProperties
        <5> WellFormed(seq[2].m)
            BY DEF KnownMsgsSpec2
        <5> seq[2].m \in Message
            BY DEF WellFormed
        <5> seq[2].m \in known_msgs[L0]
            BY DEF KnownMsgsSpec2
        <5>2. seq[2].m.lrns = { l \in Learner : [lr |-> l, q |-> { mm.acc : mm \in qd(l, seq[2].m, 1) }] \in TrustLive }
              BY DEF WellFormed
        <5> seq[2].B_m \in Ballot
            BY WhateverSpec
        <5> B(seq[2].m, seq[2].B_m)
            BY DEF HeterogeneousSpecCond

        <5> DEFINE Q2 == qd(seq[2].gamma, seq[2].m, 1)
        <5> [lr |-> seq[2].gamma, q |-> { mm.acc : mm \in Q2 }] \in TrustLive
            BY <5>2 DEF HeterogeneousSpecCond
        <5> Q2 \in SUBSET Tran(seq[2].m)
            BY QuorumProperty1
        <5> Q2 \in SUBSET Message
            BY Tran_Message
        <5> Q2 \in SUBSET known_msgs[L0]
            BY DEF KnownMsgsSpec2
        <5> Q2 \in SUBSET msgs
            BY DEF KnownMsgsSpec1
        <5> \A x \in Q2 : ~OneA(x)
            BY QuorumProperty1 DEF Proposal, OneA
        <5> \A x \in Q2 : B(x, seq[2].B_m)
            BY QuorumProperty2 DEF HeterogeneousSpecCond
        <5> PICK p \in SafeAcceptor, s0 \in Q1, r0 \in Q2 :
                /\ s0.acc = p
                /\ r0.acc = p
          <6> HIDE DEF Q2
          <6> QED BY EntQuorumIntersection

        <5> DEFINE w0 == [m |-> seq[2].m, B_m |-> seq[2].B_m, r |-> r0, s |-> s0, gamma |-> seq[2].gamma]
        <5> w0 \in Whatever
            BY DEF Whatever

        <5> DEFINE seq0 == [ seq EXCEPT ![1] = w0 ]
        <5> seq0 \in Seq(Whatever)
            BY SeqDef
        <5>3. HeterogeneousSpecCond(alpha, bal, M, V_M, seq0, 1)
          <6> seq0[1] = w0
              OBVIOUS
          <6> HIDE DEF seq0
          <6>0. B(w0.m, w0.B_m)
                OBVIOUS \* proved above
          <6>2. bal < w0.B_m
                BY DEF HeterogeneousSpecCond
          <6>7. w0.gamma \in w0.m.lrns
                BY DEF HeterogeneousSpecCond
          <6>8. w0.r \in qd(w0.gamma, w0.m, 1)
                OBVIOUS
          <6>9. w0.s \in Tran(w0.r)
            <7> HIDE DEF Q2
            <7> B(s0, bal)
                OBVIOUS
            <7>1. r0 \in PrevTran(s0) \/ s0 \in PrevTran(r0)
                  BY DEF MsgsSafeAcceptorPrevTranLinearSpec, SentBy
            <7> r0 \in Tran(s0) \/ s0 \in Tran(r0)
                BY <7>1 DEF KnownMsgsPrevTranSpec, SentBy
            <7> QED BY <6>2, TranBallot DEF Ballot
          <6>11. w0.r.acc = w0.s.acc
                 OBVIOUS
          <6> maxDepth(alpha) - 1 + 1 = maxDepth(alpha)
              OBVIOUS
          <6>12. [lr |-> alpha, q |-> { z.acc : z \in qd(alpha, w0.s, maxDepth(alpha)) }] \in TrustLive
                 BY <5>1
          <6>13. B(w0.s, bal)
                 OBVIOUS
          <6>14. V(w0.m, V_M)
                 BY DEF HeterogeneousSpecCond
          <6>15. w0.m \in Tran(M)
                 BY HeterogeneousSpecCondProperties
          <6> QED BY <6>0, <6>2, <6>7, <6>8, <6>9, <6>11, <6>12, <6>13, <6>14, <6>15
                  DEF HeterogeneousSpecCond, MaxDepthSpec
        <5>4. seq0[1].B_m < seq[1].B_m
              BY DEF HeterogeneousSpecCond
        <5>5. HeterogeneousSpecCondMin(alpha, bal, M, V_M, seq, 1)
              OBVIOUS
        <5>6. seq[1].B_m =< seq0[1].B_m
              BY <5>3, <5>5 DEF HeterogeneousSpecCondMin
        \* contradiction with minimality of seq[1]
        <5> QED BY <5>4, <5>6, WhateverSpec DEF Ballot

      \* we prove that gamma in not entangled with alpha
      \* everything else is caught
      <4> QED BY <1>caught_fake, WhateverSpec, ConAllCaught
    <3> QED OBVIOUS
  <2> QED BY <2>1, <2>2

<1>seq3. Len(mseq) =< maxDepth(alpha)
    BY Zenon, <1>seq0, <1>seq1, <1>seq2, maxDepth_XXX
<1> QED BY <1>0, <1>seq3

-----------------------------------------------------------------------------

THEOREM GeneralBallotInduction ==
    ASSUME NEW P(_),
           \A bal \in Ballot : (\A b \in Ballot : b < bal => P(b)) => P(bal)
    PROVE  \A bal \in Ballot : P(bal)
PROOF
<1> USE DEF Ballot
<1> SUFFICES \A n \in Nat : (\A m \in 0..n - 1 : P(m)) => P(n)
    BY GeneralNatInduction, Blast
<1> QED OBVIOUS

\* TODO check if can be reused, in particular ZZZ, <1>caught_safe
LEMMA SafeAcceptorSentBallotTran ==
    ASSUME MsgsSafeAcceptorPrevTranLinearSpec,
           MsgsSafeAcceptorPrevTranSpec,
           TypeOK,
           NEW A \in SafeAcceptor,
           NEW X \in SentBy(A),
           NEW Y \in SentBy(A),
           NEW bx \in Ballot,
           NEW by \in Ballot,
           B(X, bx), B(Y, by),
           bx < by
    PROVE  X \in Tran(Y) 
PROOF BY TranBallot, MessageTypeSpec
      DEF MsgsSafeAcceptorPrevTranSpec, MsgsSafeAcceptorPrevTranLinearSpec, SentBy, Ballot, TypeOK

-----------------------------------------------------------------------------

LEMMA ChosenSafeCaseEq ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW BB \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, BB, V1), ChosenIn(L2, BB, V2)
    PROVE  V1 = V2
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
    ASSUME BVal \in [Ballot -> Value],
           NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           MaxDepthSpec,
           KnownMsgsSpec1,
           KnownMsgsSpec2,
           CaughtSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           KnownMsgsPrevTranSpec,
           TypeOK,
           <<L1, L2>> \in Ent,
           B1 < B2,
           ChosenIn(L1, B1, V1),
           ChosenIn(L2, B2, V2)
    PROVE  V1 = V2
PROOF
<1> SUFFICES ASSUME V1 # V2 PROVE FALSE
    OBVIOUS
<1> PICK S2 \in SUBSET Known2a(L2, B2, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY DEF ChosenIn
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption
<1> <<L2, L2>> \in Ent
    BY EntanglementSelf, EntanglementSym
<1>non_empty PICK A \in Q2 : TRUE
    BY EntaglementTrustLiveNonEmpty
<1> PICK M \in known_msgs[L2] :
        /\ L2 \in M.lrns
        /\ TwoA(M)
        /\ B(M, B2)
        /\ V(M, V2)
    BY <1>non_empty DEF Known2a
<1> maxDepth(L1) \in 0 .. maxDepth(L1)
    BY DEF MaxDepthSpec
<1> PICK seq \in [1 .. maxDepth(L1) + 1 -> Whatever] :
            \A x \in 1 .. maxDepth(L1) + 1 :
                HeterogeneousSpecCondMin(L1, B1, M, V2, seq, x)
    BY YYY
<1> QED BY ZZZ

LEMMA ChosenSafe ==
    ASSUME BVal \in [Ballot -> Value],
           NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK,
           MaxDepthSpec,
           KnownMsgsSpec1,
           KnownMsgsSpec2,
           CaughtSpec,
           MsgsSafeAcceptorPrevTranLinearSpec,
           KnownMsgsPrevTranSpec,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE  V1 = V2
PROOF
<1>0. CASE B1 < B2 BY <1>0, ChosenSafeCaseLt
<1>1. CASE B2 < B1 BY <1>1, ChosenSafeCaseLt, EntanglementSym
<1>2. CASE B1 = B2 BY <1>2, ChosenSafeCaseEq
<1>3. QED BY <1>0, <1>1, <1>2 DEF Ballot

LEMMA SafetyStep ==
    BVal \in [Ballot -> Value] /\
    TypeOK /\ NextTLA /\
    MaxDepthSpec /\
    KnownMsgsSpec1 /\ KnownMsgsSpec2 /\
    CaughtSpec /\
    MsgsSafeAcceptorPrevTranLinearSpec /\
    KnownMsgsPrevTranSpec /\
    DecisionSpec /\
    Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME BVal \in [Ballot -> Value],
               TypeOK, NextTLA, MaxDepthSpec,
               KnownMsgsSpec1, KnownMsgsSpec2,
               CaughtSpec,
               KnownMsgsPrevTranSpec,
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
    <3>1. CASE val # V1 /\ val # V2
          BY <3>1 DEF Safety, TypeOK
    <3>2. CASE val = V1
      <4> V2 \in decision[L2, B2]
          BY <3>2 DEF TypeOK
      <4> ChosenIn(L2, B2, V2)
          BY DEF DecisionSpec
      <4>2. CASE V1 \in decision[L1, B1]
            BY <4>2 DEF Safety
      <4>3. CASE V1 \notin decision[L1, B1]
        <5> lrn = L1 /\ bal = B1
            BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L1, B1, V1)
            BY <3>2
        <5> QED BY ChosenSafe
      <4> QED BY <4>2, <4>3
    <3>3. CASE val = V2
      <4> V1 \in decision[L1, B1]
          BY <3>3 DEF TypeOK
      <4> ChosenIn(L1, B1, V1)
          BY DEF DecisionSpec
      <4>2. CASE V2 \in decision[L2, B2]
            BY <4>2 DEF Safety
      <4>3. CASE V2 \notin decision[L2, B2]
        <5> lrn = L2 /\ bal = B2
            BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L2, B2, V2)
            BY <3>3
        <5> QED BY ChosenSafe
      <4> QED BY <4>2, <4>3
    <3> QED BY <3>1, <3>2, <3>3
  <2>10. QED OBVIOUS
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage, Safety
<1>9. QED BY <1>1, <1>3, <1>6, <1>7, <1>8
          DEF NextTLA, SafeAcceptorAction, LearnerAction

\* TODO check if all used
FullSafetyInvariant ==
    /\ BVal \in [Ballot -> Value]
    /\ TypeOK
    /\ KnownMsgsSpec1
    /\ KnownMsgsSpec2
    /\ SafeAcceptorPrevSpec1
    /\ SafeAcceptorPrevSpec2
    /\ MsgsSafeAcceptorPrevTranLinearSpec
\*    /\ MsgsSafeAcceptorSpec3
    /\ MsgsSafeAcceptorPrevRefSpec
    /\ KnownMsgsPrevTranSpec
    /\ DecisionSpec
    /\ Safety

LEMMA BValInit == Init => BVal \in [Ballot -> Value]
PROOF BY DEF Init

LEMMA TypeOKInit == Init => TypeOK
PROOF BY DEF Init, TypeOK

LEMMA KnownMsgsSpec1Init == Init => KnownMsgsSpec1
PROOF BY FS_EmptySet DEF Init, KnownMsgsSpec1, Acceptor

LEMMA KnownMsgsSpec2Init == Init => KnownMsgsSpec2
PROOF BY DEF Init, KnownMsgsSpec2, Acceptor

LEMMA SafeAcceptorPrevSpec1Init == Init => SafeAcceptorPrevSpec1
PROOF BY DEF Init, SafeAcceptorPrevSpec1, Acceptor, SentBy

LEMMA SafeAcceptorPrevSpec2Init == Init => SafeAcceptorPrevSpec2
PROOF BY DEF Init, SafeAcceptorPrevSpec2, Acceptor

LEMMA MsgsSafeAcceptorPrevTranLinearSpecInit == Init => MsgsSafeAcceptorPrevTranLinearSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevTranLinearSpec, SentBy

\*LEMMA MsgsSafeAcceptorSpec3Init == Init => MsgsSafeAcceptorSpec3
\*PROOF BY DEF Init, MsgsSafeAcceptorSpec3, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecInit == Init => MsgsSafeAcceptorPrevRefSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevRefSpec, SentBy

LEMMA KnownMsgsPrevTranSpecInit == Init => KnownMsgsPrevTranSpec
PROOF BY DEF Init, KnownMsgsPrevTranSpec, SentBy, Acceptor

LEMMA DecisionSpecInit == Init => DecisionSpec
PROOF BY DEF Init, DecisionSpec

LEMMA SafetyInit == Init => Safety
PROOF BY DEF Init, Safety

LEMMA FullSafetyInvariantInit == Init => FullSafetyInvariant
PROOF BY BValInit,
         TypeOKInit,
         KnownMsgsSpec1Init,
         KnownMsgsSpec2Init,
         SafeAcceptorPrevSpec1Init,
         SafeAcceptorPrevSpec2Init,
         MsgsSafeAcceptorPrevTranLinearSpecInit,
\*         MsgsSafeAcceptorSpec3Init,
         MsgsSafeAcceptorPrevRefSpecInit,
         KnownMsgsPrevTranSpecInit,
         DecisionSpecInit,
         SafetyInit
      DEF FullSafetyInvariant

LEMMA BValStutter ==
    BVal \in [Ballot -> Value] /\ vars = vars' => (BVal \in [Ballot -> Value])'
PROOF BY DEF vars 

LEMMA TypeOKStutter ==
    TypeOK /\ vars = vars' => TypeOK'
PROOF BY DEF TypeOK, vars

LEMMA KnownMsgsSpec1Stutter ==
    KnownMsgsSpec1 /\ vars = vars' => KnownMsgsSpec1'
PROOF BY Isa DEF KnownMsgsSpec1, vars, WellFormed, WellFormed1b,
                 qd, Fresh000, D, Con, ConByQuorum, Con2as, Buried,
                 V, B, Get1a, SameBallot, SameValue, ChainRef, KnownRefs,
                 Caught, CaughtMsg

LEMMA KnownMsgsSpec2Stutter ==
    KnownMsgsSpec2 /\ vars = vars' => KnownMsgsSpec2'
PROOF BY Isa DEF KnownMsgsSpec2, vars, WellFormed, WellFormed1b,
                 qd, Fresh000, D, Con, ConByQuorum, Con2as, Buried,
                 V, B, Get1a, SameBallot, SameValue, ChainRef, KnownRefs,
                 Caught, CaughtMsg

LEMMA SafeAcceptorPrevSpec1Stutter ==
    SafeAcceptorPrevSpec1 /\ vars = vars' => SafeAcceptorPrevSpec1'
PROOF BY DEF SafeAcceptorPrevSpec1, vars, SentBy

LEMMA SafeAcceptorPrevSpec2Stutter ==
    SafeAcceptorPrevSpec2 /\ vars = vars' => SafeAcceptorPrevSpec2'
PROOF BY DEF SafeAcceptorPrevSpec2, vars, SentBy

LEMMA MsgsSafeAcceptorPrevTranLinearSpecStutter ==
    MsgsSafeAcceptorPrevTranLinearSpec /\ vars = vars' => MsgsSafeAcceptorPrevTranLinearSpec'
PROOF BY DEF MsgsSafeAcceptorPrevTranLinearSpec, vars, SentBy

\*LEMMA MsgsSafeAcceptorSpec3Stutter ==
\*    MsgsSafeAcceptorSpec3 /\ vars = vars' => MsgsSafeAcceptorSpec3'
\*PROOF BY DEF MsgsSafeAcceptorSpec3, vars, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecStutter ==
    MsgsSafeAcceptorPrevRefSpec /\ vars = vars' => MsgsSafeAcceptorPrevRefSpec'
PROOF BY DEF MsgsSafeAcceptorPrevRefSpec, vars, SentBy

LEMMA KnownMsgsPrevTranSpecStutter ==
    KnownMsgsPrevTranSpec /\ vars = vars' => KnownMsgsPrevTranSpec'
PROOF BY DEF KnownMsgsPrevTranSpec, vars, SentBy

LEMMA DecisionSpecStutter ==
    DecisionSpec /\ vars = vars' => DecisionSpec'
PROOF BY Isa DEF DecisionSpec, vars, ChosenIn, Known2a, B, V, Get1a, qd, Fresh000, D, SameBallot, SameValue

LEMMA SafetyStutter ==
    Safety /\ vars = vars' => Safety'
PROOF BY DEF Safety, vars

LEMMA BValNext == NextTLA => UNCHANGED BVal
PROOF BY DEF NextTLA,
             ProposerAction, SendProposal,
             SafeAcceptorAction, Process,
             LearnerAction, LearnerRecv, LearnerDecide,
             FakeAcceptorAction, FakeSendControlMessage

LEMMA BValInvariant ==
    BVal \in [Ballot -> Value] /\ NextTLA => (BVal \in [Ballot -> Value])'
PROOF BY BValNext 

LEMMA FullSafetyInvariantNext ==
    MaxDepthSpec /\
    FullSafetyInvariant /\ [NextTLA]_vars => FullSafetyInvariant'
PROOF
<1> SUFFICES ASSUME MaxDepthSpec,
                    FullSafetyInvariant,
                    [NextTLA]_vars
             PROVE  FullSafetyInvariant'
    OBVIOUS
<1>1. CASE NextTLA
      BY <1>1,
         BValNext,
         BValInvariant,
         TypeOKInvariant,
         KnownMsgsSpec1Invariant,
         KnownMsgsSpec2Invariant,
         SafeAcceptorPrevSpec1Invariant,
         SafeAcceptorPrevSpec2Invariant,
         MsgsSafeAcceptorSpecImpliesCaughtSpec,
         MsgsSafeAcceptorPrevTranLinearSpecInvariant,
         MsgsSafeAcceptorPrevRefSpecInvariant,
         KnownMsgsPrevTranSpecInvariant,
         DecisionSpecInvariant,
         SafetyStep
      DEF FullSafetyInvariant
<1>2. CASE vars = vars'
      BY <1>2,
         BValStutter,
         TypeOKStutter,
         KnownMsgsSpec1Stutter,
         KnownMsgsSpec2Stutter,
         SafeAcceptorPrevSpec1Stutter,
         SafeAcceptorPrevSpec2Stutter,
         MsgsSafeAcceptorPrevTranLinearSpecStutter,
         MsgsSafeAcceptorPrevRefSpecStutter,
         KnownMsgsPrevTranSpecStutter,
         DecisionSpecStutter,
         SafetyStutter
      DEF FullSafetyInvariant
<1>3. QED BY <1>1, <1>2

LEMMA MaxDepthSpecLemma == MaxDepthSpec

THEOREM SafetyResult == Spec => []Safety
PROOF BY PTL, FullSafetyInvariantInit, FullSafetyInvariantNext, NextDef, MaxDepthSpecLemma
      DEF Spec, FullSafetyInvariant

=============================================================================
\* Modification History
\* Last modified Tue May 13 01:35:25 CEST 2025 by karbyshev
\* Created Tue Jun 20 00:28:26 CEST 2023 by karbyshev
