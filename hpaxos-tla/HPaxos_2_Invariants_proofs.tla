--------------------- MODULE HPaxos_2_Invariants_proofs ---------------------
EXTENDS HPaxos_2_Specs, HMessageTheorems, HPaxos_2_Structures, LibTheorems, TLAPS

LOCAL INSTANCE FiniteSetTheorems

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
      BY OneA_Message_base
  <2> QED BY DEF SendProposal, Send, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> acc \in Acceptor BY DEF Acceptor
  <2> m \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage DEF Process, ProcessWithReply, ProcessNoReply, Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Process, Recv, TypeOK
  <2> recent_msgs' \in [Acceptor -> SUBSET Message]
      BY DEF Process, ProcessWithReply, ProcessNoReply, TypeOK
  <2> prev_msg' \in [Acceptor -> Message \cup {NoMessage}]
      BY DEF Process, ProcessWithReply, ProcessNoReply, TypeOK
  <2> decision' \in [Learner \X Ballot -> SUBSET Value]
      BY DEF Process, TypeOK
  <2> QED BY DEF TypeOK
<1>7. CASE \E l \in Learner : LearnerAction(l)
      BY <1>7 DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
  <2> SUFFICES msgs' \in SUBSET Message
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage, TypeOK
  <2> PICK fake \in FakeAcceptor,
           fin \in FINSUBSET(msgs),
           P \in msgs \cup {NoMessage},
           LL \in SUBSET Learner,
           T \in {"1b", "2a"} :
      /\ T = "2a" \/ LL = {}
      /\ Send([type |-> T, acc |-> fake, prev |-> P, refs |-> fin, lrns |-> LL])
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage
  <2> SUFFICES [type |-> T, acc |-> fake, prev |-> P, refs |-> fin, lrns |-> LL] \in Message
      BY DEF Send, TypeOK
  <2> P \in Message \cup {NoMessage}
      BY DEF TypeOK
  <2> fin \in SUBSET Message
      BY FinSubset_sub DEF TypeOK
  <2> IsFiniteSet(fin)
      BY DEF FINSUBSET
  <2> QED BY OneB_Message, TwoA_Message DEF Acceptor
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
  <2> QED BY DEF Process, ProcessWithReply, ProcessNoReply, Send
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
  <2> QED BY DEF Process, ProcessWithReply, ProcessNoReply, Send
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>8 DEF FakeAcceptorAction, FakeSendControlMessage, Send
<1>9. QED BY <1>1, <1>3, <1>6, <1>7, <1>8
          DEF NextTLA, SafeAcceptorAction, LearnerAction

LEMMA WellFormed_monotone ==
    \A m \in Message : WellFormed(m) <=> WellFormed(m)'
PROOF BY DEF WellFormed

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

\* TODO finish the proof
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
<1> SUFFICES ASSUME M \notin recent_msgs[A]
             PROVE  M \in SentBy(A)'
    BY Sent_monotone DEF RecentMsgsSpec1, SentBy, TypeOK
<1> TypeOK' BY TypeOKInvariant
<1> SafeAcceptor \in SUBSET Acceptor
    BY DEF Acceptor
<1> A \in Acceptor
    OBVIOUS
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal, SentBy, Send, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, m \in msgs : Process(acc, m)
      BY <1>3
  <2> m \in Message BY DEF TypeOK
  <2>1. CASE ProcessWithReply(acc, m)
        BY <2>1 DEF ProcessWithReply, Reply, ReplyType, SentBy, Send, OneA, TypeOK
  <2>2. CASE ProcessNoReply(acc, m)
    <3> ~OneA(m)
\*    <3> M = m
\*        BY <2>2 DEF ProcessNoReply, TypeOK
    <3> QED BY <2>2 DEF ProcessNoReply, SentBy, Send, OneA, TypeOK
  <2> QED BY <2>1, <2>2 DEF Process
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
    TypeOK /\ NextTLA /\
    KnownMsgsSpec2 /\
    DecisionSpec => DecisionSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA, DecisionSpec,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    VV \in decision[L, BB]'
             PROVE  ChosenIn(L, BB, VV)'
    BY DEF DecisionSpec
<1> TypeOK' BY TypeOKInvariant
<1> Known2a(L, BB, VV) \subseteq Message
    BY DEF Known2a, KnownMsgsSpec2, TypeOK
<1> USE DEF DecisionSpec
<1> USE DEF ChosenIn
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> UNCHANGED decision
      BY DEF SendProposal
  <2> QED BY Known2aMonotone
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process(acc, msg)
      BY <1>3
  <2> UNCHANGED decision
      BY DEF Process
  <2> QED BY Known2aMonotone
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, Known2aMonotone DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs>>
      BY <1>8 DEF LearnerDecide
  <2> QED BY Known2aMonotone DEF TypeOK
<1>9. CASE \E a \in FakeAcceptor : FakeAcceptorAction(a)
      BY <1>9, Known2aMonotone
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
  <2>1. CASE ProcessWithReply(acc, m)
    <3> PICK new \in Message :
                /\ Reply(new, m, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> ~OneA(new)
        BY ReplyNotOneA
    <3> new.acc = acc
        BY DEF Reply
    <3>1. CASE acc # A
          BY <3>1, NoMessageIsNotAMessage DEF SentBy, Send, OneA, TypeOK
    <3>2. CASE acc = A
          BY <3>2, NoMessageIsNotAMessage DEF SentBy, Send, OneA, TypeOK
    <3> QED BY <3>1, <3>2
  <2>2. CASE ProcessNoReply(acc, m)
        BY <2>2 DEF ProcessNoReply, SentBy
  <2> QED BY <2>1, <2>2 DEF Process
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
  <2>1. CASE ProcessWithReply(acc, m)
    <3> PICK new \in Message :
                /\ Reply(new, m, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> ~OneA(new)
        BY ReplyNotOneA
    <3> new # NoMessage
        BY NoMessageIsNotAMessage
    <3>1. CASE acc = A
      <4> SentBy(A)' = SentBy(A) \cup {new}
          BY <3>1 DEF SentBy, OneA, Reply
      <4> prev_msg[A]' = new
          BY <3>1 DEF Send, TypeOK
      <4> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in PrevTran(new)
          BY <3>1, Message_prev_PrevTran DEF SafeAcceptorPrevSpec1, Reply
      <4> prev_msg[A]' \in SentBy(A)'
          OBVIOUS
      <4> prev_msg[A]' \in recent_msgs[A]'
          BY DEF TypeOK
      <4> QED BY PrevTran_trans, PrevTran_refl DEF SafeAcceptorPrevSpec1
    <3>2. CASE acc # A
          BY <3>2 DEF SentBy, Reply, TypeOK
    <3> QED BY <3>1, <3>2
  <2>2. CASE ProcessNoReply(acc, m)
        BY <2>2 DEF ProcessNoReply, SentBy, TypeOK
  <2> QED BY <2>1, <2>2 DEF Process
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
  <2>1. CASE ProcessWithReply(acc, msg)
    <3> PICK new \in Message :
                /\ Reply(new, msg, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> m2 = new
        OBVIOUS
    <3> \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])
        BY DEF SafeAcceptorPrevSpec2
    <3> prev_msg[A] \in PrevTran(m2)
        BY Message_prev_PrevTran DEF Reply
    <3> QED BY PrevTran_trans DEF SentBy
  <2>2. CASE ProcessNoReply(acc, msg)
        BY <2>2 DEF ProcessNoReply
  <2> QED BY <2>1, <2>2 DEF Process
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
  <2>1. CASE ProcessWithReply(acc, msg)
    <3> PICK new \in Message :
                /\ Reply(new, msg, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> m2 = new
        OBVIOUS
    <3> acc = A
        BY DEF Reply, SentBy, TypeOK
    <3> prev_msg[A] \in Message
        BY DEF TypeOK, Acceptor
    <3> prev_msg[A] \in m1.refs
        BY DEF MsgsSafeAcceptorPrevRefSpec, Reply, SentBy, Proposal, OneA
    <3> m1 \notin Tran(prev_msg[A])
        BY Tran_ref_acyclic
    <3> m1 \in Tran(prev_msg[A])
        BY DEF SafeAcceptorPrevSpec2, MsgsSafeAcceptorPrevTranSpec, SentBy, Proposal, OneA
    <3> QED OBVIOUS
  <2>2. CASE ProcessNoReply(acc, msg)
        BY <2>2 DEF ProcessNoReply
  <2> QED BY <2>1, <2>2 DEF Process
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
  <2>1. CASE ProcessWithReply(acc, msg)
    <3> PICK new \in Message :
                /\ Reply(new, msg, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> mm = new
        OBVIOUS
    <3> QED BY DEF SafeAcceptorPrevSpec2, Reply, Recv, SentBy, TypeOK
  <2>2. CASE ProcessNoReply(acc, msg)
        BY <2>2 DEF ProcessNoReply
  <2> QED BY <2>1, <2>2 DEF Process
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
  <2>1. CASE ProcessWithReply(acc, msg)
    <3> PICK new \in Message :
                /\ Reply(new, msg, acc)
                /\ prev_msg' = [prev_msg EXCEPT ![acc] = new]
                /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {new}]
                /\ msgs' = msgs \cup {new}
        BY <2>1 DEF ProcessWithReply
    <3> m1 = new
        BY DEF Send, TypeOK
    <3> new.prev = prev_msg[acc]
        BY DEF Reply
    <3> m1.prev # NoMessage /\ m2 \in PrevTran(m1.prev)
        BY PrevTran_eq
    <3> prev_msg[acc] \in SentBy(acc)
        BY DEF SafeAcceptorPrevSpec2
    <3> prev_msg[acc] \in recent_msgs[acc]
        BY DEF SafeAcceptorPrevSpec2
    <3> m1.prev \in Message
        BY DEF SentBy, TypeOK
    <3> QED BY Tran_refl, Tran_trans, Tran_eq DEF Reply
  <2>2. CASE ProcessNoReply(acc, msg)
        BY <2>2 DEF ProcessNoReply
  <2> QED BY <2>1, <2>2 DEF Process
<1>6. CASE \E l \in Learner : LearnerAction(l)
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
  <2> PICK acc \in FakeAcceptor : FakeSendControlMessage(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSendControlMessage, Send, SentBy
<1> QED BY <1>1, <1>3, <1>6, <1>7
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction

LEMMA KnownMsgsPrevTranSpecInvariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 /\
    KnownMsgsSpec2 /\
    KnownMsgsPrevTranSpec =>
    KnownMsgsPrevTranSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, NextTLA,
                    KnownMsgsSpec1,
                    KnownMsgsSpec2,
                    KnownMsgsPrevTranSpec
             PROVE  KnownMsgsPrevTranSpec'
    OBVIOUS
<1> TypeOK'
    BY TypeOKInvariant
<1> KnownMsgsSpec1'
    BY KnownMsgsSpec1Invariant
<1> KnownMsgsSpec2'
    BY KnownMsgsSpec2Invariant
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner,
                    NEW m1 \in known_msgs[AL]',
                    m1 \notin known_msgs[AL],
                    NEW m2 \in PrevTran(m1),
                    m2 # m1
             PROVE  m2 \in Tran(m1)
    BY Tran_refl DEF KnownMsgsPrevTranSpec, KnownMsgsSpec1, TypeOK
<1> m1 \in Message
    BY DEF KnownMsgsSpec1, TypeOK
<1> m1.prev # NoMessage
    BY PrevTran_eq
<1> USE DEF KnownMsgsPrevTranSpec
<1>1. CASE \E p \in Proposer : ProposerAction(p)
  <2> PICK p \in Proposer, bal \in Ballot : SendProposal(bal)
      BY <1>1 DEF ProposerAction
  <2> QED BY DEF SendProposal
<1>3. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process(a, m)
  <2> PICK acc \in SafeAcceptor,
           msg \in msgs :
           /\ Recv(acc, msg)
           /\ WellFormed(msg)
      BY <1>3 DEF Process
  <2> AL = acc
      BY DEF Recv, TypeOK, Acceptor
  <2> m1 = msg
      BY DEF Recv, TypeOK, Acceptor
  <2> m1.prev \in m1.refs
      BY DEF WellFormed, ChainRef
  <2> m1.prev \in Tran(m1)
      BY Message_ref_Tran
  <2> m1.prev # m1
      BY Tran_ref_acyclic
  <2> m1.prev \in known_msgs[AL]
      BY DEF KnownMsgsSpec2, Recv, TypeOK
  <2> m2 \in PrevTran(m1.prev)
      BY PrevTran_eq
  <2> m2 \in Tran(m1.prev)
      OBVIOUS
  <2> QED BY Tran_trans
<1>6. CASE \E lrn \in Learner : \E msg \in msgs : LearnerRecv(lrn, msg)
  <2> PICK lrn \in Learner, msg \in msgs : LearnerRecv(lrn, msg)
      BY <1>6
  <2> Recv(lrn, msg)
      BY DEF LearnerRecv
  <2> WellFormed(msg)
      BY DEF LearnerRecv
  <2> AL = lrn
      BY DEF Recv, TypeOK, Acceptor
  <2> m1 = msg
      BY DEF Recv, TypeOK, Acceptor
  <2> m1.prev \in m1.refs
      BY DEF WellFormed, ChainRef
  <2> m1.prev \in Tran(m1)
      BY Message_ref_Tran
  <2> m1.prev # m1
      BY Tran_ref_acyclic
  <2> m1.prev \in known_msgs[AL]
      BY DEF KnownMsgsSpec2, Recv, TypeOK
  <2> m2 \in PrevTran(m1.prev)
      BY PrevTran_eq
  <2> m2 \in Tran(m1.prev)
      OBVIOUS
  <2> QED BY Tran_trans
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE \E a \in FakeAcceptor : FakeSendControlMessage(a)
      BY <1>8, AcceptorAssumption DEF FakeSendControlMessage
<1> QED BY <1>1, <1>3, <1>6, <1>7, <1>8
        DEF NextTLA, SafeAcceptorAction, FakeAcceptorAction, LearnerAction

=============================================================================
\* Modification History
\* Last modified Wed Jun 25 21:18:18 CEST 2025 by karbyshev
\* Created Tue May 20 23:09:22 CEST 2025 by karbyshev
