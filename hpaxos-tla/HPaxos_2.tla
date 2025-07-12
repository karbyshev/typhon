----------------------------- MODULE HPaxos_2 -------------------------------
EXTENDS Lib, HQuorum, HLearnerGraph, HMessage, Sequences

LOCAL INSTANCE TLAPS

Assert(P, str) == P

CONSTANT WellFormed2a(_)

-----------------------------------------------------------------------------
(* Algorithm specification *)

(****************************************************************************
--algorithm HPaxos2 {
  variables msgs = {},
            known_msgs = [x \in Acceptor \cup Learner |-> {}],
            recent_msgs = [a \in Acceptor |-> {}],
            prev_msg = [a \in Acceptor |-> NoMessage],
            decision = [lb \in Learner \X Ballot |-> {}];

  define {
    Get1a(m) ==
        { x \in Tran(m) :
            /\ OneA(x)
            /\ \A y \in Tran(m) :
                OneA(y) => y.bal <= x.bal }

    B(m, bal) == \E x \in Get1a(m) : bal = x.bal

    V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

    SameBallot(x, y) ==
        \A b \in Ballot : B(x, b) <=> B(y, b)

    SameValue(x, y) ==
        \A v \in Value : V(x, v) <=> V(y, v)

    KnownRefs(a, m) == \A r \in m.refs : r \in known_msgs[a]

    \* The acceptor is _caught_ in a message x if the transitive references of x
    \* include evidence such as two different messages both signed by the acceptor,
    \* which have equal previous messages (which may equal the NonMessage).
    CaughtMsg(x) ==
        { m \in Tran(x) :
            /\ ~Proposal(m)
            /\ \E m1 \in Tran(x) :
                /\ ~Proposal(m1)
                /\ m.acc = m1.acc
                /\ m # m1
                /\ m \notin PrevTran(m1)
                /\ m1 \notin PrevTran(m)
\*                /\ m.prev = m1.prev
\* TODO revert the change?
         }

    Caught(x) == { m.acc : m \in CaughtMsg(x) }

    \* Connected
    ConByQuorum(alpha, beta, x, S) == \* alpha : Learner, beta : Learner, x : 1b, S \in ByzQuorum
        /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
        /\ S \cap Caught(x) = {}

    Con(alpha, x) == \* alpha : Learner, x : 1b \* originally, x was supposed to be 1b; used with 1a in ValueExistence lemma
        { beta \in Learner :
            \E S \in ByzQuorum : ConByQuorum(alpha, beta, x, S) }

    \* Fresh 1b messages
    D(alpha, x, m) ==
        \* /\ TwoA(m) \* implied by the following since the intersection is non-empty
        /\ m.lrns \cap Con(alpha, x) # {}

    BallotUpperBound(M, bal) ==
        \A m \in M : \A bm \in Ballot : B(m, bm) => bm =< bal

    Latest(P) ==
        { x \in P : \A bx \in Ballot : B(x, bx) => BallotUpperBound(P, bx) }

    Fresh(alpha, x) == \* alpha : Learner, x : 1b
        \A m \in Latest({ mm \in Tran(x) : D(alpha, x, mm) }) : SameValue(m, x)

    QRec0 == [ LM \in Learner \X Message |-> [x \in Message |-> {}] ]

    QRec1(Q, n) ==
        [ LM \in Learner \X Message |->
            LET alpha == LM[1] IN
            LET x == LM[2] IN
                IF n = 1 THEN
                    [ y \in Tran(x) |->
                        { m \in Tran(y) :
                            /\ OneB(m)
                            /\ SameBallot(m, y)
                            /\ Fresh(alpha, m) } ]
                ELSE
                    [ y \in Tran(x) |->
                        { m \in Tran(y) :
                            /\ TwoA(m)
                            /\ SameBallot(m, y)
                            /\ [ lr |-> alpha,
                                 q  |-> { z.acc : z \in Q[LM][m] } ] \in TrustLive } ]
        ]

    QRec[n \in Nat] ==
        IF n = 0 THEN QRec0 ELSE QRec1(QRec[n - 1], n)

    \* Quorum of messages referenced by 2a for a learner instance
    qd(alpha, x, d) ==
        IF TwoA(x) THEN QRec[d][<<alpha, x>>][x] ELSE {}

    ConSeq(alpha) ==
        { seq \in Seq(Message) :
            /\ \A i, j \in 1..Len(seq) : i < j =>
                /\ seq[j] \in Tran(seq[i])
                /\ Con(alpha, seq[j]) # Con(alpha, seq[i])
            /\ seq # << >> => alpha \in Con(alpha, Head(seq))
        }

    maxDepth(alpha) ==
        LET I == { n \in Nat : \E seq \in ConSeq(alpha) : n = Len(seq) }
        IN Max(I)

    ChainRef(m) ==
        \/ m.prev = NoMessage
        \/ /\ m.prev \in m.refs
           /\ m.prev.acc = m.acc

    WellFormed1b(m) ==
        \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => Proposal(y)

    WellFormed(m) ==
        /\ m \in Message
        /\ \E b \in Ballot : B(m, b) \* TODO prove it
        /\ ChainRef(m)
        /\ m.lrns = { alpha \in Learner : [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, 1) }] \in TrustLive }
        /\ OneA(m) => B(m, m.bal)
        /\ OneB(m) => WellFormed1b(m)
        /\ TwoA(m) =>
            \* TODO check if this can be removed (most likely, is is not required for safety).
\*            /\ m.refs # {}
            \* Since the message structure embodies the learner values in our formalization,
            \* we must validate correctness of these values.
            /\ WellFormed2a(m)

    Known2a(alpha, b, v) ==
        { x \in known_msgs[alpha] :
            /\ TwoA(x)
            /\ alpha \in x.lrns
            /\ B(x, b)
            /\ V(x, v) }

    ChosenIn(alpha, b, v) ==
        \E S \in SUBSET Known2a(alpha, b, v) :
            /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
            /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive

    ReplyType(m, t) ==
        \/ OneA(m) /\ t = "1b"
        \/ OneB(m) /\ t = "2a"
        \/ TwoA(m) /\ t = "2a"

    Reply(new, m, acc) ==
        /\ ReplyType(m, new.type)
        /\ new.acc = acc
        /\ new.prev = prev_msg[acc]
        /\ new.refs = recent_msgs[acc] \cup {m}
        /\ WellFormed(new)
  } \* define

  macro Send(m) { msgs := msgs \cup {m} }

  macro SendProposal(b) {
    Send([type |-> "1a", bal |-> b, prev |-> NoMessage, refs |-> {}])
  }

  macro Receive(m) {
    when /\ m \notin known_msgs[self]
         /\ KnownRefs(self, m) ;
    known_msgs[self] := known_msgs[self] \cup {m}
  }

  macro Process(m) {
    \* TODO formulate a lemma that claims that given a Message m a reply Message can be contructed?
    either {
      with (new \in {reply \in Message : Reply(reply, m, self)})
      {
        prev_msg[self] := new ;
        recent_msgs[self] := {new} ;
        Send(new)
      }
    }
    or {
      when \A new \in Message : ~Reply(new, m, self) ;
      recent_msgs[self] := recent_msgs[self] \cup {m}
    }
  }

  macro FakeSendControlMessage() {
    with (fin \in FINSUBSET(msgs),
          P \in msgs \cup {NoMessage},
          LL \in SUBSET Learner,
          T \in {"1b", "2a"},
          msg = [type |-> T, acc |-> self, prev |-> P, refs |-> fin, lrns |-> LL])
    {
      when T = "2a" \/ LL = {} ;
      Send(msg)
    }
  }

  macro LearnerReceive(m) {
    when WellFormed(m) ;
    Receive(m)
  }

  macro LearnerDecide(b, v) {
    when ChosenIn(self, b, v) ;
    decision[<<self, b>>] := decision[self, b] \cup {v}
  }

  process (proposer \in Proposer) {
    propose: while (TRUE) {
      with (b \in Ballot) { SendProposal(b) }
    }
  }

  process (safe_acceptor \in SafeAcceptor) {
    safe: while (TRUE) {
      with (m \in msgs) {
        Receive(m) ;
        when WellFormed(m) ;
        Process(m)
      }
    }
  }

  process (learner \in Learner) {
    learn: while (TRUE) {
      either with (m \in msgs) LearnerReceive(m)
      or     with (b \in Ballot, v \in Value) LearnerDecide(b, v)
    }
  }

  process (fake_acceptor \in FakeAcceptor) {
    fake: while (TRUE) {
      FakeSendControlMessage()
    }
  }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "2c793f03" /\ chksum(tla) = "37449b54")
VARIABLES msgs, known_msgs, recent_msgs, prev_msg, decision

(* define statement *)
Get1a(m) ==
    { x \in Tran(m) :
        /\ OneA(x)
        /\ \A y \in Tran(m) :
            OneA(y) => y.bal <= x.bal }

B(m, bal) == \E x \in Get1a(m) : bal = x.bal

V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

SameBallot(x, y) ==
    \A b \in Ballot : B(x, b) <=> B(y, b)

SameValue(x, y) ==
    \A v \in Value : V(x, v) <=> V(y, v)

KnownRefs(a, m) == \A r \in m.refs : r \in known_msgs[a]




CaughtMsg(x) ==
    { m \in Tran(x) :
        /\ ~Proposal(m)
        /\ \E m1 \in Tran(x) :
            /\ ~Proposal(m1)
            /\ m.acc = m1.acc
            /\ m # m1
            /\ m \notin PrevTran(m1)
            /\ m1 \notin PrevTran(m)


     }

Caught(x) == { m.acc : m \in CaughtMsg(x) }


ConByQuorum(alpha, beta, x, S) ==
    /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
    /\ S \cap Caught(x) = {}

Con(alpha, x) ==
    { beta \in Learner :
        \E S \in ByzQuorum : ConByQuorum(alpha, beta, x, S) }


D(alpha, x, m) ==

    /\ m.lrns \cap Con(alpha, x) # {}

BallotUpperBound(M, bal) ==
    \A m \in M : \A bm \in Ballot : B(m, bm) => bm =< bal

Latest(P) ==
    { x \in P : \A bx \in Ballot : B(x, bx) => BallotUpperBound(P, bx) }

Fresh(alpha, x) ==
    \A m \in Latest({ mm \in Tran(x) : D(alpha, x, mm) }) : SameValue(m, x)

QRec0 == [ LM \in Learner \X Message |-> [x \in Message |-> {}] ]

QRec1(Q, n) ==
    [ LM \in Learner \X Message |->
        LET alpha == LM[1] IN
        LET x == LM[2] IN
            IF n = 1 THEN
                [ y \in Tran(x) |->
                    { m \in Tran(y) :
                        /\ OneB(m)
                        /\ SameBallot(m, y)
                        /\ Fresh(alpha, m) } ]
            ELSE
                [ y \in Tran(x) |->
                    { m \in Tran(y) :
                        /\ TwoA(m)
                        /\ SameBallot(m, y)
                        /\ [ lr |-> alpha,
                             q  |-> { z.acc : z \in Q[LM][m] } ] \in TrustLive } ]
    ]

QRec[n \in Nat] ==
    IF n = 0 THEN QRec0 ELSE QRec1(QRec[n - 1], n)


qd(alpha, x, d) ==
    IF TwoA(x) THEN QRec[d][<<alpha, x>>][x] ELSE {}

ConSeq(alpha) ==
    { seq \in Seq(Message) :
        /\ \A i, j \in 1..Len(seq) : i < j =>
            /\ seq[j] \in Tran(seq[i])
            /\ Con(alpha, seq[j]) # Con(alpha, seq[i])
        /\ seq # << >> => alpha \in Con(alpha, Head(seq))
    }

maxDepth(alpha) ==
    LET I == { n \in Nat : \E seq \in ConSeq(alpha) : n = Len(seq) }
    IN Max(I)

ChainRef(m) ==
    \/ m.prev = NoMessage
    \/ /\ m.prev \in m.refs
       /\ m.prev.acc = m.acc

WellFormed1b(m) ==
    \A y \in Tran(m) :
        m # y /\ SameBallot(m, y) => Proposal(y)

WellFormed(m) ==
    /\ m \in Message
    /\ \E b \in Ballot : B(m, b)
    /\ ChainRef(m)
    /\ m.lrns = { alpha \in Learner : [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, 1) }] \in TrustLive }
    /\ OneA(m) => B(m, m.bal)
    /\ OneB(m) => WellFormed1b(m)
    /\ TwoA(m) =>




        /\ WellFormed2a(m)

Known2a(alpha, b, v) ==
    { x \in known_msgs[alpha] :
        /\ TwoA(x)
        /\ alpha \in x.lrns
        /\ B(x, b)
        /\ V(x, v) }

ChosenIn(alpha, b, v) ==
    \E S \in SUBSET Known2a(alpha, b, v) :
        /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
        /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive

ReplyType(m, t) ==
    \/ OneA(m) /\ t = "1b"
    \/ OneB(m) /\ t = "2a"
    \/ TwoA(m) /\ t = "2a"

Reply(new, m, acc) ==
    /\ ReplyType(m, new.type)
    /\ new.acc = acc
    /\ new.prev = prev_msg[acc]
    /\ new.refs = recent_msgs[acc] \cup {m}
    /\ WellFormed(new)


vars == << msgs, known_msgs, recent_msgs, prev_msg, decision >>

ProcSet == (Proposer) \cup (SafeAcceptor) \cup (Learner) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ msgs = {}
        /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
        /\ recent_msgs = [a \in Acceptor |-> {}]
        /\ prev_msg = [a \in Acceptor |-> NoMessage]
        /\ decision = [lb \in Learner \X Ballot |-> {}]

proposer(self) == /\ \E b \in Ballot:
                       msgs' = (msgs \cup {([type |-> "1a", bal |-> b, prev |-> NoMessage, refs |-> {}])})
                  /\ UNCHANGED << known_msgs, recent_msgs, prev_msg, decision >>

safe_acceptor(self) == /\ \E m \in msgs:
                            /\ /\ m \notin known_msgs[self]
                               /\ KnownRefs(self, m)
                            /\ known_msgs' = [known_msgs EXCEPT ![self] = known_msgs[self] \cup {m}]
                            /\ WellFormed(m)
                            /\ \/ /\ \E new \in {reply \in Message : Reply(reply, m, self)}:
                                       /\ prev_msg' = [prev_msg EXCEPT ![self] = new]
                                       /\ recent_msgs' = [recent_msgs EXCEPT ![self] = {new}]
                                       /\ msgs' = (msgs \cup {new})
                               \/ /\ \A new \in Message : ~Reply(new, m, self)
                                  /\ recent_msgs' = [recent_msgs EXCEPT ![self] = recent_msgs[self] \cup {m}]
                                  /\ UNCHANGED <<msgs, prev_msg>>
                       /\ UNCHANGED decision

learner(self) == /\ \/ /\ \E m \in msgs:
                            /\ WellFormed(m)
                            /\ /\ m \notin known_msgs[self]
                               /\ KnownRefs(self, m)
                            /\ known_msgs' = [known_msgs EXCEPT ![self] = known_msgs[self] \cup {m}]
                       /\ UNCHANGED decision
                    \/ /\ \E b \in Ballot:
                            \E v \in Value:
                              /\ ChosenIn(self, b, v)
                              /\ decision' = [decision EXCEPT ![<<self, b>>] = decision[self, b] \cup {v}]
                       /\ UNCHANGED known_msgs
                 /\ UNCHANGED << msgs, recent_msgs, prev_msg >>

fake_acceptor(self) == /\ \E fin \in FINSUBSET(msgs):
                            \E P \in msgs \cup {NoMessage}:
                              \E LL \in SUBSET Learner:
                                \E T \in {"1b", "2a"}:
                                  LET msg == [type |-> T, acc |-> self, prev |-> P, refs |-> fin, lrns |-> LL] IN
                                    /\ T = "2a" \/ LL = {}
                                    /\ msgs' = (msgs \cup {msg})
                       /\ UNCHANGED << known_msgs, recent_msgs, prev_msg, 
                                       decision >>

Next == (\E self \in Proposer: proposer(self))
           \/ (\E self \in SafeAcceptor: safe_acceptor(self))
           \/ (\E self \in Learner: learner(self))
           \/ (\E self \in FakeAcceptor: fake_acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


Send(m) == msgs' = msgs \cup {m}

Recv(a, m) ==
    /\ m \notin known_msgs[a] \* ignore known messages
    /\ KnownRefs(a, m)
    /\ known_msgs' = [known_msgs EXCEPT ![a] = known_msgs[a] \cup {m}]

SendProposal(b) ==
    /\ Send([type |-> "1a", bal |-> b, prev |-> NoMessage, refs |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision

ProcessWithReply(a, m) ==
    \E new \in {reply \in Message : Reply(reply, m, a)}:
        /\ prev_msg' = [prev_msg EXCEPT ![a] = new]
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new}]
        /\ msgs' = msgs \cup {new}

ProcessNoReply(a, m) ==
    /\ \A new \in Message : ~Reply(new, m, a)
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ UNCHANGED <<msgs, prev_msg>>

Process(a, m) ==
    /\ Recv(a, m)
    /\ WellFormed(m)
    /\ \/ ProcessWithReply(a, m)
       \/ ProcessNoReply(a, m)
    /\ UNCHANGED decision

ProposerAction(p) ==
    \E bal \in Ballot : SendProposal(bal)

SafeAcceptorAction(a) ==
    \E m \in msgs : Process(a, m)

FakeSendControlMessage(a) ==
    /\ \E fin \in FINSUBSET(msgs) :
        \E P \in msgs \cup {NoMessage} :
        \E LL \in SUBSET Learner :
        \E T \in {"1b", "2a"} :
            /\ T = "2a" \/ LL = {}
            /\ LET new == [type |-> T, acc |-> a, prev |-> P, refs |-> fin, lrns |-> LL] IN
                Send(new)
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg  >>
    /\ UNCHANGED decision

LearnerRecv(l, m) ==
    /\ Recv(l, m)
    /\ WellFormed(m)
    /\ UNCHANGED << msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision

LearnerDecide(l, b, v) ==
    /\ ChosenIn(l, b, v)
    /\ decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, prev_msg >>

LearnerAction(lrn) ==
    \/ \E m \in msgs :
        LearnerRecv(lrn, m)
    \/ \E bal \in Ballot :
        \E val \in Value :
            LearnerDecide(lrn, bal, val)

FakeAcceptorAction(a) == FakeSendControlMessage(a)

NextTLA ==
    \/ \E p \in Proposer :
        ProposerAction(p)
    \/ \E acc \in SafeAcceptor :
        SafeAcceptorAction(acc)
    \/ \E lrn \in Learner :
        LearnerAction(lrn)
    \/ \E acc \in FakeAcceptor :
        FakeAcceptorAction(acc)

THEOREM NextDef == Next <=> NextTLA
<1>1. ASSUME NEW self \in Proposer
      PROVE proposer(self) <=> ProposerAction(self)
      BY DEF proposer, ProposerAction, SendProposal, Send
<1>2. ASSUME NEW self \in SafeAcceptor
      PROVE safe_acceptor(self) <=> SafeAcceptorAction(self)
      BY Zenon DEF safe_acceptor, SafeAcceptorAction, Process, ProcessWithReply, ProcessNoReply, Recv, Send, Assert
<1>3. ASSUME NEW self \in Learner
      PROVE learner(self) <=> LearnerAction(self)
      BY Zenon DEF learner, LearnerAction, LearnerRecv, LearnerDecide, Recv
<1>4. ASSUME NEW self \in FakeAcceptor
      PROVE fake_acceptor(self) <=> FakeAcceptorAction(self)
      BY Zenon DEF fake_acceptor, FakeAcceptorAction, FakeSendControlMessage, FakeSendControlMessage, Send
<1>5. QED BY <1>1, <1>2, <1>3, <1>4 DEF Next, NextTLA

-----------------------------------------------------------------------------
(* Sanity check propositions *)

\*SanityCheck0 ==
\*    \A L \in Learner : Cardinality(known_msgs[L]) = 0

SanityCheck1 ==
    \A L \in Learner : \A m1, m2 \in known_msgs[L] :
    \A b1, b2 \in Ballot :
        B(m1, b1) /\ B(m2, b2) => b1 = b2

2aNotSent ==
    \A M \in msgs : ~TwoA(M)

2aNotSentBySafeAcceptor ==
    \A M \in msgs : TwoA(M) => M.acc \notin SafeAcceptor

1bNotSentBySafeAcceptor ==
    \A M \in msgs : OneB(M) => M.acc \notin SafeAcceptor

NoDecision ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \notin decision[L, BB]

UniqueDecision ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

=============================================================================
\* Modification History
\* Last modified Thu Jul 10 21:50:55 CEST 2025 by karbyshev
\* Created Mon Jun 19 12:24:03 CEST 2022 by karbyshev
