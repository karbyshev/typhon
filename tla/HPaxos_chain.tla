---------------------------- MODULE HPaxos_chain ----------------------------
EXTENDS Naturals, FiniteSets, Functions

-----------------------------------------------------------------------------
CONSTANT LastBallot
ASSUME LastBallot \in Nat

Ballot == Nat

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

-----------------------------------------------------------------------------
CONSTANTS SafeAcceptor,
          FakeAcceptor,
          ByzQuorum,
          Learner

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorAssumption ==
    /\ SafeAcceptor \cap FakeAcceptor = {}
\*    /\ Acceptor \cap Learner = {}

ASSUME BQAssumption ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor

-----------------------------------------------------------------------------
(* Learner graph *)

CONSTANT TrustLive
ASSUME TrustLiveAssumption ==
    TrustLive \in SUBSET [lr : Learner, q : ByzQuorum]

CONSTANT TrustSafe
ASSUME TrustSafeAssumption ==
    TrustSafe \in SUBSET [from : Learner, to : Learner, q : ByzQuorum]

ASSUME LearnerGraphAssumptionSymmetry ==
    \A E \in TrustSafe :
        [from |-> E.to, to |-> E.from, q |-> E.q] \in TrustSafe

ASSUME LearnerGraphAssumptionTransitivity ==
    \A E1, E2 \in TrustSafe :
        E1.q = E2.q /\ E1.to = E2.from =>
        [from |-> E1.from, to |-> E2.to, q |-> E1.q] \in TrustSafe

ASSUME LearnerGraphAssumptionClosure ==
    \A E \in TrustSafe : \A Q \in ByzQuorum :
        E.q \subseteq Q =>
        [from |-> E.from, to |-> E.to, q |-> Q] \in TrustSafe

ASSUME LearnerGraphAssumptionValidity ==
    \A E \in TrustSafe : \A Q1, Q2 \in ByzQuorum :
        [lr |-> E.from, q |-> Q1] \in TrustLive /\
        [lr |-> E.to, q |-> Q2] \in TrustLive =>
        \E N \in E.q : N \in Q1 /\ N \in Q2

(* Entanglement relation *)
Ent == { LL \in Learner \X Learner :
         [from |-> LL[1], to |-> LL[2], q |-> SafeAcceptor] \in TrustSafe }

-----------------------------------------------------------------------------
(* Messages *)

CONSTANT MaxRefCardinality
ASSUME MaxRefCardinalityAssumption ==
    /\ MaxRefCardinality \in Nat
    /\ MaxRefCardinality >= 1

\*RefCardinality == Nat
RefCardinality == 1..MaxRefCardinality

FINSUBSET(S, R) == { Range(seq) : seq \in [R -> S] }
\*FINSUBSET(S, K) == { Range(seq) : seq \in [1..K -> S] }
\*FINSUBSET(S, R) == UNION { {Range(seq) : seq \in [1..K -> S]} : K \in R }

-----------------------------------------------------------------------------
(* Non-message value *)
NoMessage == [ type |-> "null" ]

MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, ref : {{}} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1b"},
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ] \cup
    [ type : {"2a"},
      lrn : Learner,
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ]

MessageRec[n \in Nat] ==
    IF n = 0
    THEN MessageRec0
    ELSE MessageRec1(MessageRec[n-1], n)

CONSTANT MaxMessageDepth
ASSUME MaxMessageDepth \in Nat

MessageDepthRange == Nat

Message == UNION { MessageRec[n] : n \in MessageDepthRange }

-----------------------------------------------------------------------------
(* Transitive references *)

\* Bounded transitive references
TranBound0 == [m \in Message |-> {m}]
TranBound1(tr, n) ==
    [m \in Message |-> {m} \cup UNION {tr[r] : r \in m.ref}]

TranBound[n \in Nat] ==
    IF n = 0
    THEN TranBound0
    ELSE TranBound1(TranBound[n-1], n)

\* Countable transitive references
TranDepthRange == MessageDepthRange

Tran(m) == UNION {TranBound[n][m] : n \in TranDepthRange}

-----------------------------------------------------------------------------
(* Algorithm specification *)

 \* TODO comment
VARIABLES msgs,
          known_msgs,
          recent_msgs,
          queued_msg,
          prev_msg,
          2a_lrn_loop,
          processed_lrns,
          decision,
          BVal

Get1a(m) ==
    { x \in Tran(m) :
        /\ x.type = "1a"
        /\ \A y \in Tran(m) :
            y.type = "1a" => y.bal <= x.bal }

B(m, bal) == \E x \in Get1a(m) : bal = x.bal

V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

\* Maximal ballot number of any messages known to acceptor a
MaxBal(a, mbal) ==
    /\ \E m \in known_msgs[a] : B(m, mbal)
    /\ \A x \in known_msgs[a] :
        \A b \in Ballot : B(x, b) => b =< mbal

SameBallot(x, y) ==
    \A b \in Ballot : B(x, b) <=> B(y, b)

\* The acceptor is _caught_ in a message x if the transitive references of x
\* include evidence such as two different messages both signed by the acceptor,
\* which have equal previous messges.
CaughtMsg(x) ==
    { m \in Tran(x) :
        /\ m.type # "1a"
        /\ \E m1 \in Tran(x) :
            /\ m1.type # "1a"
            /\ m.acc = m1.acc
            /\ m /= m1
            /\ m.prev = m1.prev }

Caught(x) == { m.acc : m \in CaughtMsg(x) }

\* Connected
ConByQuorum(a, b, x, S) == \* a : Learner, b : Learner, x : 1b, S \in ByzQuorum
    /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
    /\ S \cap Caught(x) = {}

Con(a, x) == \* a : Learner, x : 1b
    { b \in Learner :
        \E S \in ByzQuorum : ConByQuorum(a, b, x, S) }

\* 2a-message is _buried_ if there exists a quorum of acceptors that have seen
\* 2a-messages with different values, the same learner, and higher ballot
\* numbers.
Buried(x, y) == \* x : 2a, y : 1b
    LET Q == { m \in Tran(y) :
                \E z \in Tran(m) :
                    /\ z.type = "2a"
                    /\ z.lrn = x.lrn
                    /\ \A bx, bz \in Ballot :
                        B(x, bx) /\ B(z, bz) => bx < bz
                    /\ \A vx, vz \in Value :
                        V(x, vx) /\ V(z, vz) => vx # vz }
    IN [lr |-> x.lrn, q |-> { m.acc : m \in Q }] \in TrustLive

\* Connected 2a messages
Con2as(l, x) == \* l : Learner, x : 1b
    { m \in Tran(x) :
        /\ m.type = "2a"
        /\ m.acc = x.acc
        /\ ~Buried(m, x)
        /\ m.lrn \in Con(l, x) }

\* Fresh 1b messages
Fresh(l, x) == \* l : Learner, x : 1b
    \A m \in Con2as(l, x) : \A v \in Value : V(x, v) <=> V(m, v)

\* Quorum of messages referenced by 2a
q(x) == \* x : 2a
    LET Q == { m \in Tran(x) :
                /\ m.type = "1b"
                /\ Fresh(x.lrn, m)
                /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
    IN { m.acc : m \in Q }

ChainRef(m) == \A r \in m.ref : r.acc = m.acc <=> r = m.prev

WellFormed(m) ==
    /\ m \in Message
    /\ \E b \in Ballot : B(m, b) \* TODO prove it
    /\ ChainRef(m)
    /\ m.type = "1b" =>
        /\ m.ref # {}
        /\ (m.prev = NoMessage \/ m.prev \in m.ref)
        /\ \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    /\ m.type = "2a" =>
        /\ m.ref # {}
        /\ (m.prev = NoMessage \/ m.prev \in m.ref)
        /\ [lr |-> m.lrn, q |-> q(m)] \in TrustLive

vars == << msgs, known_msgs, recent_msgs, queued_msg,
           2a_lrn_loop, processed_lrns, decision, BVal >>

Init ==
    /\ msgs = {}
    /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
    /\ recent_msgs = [a \in Acceptor \cup Learner |-> {}]
    /\ queued_msg = [a \in Acceptor |-> NoMessage]
    /\ prev_msg = [a \in Acceptor |-> NoMessage]
    /\ 2a_lrn_loop = [a \in Acceptor |-> FALSE]
    /\ processed_lrns = [a \in Acceptor |-> {}]
    /\ decision = [lb \in Learner \X Ballot |-> {}]
    /\ BVal \in [Ballot -> Value]

Send(m) == msgs' = msgs \cup {m}

Proper(a, m) == \A r \in m.ref : r \in known_msgs[a]

Recv(a, m) ==
    /\ m \notin known_msgs[a] \* ignore known messages
    /\ WellFormed(m)
    /\ Proper(a, m)

Store(a, m) ==
    /\ known_msgs' = [known_msgs EXCEPT ![a] = known_msgs[a] \cup {m}]

Send1a(b) ==
    /\ Send([type |-> "1a", bal |-> b, prev |-> NoMessage, ref |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs,
                    queued_msg, prev_msg,
                    2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

Known2a(l, b, v) ==
    { x \in known_msgs[l] :
        /\ x.type = "2a"
        /\ x.lrn = l
        /\ B(x, b)
        /\ V(x, v) }

\* The following is invariant for queued_msg variable values.
\* For any safe acceptor A, if queued_msg[A] # NoMessage then
\* queued_msg[A] is a well-formed message of type "1b" sent by A,
\* having the direct references all known to A.

Process1a(a, m) ==
    LET new1b == [type |-> "1b", acc |-> a,
                  prev |-> prev_msg[a],
                  ref |-> recent_msgs[a] \cup {m}] IN
    /\ m.type = "1a"
    /\ Recv(a, m)
    /\ Store(a, m)
    /\ WellFormed(new1b) =>
        /\ Send(new1b)
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {}]
        /\ queued_msg' = [queued_msg EXCEPT ![a] = new1b]
        /\ prev_msg' = [prev_msg EXCEPT ![a] = new1b]
    /\ (~WellFormed(new1b)) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
        /\ UNCHANGED << msgs, queued_msg, prev_msg >>
    /\ UNCHANGED << 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

Process1b(a, m) ==
    /\ m.type = "1b"
    /\ Recv(a, m)
    /\ Store(a, m)
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ (\A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b) =>
        /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = TRUE]
        /\ processed_lrns' = [processed_lrns EXCEPT ![a] = {}]
    /\ (~(\A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b)) =>
        UNCHANGED << 2a_lrn_loop, processed_lrns >>
    \* TODO: move the instruction from here to AcceptorProcessAction
    /\ queued_msg' = [queued_msg EXCEPT ![a] = NoMessage]
    /\ UNCHANGED << msgs, prev_msg, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoopStep(a, lrn) ==
    LET new2a == [type |-> "2a", lrn |-> lrn, acc |-> a,
                  prev |-> prev_msg[a],
                  ref |-> recent_msgs[a]] IN
    /\ processed_lrns' =
        [processed_lrns EXCEPT ![a] = processed_lrns[a] \cup {lrn}]
    /\ WellFormed(new2a) =>
        /\ Send(new2a)
        /\ Store(a, new2a)
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new2a}]
        /\ prev_msg' = [prev_msg EXCEPT ![a] = new2a]
    /\ (~WellFormed(new2a)) =>
        UNCHANGED << msgs, known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED << queued_msg, 2a_lrn_loop, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoopDone(a) ==
    /\ Learner \ processed_lrns[a] = {}
    /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = FALSE]
    /\ UNCHANGED << msgs,
                    known_msgs, recent_msgs,
                    queued_msg, prev_msg,
                    processed_lrns, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoop(a) ==
    \/ \E lrn \in Learner \ processed_lrns[a] :
        Process1bLearnerLoopStep(a, lrn)
    \/ Process1bLearnerLoopDone(a)

Process2a(a, m) ==
    /\ m.type = "2a"
    /\ Recv(a, m)
    /\ Store(a, m)
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ UNCHANGED << msgs, queued_msg, prev_msg, 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

ProposerSendAction ==
    \E bal \in Ballot : Send1a(bal)

AcceptorProcessAction ==
    \E a \in SafeAcceptor :
        \/ /\ 2a_lrn_loop[a] = FALSE
           /\ \/ /\ queued_msg[a] # NoMessage
                 /\ Process1b(a, queued_msg[a])
              \/ /\ queued_msg[a] = NoMessage
                 /\ \E m \in msgs :
                    /\ \/ Process1a(a, m)
                       \/ Process1b(a, m)
        \/ /\ 2a_lrn_loop[a] = TRUE
           /\ Process1bLearnerLoop(a)

FakeSend1b(a) ==
    /\ \E fin \in FINSUBSET(msgs, RefCardinality) :
        LET new1b == [type |-> "1b", acc |-> a, ref |-> fin] IN
        /\ WellFormed(new1b)
        /\ Send(new1b)
    /\ UNCHANGED << known_msgs, recent_msgs, queued_msg, prev_msg,
                    2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

FakeSend2a(a) ==
    /\ \E fin \in FINSUBSET(msgs, RefCardinality) :
        \E lrn \in Learner :
            LET new2a == [type |-> "2a", lrn |-> lrn, acc |-> a, ref |-> fin] IN
            /\ WellFormed(new2a)
            /\ Send(new2a)
    /\ UNCHANGED << known_msgs, recent_msgs, queued_msg, prev_msg,
                    2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

LearnerRecv(l, m) ==
    /\ Recv(l, m)
    /\ Store(l, m)
    /\ UNCHANGED << msgs, recent_msgs, queued_msg, prev_msg,
                    2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

ChosenIn(l, b, v) ==
    \E S \in SUBSET Known2a(l, b, v) :
        [lr |-> l, q |-> { m.acc : m \in S }] \in TrustLive

LearnerDecide(l, b, v) ==
    /\ ChosenIn(l, b, v)
    /\ decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, queued_msg, prev_msg,
                    2a_lrn_loop, processed_lrns >>
    /\ UNCHANGED BVal

LearnerAction ==
    \E lrn \in Learner :
        \/ \E m \in msgs :
            LearnerRecv(lrn, m)
        \/ \E bal \in Ballot :
           \E val \in Value :
            LearnerDecide(lrn, bal, val)

FakeAcceptorAction ==
    \E a \in FakeAcceptor :
        \/ FakeSend1b(a)
        \/ FakeSend2a(a)

Next ==
    \/ ProposerSendAction
    \/ AcceptorProcessAction
    \/ LearnerAction
    \/ FakeAcceptorAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

\* THEOREM SafetyResult == Spec => []Safety

-----------------------------------------------------------------------------
(* Sanity check propositions *)

SanityCheck0 ==
    \A L \in Learner : Cardinality(known_msgs[L]) = 0

SanityCheck1 ==
    \A L \in Learner : \A m1, m2 \in known_msgs[L] :
    \A b1, b2 \in Ballot :
        B(m1, b1) /\ B(m2, b2) => b1 = b2

2aNotSent ==
    \A M \in msgs : M.type # "2a"

2aNotSentBySafeAcceptor ==
    \A M \in msgs : M.type = "2a" => M.acc \notin SafeAcceptor

1bNotSentBySafeAcceptor ==
    \A M \in msgs : M.type = "1b" => M.acc \notin SafeAcceptor

NoDecision ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \notin decision[L, BB]

UniqueDecision ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

=============================================================================
\* Modification History
\* Last modified Thu Jun 22 14:30:47 CEST 2023 by karbyshev
\* Created Mon Jun 19 12:24:03 CEST 2022 by karbyshev
