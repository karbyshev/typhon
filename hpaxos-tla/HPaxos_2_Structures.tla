------------------------ MODULE HPaxos_2_Structures ------------------------
EXTENDS HPaxos_2, HPaxos_2_Specs

LOCAL INSTANCE FiniteSets

-----------------------------------------------------------------------------

LEMMA BallotFiniteSetMaxExists ==
    ASSUME NEW A \in SUBSET Ballot,
           A # {},
           IsFiniteSet(A)
    PROVE  \E max \in A : IsMax(max, A)

LEMMA BallotMaxUnique ==
    ASSUME NEW A \in SUBSET Ballot,
           NEW x \in A, NEW y \in A,
           IsMax(x, A),
           IsMax(y, A)
    PROVE  x = y

-----------------------------------------------------------------------------
LEMMA CaughtMsgSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg(M) \in SUBSET Message
           /\ \A X \in CaughtMsg(M) : ~Proposal(X)

-----------------------------------------------------------------------------
\* TODO clean
\*LEMMA ReplyTypeSpec ==
\*    ASSUME NEW m \in Message,
\*           NEW t \in {"1b", "2a", "2b"},
\*           ReplyType(m, t)
\*    PROVE  ~TwoB(m)

-----------------------------------------------------------------------------
(* Facts about Get1a, B and V relations *)

LEMMA Get1a_TypeOK ==
    ASSUME NEW m \in Message
    PROVE  /\ Get1a(m) \subseteq Message
           /\ \A x \in Get1a(m) : x.bal \in Ballot

LEMMA Get1a_correct ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m), NEW y \in Get1a(m)
    PROVE  x.bal = y.bal

LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE  b1 = b2

LEMMA B_def ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m)
    PROVE  \E b \in Ballot : B(m, b)

LEMMA B_1a ==
    ASSUME NEW m \in Message,
               OneA(m),
               m.refs = {}
    PROVE  B(m, m.bal)

LEMMA V_func ==
    ASSUME NEW m \in Message,
           NEW v1 \in Value, V(m, v1),
           NEW v2 \in Value, V(m, v2)
    PROVE  v1 = v2

LEMMA V_def ==
    ASSUME BVal \in [Ballot -> Value],
           NEW m \in Message,
           NEW b \in Ballot, B(m, b)
    PROVE V(m, BVal[b])

LEMMA SameBallot_B ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot,
           B(x, bal),
           B(y, bal)
    PROVE  SameBallot(x, y)

\* TODO remove if not used
LEMMA SameBallot_sym ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           SameBallot(x, y)
    PROVE  SameBallot(y, x)

\* TODO remove if not used
LEMMA SameValue_sym ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           SameValue(x, y)
    PROVE  SameValue(y, x)

LEMMA SameBallotValue ==
    ASSUME BVal \in [Ballot -> Value],
           NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot, B(x, bal),
           SameBallot(x, y)
    PROVE  SameValue(x, y)

LEMMA TranBallot ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           NEW b1 \in Ballot, NEW b2 \in Ballot,
           B(m1, b1), B(m2, b2)
    PROVE  b2 =< b1

-----------------------------------------------------------------------------
\* Facts about Latest

LEMMA LatestSubset ==
    ASSUME NEW P \in SUBSET Message
    PROVE  Latest(P) \in SUBSET P

LEMMA LatestNonEmpty ==
    ASSUME NEW P \in SUBSET { m \in Message : WellFormed(m) },
           P # {},
           IsFiniteSet(P)
    PROVE  Latest(P) # {}

-----------------------------------------------------------------------------
\* TODO
LEMMA LearnersWellFormed ==
    ASSUME NEW m \in Message,
           WellFormed(m)
    PROVE  m.lrns # {} <=> TwoA(m)

-----------------------------------------------------------------------------
\* Check equivalence of two well-formedness conditions

LEMMA WellFormedCondition1 ==
    ASSUME NEW m \in Message, OneB(m),
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y)
    PROVE  \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m)

\* Equivalence of two well-formedness conditions
LEMMA WellFormedConditionEquiv1 ==
    ASSUME NEW m \in Message, OneB(m)
    PROVE  (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m))
           <=>
           (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y))

LEMMA WellFormedCondition2 ==
    ASSUME NEW m \in Message, OneB(m),
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => OneA(y)
    PROVE  \A y \in Tran(m) :
            m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm

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

-----------------------------------------------------------------------------
\* TODO rename
LEMMA WellFormedCondition111 ==
    ASSUME NEW m \in Message,
           WellFormed(m),
           OneB(m)
    PROVE  \A y \in Tran(m) : m # y /\ ~OneA(y) =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm


-----------------------------------------------------------------------------
\* Caught

LEMMA CaughtTran ==
    ASSUME NEW y \in Message,
           NEW x \in Tran(y)
    PROVE  Caught(x) \in SUBSET Caught(y)

-----------------------------------------------------------------------------
\* Connected

LEMMA ConnectedLearner ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message
    PROVE  Con(alpha, x) \in SUBSET Learner

\* TODO unify naming
LEMMA ConnectedSym ==
    ASSUME NEW alpha \in Learner,
           NEW beta \in Learner,
           NEW m \in Message,
           alpha \in Con(beta, m)
    PROVE  beta \in Con(alpha, m)

LEMMA ConTran ==
    ASSUME NEW y \in Message,
           NEW alpha \in Learner,
           NEW x \in Tran(y)
    PROVE  Con(alpha, y) \in SUBSET Con(alpha, x)

LEMMA Con_compat ==
    ASSUME NEW x \in Message
    PROVE  \A alpha, beta \in Learner :
            beta \in Con(alpha, x) => Con(alpha, x) = Con(beta, x)

LEMMA ConFinite ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message
    PROVE  /\ IsFiniteSet(Con(alpha, x))
           /\ Cardinality(Con(alpha, x)) =< N_L

LEMMA ConnectedXXX ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW m \in Message,
           Caught(m) \cap SafeAcceptor = {}
    PROVE  beta \in Con(alpha, m)

LEMMA ConAllCaught ==
    ASSUME NEW alpha \in Learner,
           NEW beta \in Learner,
           NEW x \in Message,
           beta \in Con(alpha, x),
           FakeAcceptor \in SUBSET Caught(x)
    PROVE  <<alpha, beta>> \in Ent

-----------------------------------------------------------------------------
\* TODO this subsection depends on HPaxos_2_Specs

LEMMA ChosenBalVal ==
    ASSUME BVal \in [Ballot -> Value],
           KnownMsgsSpec1,
           TypeOK,
           NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           ChosenIn(alpha, bal, val)
    PROVE  \A x \in Message : B(x, bal) => V(x, val)

-----------------------------------------------------------------------------
\* TODO this subsection depends on HPaxos_2_Specs

\* TODO rename
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

-----------------------------------------------------------------------------
\* TODO this subsection depends on HPaxos_2_Specs

LEMMA EntConnectedByQuorum ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  ConByQuorum(alpha, beta, m, SafeAcceptor)

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  beta \in Con(alpha, m)

-----------------------------------------------------------------------------

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

\* TODO rename Ent -> ""
\* TODO remove -- implies by LiveQuorumConIntersectionBis
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

\* TODO rename Quorum -> LiveQuorum
\* TODO check if implies by the lemmas above
LEMMA EntQuorumIntersection ==
    ASSUME NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW Qalpha \in SUBSET Message, NEW Qbeta \in SUBSET Message,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive
    PROVE  \E p \in SafeAcceptor, ma \in Qalpha, mb \in Qbeta :
            /\ ma.acc = p
            /\ mb.acc = p

-----------------------------------------------------------------------------

\* TODO fix the proof
LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK, KnownMsgsSpec2, MsgsSafeAcceptorPrevTranLinearSpec
    PROVE  CaughtSpec

-----------------------------------------------------------------------------

LEMMA ConSeqContainsEmpty ==
    ASSUME NEW alpha \in Learner
    PROVE  << >> \in ConSeq(alpha)

LEMMA ConSeqNonTrivial ==
    ASSUME NEW alpha \in Learner,
           <<alpha, alpha>> \in Ent
    PROVE  \E seq \in ConSeq(alpha) : seq # << >>

LEMMA ConSeqBound ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in ConSeq(alpha)
    PROVE  Len(seq) =< N_L

LEMMA ConSeqMaxDepth ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in ConSeq(alpha)
    PROVE  Len(seq) =< maxDepth(alpha)

-----------------------------------------------------------------------------

LEMMA Qd_eq ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  qd(alpha, x, d) =
            IF TwoA(x) THEN (
                IF d = 0 THEN {}
                ELSE (
                    IF d = 1 THEN
                        { m \in Tran(x) :
                            /\ SameBallot(m, x)
                            /\ OneB(m)
                            /\ Fresh000(alpha, m) }
                    ELSE
                        { m \in Tran(x) :
                            /\ SameBallot(m, x)
                            /\ TwoA(m)
                            /\ [ lr |-> alpha, q  |-> { z.acc : z \in qd(alpha, m, d - 1) } ] \in TrustLive }
                )
            )
            ELSE {}

LEMMA QdProperty1 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  \A y \in qd(alpha, x, d) :
            /\ y \in Tran(x)
            /\ ~Proposal(y)
            /\ SameBallot(y, x)

LEMMA QdProperty4 ==
    ASSUME NEW alpha \in Learner,
           Accurate(alpha),
           NEW m \in Message,
           NEW d \in Nat, 1 =< d,
           NEW d1 \in Nat, d =< d1
    PROVE  [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, d1) }] \in TrustLive =>
           [lr |-> alpha, q |-> { mm.acc : mm \in qd(alpha, m, d) }] \in TrustLive

=============================================================================
\* Modification History
\* Last modified Thu Jun 05 12:13:58 CEST 2025 by karbyshev
\* Created Tue May 20 22:46:05 CEST 2025 by karbyshev
