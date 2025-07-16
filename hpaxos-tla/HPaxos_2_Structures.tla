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
(* Facts about Get1a, B and V relations *)

LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE  b1 = b2

LEMMA B_def ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m)
    PROVE  \E b \in Ballot : B(m, b)

LEMMA V_func ==
    ASSUME NEW m \in Message,
           NEW v1 \in Value, V(m, v1),
           NEW v2 \in Value, V(m, v2)
    PROVE  v1 = v2

LEMMA V_def ==
    ASSUME NEW m \in Message,
           NEW b \in Ballot, B(m, b)
    PROVE V(m, BVal[b])

LEMMA SameBallot_B ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot,
           B(x, bal),
           B(y, bal)
    PROVE  SameBallot(x, y)

LEMMA SameBallotValue ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           NEW bal \in Ballot, B(x, bal),
           SameBallot(x, y)
    PROVE  SameValue(x, y)

LEMMA TranBallot ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           NEW b1 \in Ballot, NEW b2 \in Ballot,
           B(m1, b1), B(m2, b2)
    PROVE  b2 =< b1

LEMMA B_1a ==
    ASSUME NEW m \in Message,
           OneA(m),
           m.refs = {}
    PROVE  B(m, m.bal)

LEMMA B_1a_refs ==
    ASSUME NEW m \in Message,
           OneA(m),
           BallotUpperBound(m.refs, m.bal)
    PROVE  B(m, m.bal)

LEMMA ReplyNotOneA ==
    ASSUME NEW acc, NEW msg, NEW reply, Reply(reply, msg, acc)
    PROVE ~OneA(reply)

-----------------------------------------------------------------------------
\* Facts about Latest

LEMMA LatestSubset ==
    ASSUME NEW M PROVE Latest(M) \in SUBSET M

LEMMA LatestNonEmpty ==
    ASSUME NEW M \in SUBSET { m \in Message : WellFormed(m) },
           M # {},
           IsFiniteSet(M)
    PROVE  Latest(M) # {}

LEMMA LatestEqBallot ==
    ASSUME NEW M
    PROVE  \A x, y \in Latest(M) : \A bx, by \in Ballot :
            B(x, bx) /\ B(y, by) => bx = by

-----------------------------------------------------------------------------

LEMMA BallotUpperBoundLeq ==
    ASSUME NEW M,
           NEW x \in Ballot,
           BallotUpperBound(M, x)
    PROVE  \A y \in Ballot: x =< y => BallotUpperBound(M, y)

LEMMA BallotUpperBoundExistence ==
    ASSUME NEW M \in SUBSET { m \in Message : WellFormed(m) },
           IsFiniteSet(M)
    PROVE  \E bal \in Ballot : BallotUpperBound(M, bal)

-----------------------------------------------------------------------------

LEMMA WellFormedOneBProperty ==
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

LEMMA CaughtCon ==
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
    ASSUME KnownMsgsSpec1,
           TypeOK,
           NEW alpha \in Learner,
           NEW bal \in Ballot,
           NEW val \in Value,
           ChosenIn(alpha, bal, val)
    PROVE  \A x \in Message : B(x, bal) => V(x, val)

-----------------------------------------------------------------------------
\* TODO this subsection depends on HPaxos_2_Specs

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW alpha \in Learner, NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  beta \in Con(alpha, m)

-----------------------------------------------------------------------------

LEMMA LiveQuorumEntIntersection ==
    ASSUME NEW alpha \in Learner,
           NEW beta \in Learner,
           <<alpha, beta>> \in Ent,
           NEW Qalpha \in SUBSET Message,
           NEW Qbeta \in SUBSET Message,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive
    PROVE  \E p \in SafeAcceptor, ma \in Qalpha, mb \in Qbeta :
            /\ ma.acc = p
            /\ mb.acc = p

LEMMA LiveQuorumConIntersection ==
    ASSUME TypeOK,
           NEW alpha \in Learner,
           NEW beta \in Learner,
           NEW Qalpha \in SUBSET Message,
           NEW Qbeta \in SUBSET Message,
           [lr |-> alpha, q |-> { mm.acc : mm \in Qalpha }] \in TrustLive,
           [lr |-> beta, q |-> { mm.acc : mm \in Qbeta }] \in TrustLive,
           NEW M \in Message,
           beta \in Con(alpha, M)
    PROVE  \E p \in Acceptor, ma \in Qalpha, mb \in Qbeta :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p

-----------------------------------------------------------------------------

LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK,
           KnownMsgsSpec1,
           KnownMsgsSpec2,
           MsgsSafeAcceptorPrevTranLinearSpec
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

LEMMA MaxDepthProperties ==
    ASSUME NEW alpha \in Learner
    PROVE  /\ maxDepth(alpha) \in Nat
           /\ Accurate(alpha) => 1 =< maxDepth(alpha)
           /\ maxDepth(alpha) =< N_L
           /\ \A seq \in ConSeq(alpha) :
                Len(seq) =< maxDepth(alpha)

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
                            /\ Fresh(alpha, m) }
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

-----------------------------------------------------------------------------

LEMMA WellFormedTwoALearners ==
    ASSUME NEW m \in Message,
           WellFormed(m),
           m.lrns # {}
    PROVE  TwoA(m)

=============================================================================
\* Modification History
\* Last modified Tue Jul 08 19:03:57 CEST 2025 by karbyshev
\* Created Tue May 20 22:46:05 CEST 2025 by karbyshev
