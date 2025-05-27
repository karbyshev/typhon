--------------------- MODULE HPaxos_2_Structures_proofs ---------------------
EXTENDS HPaxos_2, HPaxos_2_Specs,
        HMessageTheorems, HLearnerGraphTheorems, LibTheorems,
        SequenceTheorems, SequencesExtTheorems,
        TLAPS

LOCAL INSTANCE FunctionTheorems
LOCAL INSTANCE FiniteSetTheorems

-----------------------------------------------------------------------------

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

-----------------------------------------------------------------------------
\* Facts about Latest

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

-----------------------------------------------------------------------------
\* TODO
LEMMA LearnersWellFormed ==
    ASSUME NEW m \in Message,
           WellFormed(m)
    PROVE  m.lrns # {} <=> TwoA(m)
PROOF
<1> QED

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

-----------------------------------------------------------------------------
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
\* Caught

LEMMA CaughtTran ==
    ASSUME NEW y \in Message,
           NEW x \in Tran(y)
    PROVE  Caught(x) \in SUBSET Caught(y)
PROOF BY Tran_trans DEF Caught, CaughtMsg

-----------------------------------------------------------------------------
\* Connected

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
<1> QED BY LearnerGraphAssumptionTransitivity, LearnerGraphAssumptionClosure
        DEF ConByQuorum 

LEMMA ConFinite ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message
    PROVE  /\ IsFiniteSet(Con(alpha, x))
           /\ Cardinality(Con(alpha, x)) =< N_L
PROOF BY ConnectedLearner, LearnerGraphCard, FS_Subset

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
PROOF
<1> SUFFICES ASSUME x # y PROVE x \in Tran(y) \/ y \in Tran(x)
    BY Tran_refl DEF KnownMsgsSpec1, KnownMsgsSpec2, TypeOK
<1> x \in known_msgs[AL] /\ y \in known_msgs[AL]
    BY DEF KnownMsgsSpec2
<1> QED BY DEF KnownMsgsPrevTranSpec, Caught, CaughtMsg

-----------------------------------------------------------------------------
\* TODO this subsection depends on HPaxos_2_Specs

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
PROOF
<1> /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
    /\ S \cap Caught(M) = {}
    BY DEF ConByQuorum
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qalpha }
                     /\ acc \in { mm.acc : mm \in Qbeta }
    BY TrustLiveAssumption, LearnerGraphAssumptionValidity
<1> QED BY ByzQuorumProperties

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
BY TrustLiveAssumption, LearnerGraphAssumptionValidity DEF Ent

-----------------------------------------------------------------------------

\* TODO fix the proof
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

-----------------------------------------------------------------------------

LEMMA ConSeqContainsEmpty ==
    ASSUME NEW alpha \in Learner
    PROVE  << >> \in ConSeq(alpha)
PROOF BY DEF ConSeq

LEMMA ConSeqNonTrivial ==
    ASSUME NEW alpha \in Learner,
           <<alpha, alpha>> \in Ent
    PROVE  \E seq \in ConSeq(alpha) : seq # << >>
PROOF
<1> PICK bal \in Ballot : TRUE
    BY DEF Ballot

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
    BY PrevTran_1a
<1> HIDE DEF p

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
<1> HIDE DEF oneb

<1> alpha \in Con(alpha, oneb)
  <2> Caught(oneb) = {}
      BY DEF Caught, CaughtMsg
  <2> QED BY ByzQuorumProperties DEF Con, ConByQuorum, Ent

<1> [x \in 1..1 |-> oneb] \in ConSeq(alpha)
    BY SeqDef DEF ConSeq
<1> QED OBVIOUS

LEMMA ConSeqBound ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in ConSeq(alpha)
    PROVE  Len(seq) =< N_L
PROOF
<1> DEFINE P(s) ==
        s # << >> /\
        (\A i, j \in 1..Len(s) : i < j =>
            /\ s[j] \in Tran(s[i])
            /\ Con(alpha, s[j]) # Con(alpha, s[i])) /\
        alpha \in Con(alpha, Head(s)) =>
        Len(s) =< Cardinality(Con(alpha, Last(s)))
<1> SUFFICES ASSUME NEW s1 \in Seq(Message) PROVE P(s1)
  <2> seq \in Seq(Message)
      BY DEF ConSeq
  <2> CASE seq # << >>
    <3> Len(seq) \in Nat
        OBVIOUS
    <3> Len(seq) =< Cardinality(Con(alpha, Last(seq)))
        BY DEF ConSeq
    <3> Last(seq) \in Message
        BY LastProperties
    <3> Con(alpha, Last(seq)) \in SUBSET Learner
        BY ConnectedLearner
    <3> /\ IsFiniteSet(Con(alpha, Last(seq)))
        /\ Cardinality(Con(alpha, Last(seq))) =< Cardinality(Learner)
        BY FS_Subset, LearnerGraphCard
    <3> Cardinality(Con(alpha, Last(seq))) =< N_L
        BY LearnerGraphCard
    <3> QED BY LearnerGraphSize, FS_CardinalityType
  <2> QED BY LearnerGraphSize
<1>0. P(<< >>)
      OBVIOUS
<1>1. \A s \in Seq(Message), msg \in Message : P(s) => P(Append(s, msg))
  <2> SUFFICES ASSUME NEW s \in Seq(Message),
                      NEW msg \in Message,
                      P(s)
               PROVE  P(Append(s, msg))
      OBVIOUS
  <2> DEFINE s2 == Append(s, msg)
  <2> SUFFICES ASSUME \A i, j \in 1..Len(s2) : i < j =>
                        /\ s2[j] \in Tran(s2[i])
                        /\ Con(alpha, s2[j]) # Con(alpha, s2[i]),
                      alpha \in Con(alpha, Head(s2))
               PROVE  Len(s2) =< Cardinality(Con(alpha, Last(s2)))
      OBVIOUS
  <2> CASE s = << >>
    <3> Len(s2) = 1
        BY AppendProperties
    <3> Last(s2) = msg
        BY FrontLastAppend
    <3> Head(s2) = msg
        BY HeadTailAppend
    <3> Cardinality(Con(alpha, msg)) >= 1
      <4> {alpha} \in SUBSET Con(alpha, msg)
          OBVIOUS
      <4> Cardinality({alpha}) = 1
          BY FS_Singleton
      <4> QED BY FS_Subset, ConFinite
    <3> QED OBVIOUS
  <2> CASE s # << >>
    <3> Last(s) \in Message
        BY DEF Last
    <3> Len(s2) = Len(s) + 1
        BY AppendProperties
    <3> Len(s) < Len(s2)
        OBVIOUS
    <3> 1..Len(s) \in SUBSET 1..Len(s2)
        OBVIOUS
    <3> Last(s2) = msg
        BY FrontLastAppend
    <3>IH. Len(s) =< Cardinality(Con(alpha, Last(s)))
           OBVIOUS
    <3> Cardinality(Con(alpha, Last(s))) + 1 =< Cardinality(Con(alpha, Last(s2)))
      <4> Con(alpha, Last(s)) \in SUBSET Con(alpha, Last(s2))
        <5> Last(s2) \in Tran(Last(s))
            BY DEF Last
        <5> QED BY ConTran
      <4> Con(alpha, Last(s)) # Con(alpha, Last(s2))
          BY DEF Last
      <4> IsFiniteSet(Con(alpha, Last(s2)))
          BY ConFinite
      <4> QED BY FS_Subset, FS_CardinalityType, ConFinite
    <3> QED BY <3>IH, FS_CardinalityType, ConFinite
  <2> QED OBVIOUS
<1> HIDE DEF P
<1> QED BY <1>0, <1>1, SequencesInductionAppend, Blast

LEMMA ConSeqMaxDepth ==
    ASSUME NEW alpha \in Learner,
           NEW seq \in ConSeq(alpha)
    PROVE  Len(seq) =< maxDepth(alpha)
PROOF
<1> seq \in Seq(Message)
    BY DEF ConSeq
<1> DEFINE I == { n \in Nat : \E s \in ConSeq(alpha) : n = Len(s) }
<1> Len(seq) \in I
    BY LenProperties
<1> I # {}
    BY ConSeqContainsEmpty
<1> IsFiniteSet(I)
  <2> I \in SUBSET 0..N_L
      BY ConSeqBound
  <2> IsFiniteSet(0..N_L)
      BY InitialSegmentIsFinite, LearnerGraphSize
  <2> QED BY FS_Subset
<1> QED BY Zenon, MaxIsMax, NatFiniteSetMaxExists DEF maxDepth

-----------------------------------------------------------------------------

LEMMA QRec_def ==
    QRec = [n \in Nat |->
                IF n = 0
                THEN QRec0
                ELSE QRec1(QRec[n - 1], n)]
PROOF BY NatInductiveDef, Isa
      DEF NatInductiveDefHypothesis,
          NatInductiveDefConclusion,
          QRec

QRecType(Q) ==
    \A L \in Learner : \A M \in Message :
        \A y \in Tran(M) : Q[<<L, M>>][y] \in SUBSET Message

LEMMA QRec0_spec == QRecType(QRec0)
PROOF BY Tran_Message DEF QRecType, QRec0

LEMMA QRec1_spec ==
    ASSUME NEW v,
           QRecType(v),
           NEW n \in Nat \ {0}
    PROVE  QRecType(QRec1(v, n))
PROOF BY Tran_Message DEF QRecType, QRec1

LEMMA QRec_spec ==
    \A n \in Nat : QRecType(QRec[n])
PROOF
<1> DEFINE P(m) == QRecType(QRec[m])
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0)
      BY QRec0_spec, QRec_def
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m + 1)
      BY <1>1, QRec1_spec, QRec_def
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Qd_spec ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  qd(alpha, x, d) \in SUBSET Message
PROOF BY QRec_spec, Tran_refl DEF qd, QRecType

LEMMA QRec_eq_0 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW y \in Message
    PROVE  QRec[0][<<alpha, x>>][y] = {}
PROOF BY QRec_def DEF QRec0

LEMMA QRec_eq_1 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW y \in Tran(x)
    PROVE  QRec[1][<<alpha, x>>][y] =
            { m \in Tran(y) :
                /\ SameBallot(m, y)
                /\ OneB(m)
                /\ Fresh000(alpha, m) }
PROOF BY QRec_def, Tran_refl DEF QRec1

LEMMA QRec_eq_2 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW y \in Tran(x),
           NEW n \in Nat,
           1 < n
    PROVE  QRec[n][<<alpha, x>>][y] =
            { m \in Tran(y) :
                /\ SameBallot(m, y)
                /\ TwoA(m)
                /\ [ lr |-> alpha, q  |-> { z.acc : z \in QRec[n - 1][<<alpha, x>>][m] } ] \in TrustLive }
PROOF BY QRec_def, Tran_refl DEF QRec1

LEMMA QRec_compat ==
    ASSUME NEW alpha \in Learner
    PROVE  \A n \in Nat :
            \A x, y \in Message :
            \A z \in Tran(x) \cap Tran(y) :
                QRec[n][<<alpha, x>>][z] = QRec[n][<<alpha, y>>][z]
PROOF
<1> DEFINE P(k) ==
        \A x, y \in Message :
            \A z \in Tran(x) \cap Tran(y) :
                QRec[k][<<alpha, x>>][z] = QRec[k][<<alpha, y>>][z]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j)
    OBVIOUS
<1>0. P(0)
      BY QRec_eq_0, Tran_Message
<1>1. ASSUME NEW h \in Nat, P(h) PROVE P(h + 1)
  <2>1. CASE h = 0
        BY <2>1, QRec_eq_1
  <2>2. CASE h > 0
    <3> SUFFICES ASSUME NEW x \in Message,
                        NEW y \in Message,
                        NEW z \in Tran(x),
                        z \in Tran(y)
                 PROVE  QRec[h + 1][<<alpha, x>>][z] = QRec[h + 1][<<alpha, y>>][z]
        OBVIOUS
    <3> 1 < h + 1
        BY <2>2
    <3> h + 1 \in Nat
        BY <1>1
    <3> SUFFICES
        { m \in Tran(z) :
            /\ SameBallot(m, z)
            /\ TwoA(m)
            /\ [lr |-> alpha,
                q  |-> { w.acc : w \in QRec[(h + 1) - 1][<<alpha, x>>][m] }] \in TrustLive } =
        { m \in Tran(z) :
            /\ SameBallot(m, z)
            /\ TwoA(m)
            /\ [lr |-> alpha,
                q  |-> { w.acc : w \in QRec[(h + 1) - 1][<<alpha, y>>][m] }] \in TrustLive }
        BY QRec_eq_2, Isa
    <3> SUFFICES ASSUME NEW m \in Tran(z)
                 PROVE  QRec[h][<<alpha, x>>][m] = QRec[h][<<alpha, y>>][m]
        OBVIOUS
    <3> QED BY <1>1, Tran_trans
  <2> QED BY <2>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

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
PROOF
<1> CASE TwoA(x)
  <2>0. CASE d = 0
        BY <2>0, QRec_eq_0 DEF qd
  <2>1. CASE d = 1
        BY <2>1, QRec_eq_1, Tran_refl, Isa DEF qd
  <2>2. CASE d > 1
    <3> DEFINE qd1(L, M, DD) == qd(L, M, DD)
    <3> SUFFICES qd(alpha, x, d) = { m \in Tran(x) :
                        /\ SameBallot(m, x)
                        /\ TwoA(m)
                        /\ [ lr |-> alpha, q  |-> { z.acc : z \in qd1(alpha, m, d - 1) } ] \in TrustLive }
        BY <2>2
    <3> SUFFICES QRec[d][<<alpha, x>>][x] =
                    { m \in Tran(x) :
                        /\ SameBallot(m, x)
                        /\ TwoA(m)
                        /\ [ lr |-> alpha, q  |-> { z.acc : z \in qd1(alpha, m, d - 1) } ] \in TrustLive }
      <4> HIDE DEF qd1
      <4> QED BY DEF qd
    <3> SUFFICES
        { m \in Tran(x) :
            /\ SameBallot(m, x)
            /\ TwoA(m)
            /\ [ lr |-> alpha, q  |-> { z.acc : z \in QRec[d - 1][<<alpha, x>>][m] } ] \in TrustLive } =
        { m \in Tran(x) :
            /\ SameBallot(m, x)
            /\ TwoA(m)
            /\ [ lr |-> alpha, q  |-> { z.acc : z \in qd1(alpha, m, d - 1) } ] \in TrustLive }
        BY QRec_eq_2, <2>2, Tran_refl
    <3> SUFFICES ASSUME NEW m \in Tran(x),
                        TwoA(m)
                 PROVE  QRec[d - 1][<<alpha, x>>][m] = qd1(alpha, m, d - 1)
        OBVIOUS
    <3> m \in Message
        BY Tran_Message
    <3> SUFFICES QRec[d - 1][<<alpha, x>>][m] = QRec[d - 1][<<alpha, m>>][m]
        BY DEF qd
    <3> d - 1 \in Nat
        BY <2>2
    <3> QED BY QRec_compat, Tran_refl
  <2> QED BY <2>0, <2>1, <2>2
<1> QED BY DEF qd

\*LEMMA QuorumNonTwoA ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message,
\*           ~TwoA(x),
\*           NEW d \in Nat
\*    PROVE  qd(alpha, x, d) = {}
\*PROOF BY DEF qd
\*
\*LEMMA QuorumProperty0 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message,
\*           Proposal(x),
\*           NEW d \in Nat
\*    PROVE  qd(alpha, x, d) = {}
\*PROOF BY DEF qd, Proposal, OneA, TwoA

\*LEMMA Qd_eq_0 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message
\*    PROVE  qd(alpha, x, 0) = {}
\*PROOF BY Qd_eq
\*
\*LEMMA Qd_eq_1 ==
\*    ASSUME NEW alpha \in Learner,
\*           NEW x \in Message,
\*           TwoA(x)
\*    PROVE  qd(alpha, x, 1) =
\*            { m \in Tran(x) :
\*                /\ SameBallot(m, x)
\*                /\ OneB(m)
\*                /\ Fresh000(alpha, m) }
\*PROOF BY Qd_eq

\*    QRec0 == [ LM \in Learner \X Message |-> [x \in Message |-> {}] ]
\*
\*    QRec1(Q, n) ==
\*        [ LM \in Learner \X Message |->
\*            LET alpha == LM[1] IN
\*            LET x == LM[2] IN
\*                IF n = 1 THEN
\*                    [ y \in Tran(x) |->
\*                        { m \in Tran(y) :
\*                            /\ SameBallot(m, y)
\*                            /\ OneB(m)
\*                            /\ Fresh000(alpha, m) } ]
\*                ELSE
\*                    [ y \in Tran(x) |->
\*                        { m \in Tran(y) :
\*                            /\ SameBallot(m, y)
\*                            /\ [ lr |-> alpha,
\*                                 q  |-> { z.acc : z \in Q[LM][m] } ] \in TrustLive } ]
\*        ]
\*
\*    QRec[n \in Nat] ==
\*        IF n = 0 THEN QRec0 ELSE QRec1(QRec[n - 1], n)
\*
\*    \* Quorum of messages referenced by 2a for a learner instance
\*    qd(alpha, x, d) ==
\*        IF TwoA(x) THEN QRec[d][<<alpha, x>>][x] ELSE {}

LEMMA QdProperty1 ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW d \in Nat
    PROVE  \A y \in qd(alpha, x, d) :
            /\ y \in Tran(x)
            /\ ~Proposal(y)
PROOF BY Qd_eq, MessageTypeSpec, Tran_Message DEF OneA, Proposal


=============================================================================
\* Modification History
\* Last modified Tue May 27 14:43:20 CEST 2025 by karbyshev
\* Created Tue May 20 22:50:04 CEST 2025 by karbyshev
