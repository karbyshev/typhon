---------------------- MODULE HPaxos_2_Liveness_proofs ----------------------

EXTENDS HMessageTheorems,
        HPaxos_2_Structures,
        TLAPS

LOCAL INSTANCE FiniteSets

\*    Fresh(alpha, x) == \* alpha : Learner, x : 1b
\*        \A m \in Latest({ mm \in Tran(x) : D(alpha, x, mm) }) : SameValue(m, x)

\*    Fresh(alpha, x) == \* alpha : Learner, x : 1b
\*        \A m \in Latest({ mm \in M : D(alpha, x, mm) }) : V(m, val)

\*    D(alpha, x, m) ==
\*        \* /\ TwoA(m) \* implied by the following since the intersection is non-empty
\*        /\ m.lrns \cap Con(alpha, x) # {}

\*    ConByQuorum(alpha, beta, x, S) == \* alpha : Learner, beta : Learner, x : 1b, S \in ByzQuorum
\*        /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
\*        /\ S \cap Caught(x) = {}
\*
\*    Con(alpha, x) == \* alpha : Learner, x : 1b
\*        { beta \in Learner :
\*            \E S \in ByzQuorum : ConByQuorum(alpha, beta, x, S) }

\*    CaughtMsg(x) ==
\*        { m \in Tran(x) :
\*            /\ ~Proposal(m)
\*            /\ \E m1 \in Tran(x) :
\*                /\ ~Proposal(m1)
\*                /\ m.acc = m1.acc
\*                /\ m # m1
\*                /\ m \notin PrevTran(m1)
\*                /\ m1 \notin PrevTran(m)
\*\*                /\ m.prev = m1.prev
\*\* TODO revert the change?
\*         }
\*
\*    Caught(x) == { m.acc : m \in CaughtMsg(x) }

\*    CaughtMsg(x) ==
\*        { m \in Tran(M) :
\*            /\ ~Proposal(m)
\*            /\ \E m1 \in Tran(M) :
\*                /\ ~Proposal(m1)
\*                /\ m.acc = m1.acc
\*                /\ m # m1
\*                /\ m \notin PrevTran(m1)
\*                /\ m1 \notin PrevTran(m)
\*         }

\*    CaughtMsg(x) ==
\*      CaughtMsgOfSet({x})

\*    CaughtMsgOfSet(M) ==
\*        { m \in Tran(M) :
\*            /\ ~Proposal(m)
\*            /\ \E m1 \in Tran(M) :
\*                /\ ~Proposal(m1)
\*                /\ m.acc = m1.acc
\*                /\ m # m1
\*                /\ m \notin PrevTran(m1)
\*                /\ m1 \notin PrevTran(m)
\*         }

\* {beta \in Learner : \E S \in BQ :
\*        /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
\*        /\ S \cap { m.acc : m \in CaughtMsgOfSet(M) } = {}
\* }

\*    ConOfSet(alpha, M) == \* alpha : Learner, x : 1b
\*        { beta \in Learner :
\*            \E S \in ByzQuorum : ConByQuorumOfSet(alpha, beta, M, S) }

\*    ConByQuorumOfSet(alpha, beta, M, S) == \* alpha : Learner, beta : Learner, M : SUBSET Message, S \in ByzQuorum
\*        /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
\*        /\ S \cap Caught(x) = {}

LEMMA YYY ==
    ASSUME NEW x \in Message,
           NEW y \in Message,
           x.refs = y.refs
    PROVE  Tran(x) \cup {y} = Tran(y) \cup {x}
PROOF BY Tran_eq

LEMMA XXX ==
    ASSUME NEW alpha \in Learner,
           NEW x \in Message,
           NEW y \in Message,
           Proposal(x),
           Proposal(y),
           x.refs = y.refs
    PROVE  Con(alpha, x) = Con(alpha, y)
PROOF
<1>0. Tran(x) \cup {y} = Tran(y) \cup {x}
      BY YYY
<1>2. Caught(x) = Caught(y)
  <2> CaughtMsg(x) = CaughtMsg(y)
      BY <1>0 DEF CaughtMsg
  <2> QED BY DEF Caught
<1> QED BY <1>2 DEF Con, ConByQuorum

LEMMA ValueExistence ==
    ASSUME NEW alpha \in Learner,
           NEW M \in SUBSET { m \in Message : WellFormed(m) },
           IsFiniteSet(M)
    PROVE  \E bal \in Ballot : \E val \in Value : \E x \in Message :
            /\ Proposal(x)
            /\ B(x, bal)
            /\ val = BVal[bal]
            /\ BallotUpperBound(M, bal)
            /\ M \in SUBSET Tran(x)
            /\ \A m \in Latest({ mm \in M : D(alpha, x, mm) }) : V(m, val)
PROOF
<1> M \in SUBSET Message
    OBVIOUS
<1> PICK ybal \in Ballot : TRUE
    BY DEF Ballot
\* Define a proposal with M being its reference set:
<1> DEFINE y == [ type |-> "1a", bal |-> ybal, prev |-> NoMessage, refs |-> M ]
<1> y \in Message /\ Proposal(y)
    BY OneA_Message DEF Proposal, OneA
<1> y.prev = NoMessage
    OBVIOUS
<1> PICK bal0 \in Ballot : BallotUpperBound(M, bal0)
    BY BallotUpperBoundExistence
<1> DEFINE Ly == Latest({ mm \in M : D(alpha, y, mm) })
<1>0. CASE Ly = {}
  <2> PICK val \in Value : TRUE
      BY ValueNonEmpty
  <2> PICK bal \in Ballot : bal0 =< bal /\ val = BVal[bal]
      BY BValValueAssumption
  <2>1. BallotUpperBound(M, bal)
        BY BallotUpperBoundLeq
  <2> DEFINE x == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ]
  <2> x \in Message /\ Proposal(x)
      BY OneA_Message DEF Proposal, OneA
  <2> x.prev = NoMessage
      OBVIOUS
  <2> x.refs = y.refs
      OBVIOUS
  <2>2. B(x, bal)
        BY B_1a_bis, <2>1 DEF OneA, Proposal
  <2>3. Latest({ mm \in M : D(alpha, x, mm) }) = Ly
    <3> HIDE DEF x, y
    <3> QED BY Zenon, XXX DEF D
  <2>4. Latest({ mm \in M : D(alpha, x, mm) }) = {}
        BY <1>0, <2>3
  <2>5. M \in SUBSET Tran(x)
        BY Tran_eq, Tran_refl
  <2> HIDE DEF x
  <2> WITNESS bal \in Ballot, val \in Value, x \in Message
  <2> QED BY <2>1, <2>2, <2>4, <2>5
<1>1. CASE Ly # {}
  <2> PICK m1 \in Latest({ mm \in M : D(alpha, y, mm) }) : TRUE
      BY <1>1
  <2> m1 \in M
      BY LatestSubset
  <2> PICK bal1 \in Ballot : B(m1, bal1)
      BY DEF WellFormed
  <2> DEFINE val == BVal[bal1]
  <2> val \in Value
      BY BValAssumption
  <2> PICK bal \in Ballot : bal1 =< bal /\ bal0 =< bal /\ val = BVal[bal]
      BY BValValueAssumption DEF Ballot
  <2>1. BallotUpperBound(M, bal)
        BY BallotUpperBoundLeq
  <2> DEFINE x == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ]
  <2> x \in Message /\ Proposal(x)
      BY OneA_Message DEF Proposal, OneA
  <2> x.prev = NoMessage
      OBVIOUS
  <2> x.refs = y.refs
      OBVIOUS
  <2>2. B(x, bal)
        BY B_1a_bis, <2>1 DEF OneA, Proposal
  <2>3. Latest({ mm \in M : D(alpha, x, mm) }) = Ly
    <3> HIDE DEF x, y
    <3> QED BY Zenon, XXX DEF D
  <2>4. \A m \in Latest({ mm \in M : D(alpha, x, mm) }) : V(m, val)
    <3> SUFFICES ASSUME NEW m \in Ly PROVE V(m, val)
        BY <2>3
    <3> m \in M
        BY LatestSubset
    <3> PICK bm \in Ballot : B(m, bm)
        BY DEF WellFormed
    <3> QED BY LatestEqBallot, V_def
  <2>5. M \in SUBSET Tran(x)
        BY Tran_eq, Tran_refl
  <2> HIDE DEF x
  <2> WITNESS bal \in Ballot, val \in Value, x \in Message
  <2> QED BY <2>1, <2>2, <2>4, <2>5
<1> QED BY <1>0, <1>1

=============================================================================
\* Modification History
\* Last modified Fri Jun 27 17:29:23 CEST 2025 by karbyshev
\* Created Wed Jun 25 11:47:50 CEST 2025 by karbyshev
