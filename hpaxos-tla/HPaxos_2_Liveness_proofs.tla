---------------------- MODULE HPaxos_2_Liveness_proofs ----------------------

EXTENDS HMessageTheorems,
        HPaxos_2_Structures,
        HPaxos_2_Safety,
        TLAPS

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetTheorems

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

\*    ReplyType(m, t) ==
\*        \/ OneA(m) /\ t = "1b"
\*        \/ OneB(m) /\ t = "2a"
\*        \/ TwoA(m) /\ t = "2a"
\*
\*    Reply(new, m, acc) ==
\*        /\ ReplyType(m, new.type)
\*        /\ new.acc = acc
\*        /\ new.prev = prev_msg[acc]
\*        /\ new.refs = recent_msgs[acc] \cup {m}
\*        /\ WellFormed(new)

\*RecentMsgsSpec3 ==
\*    \A A \in SafeAcceptor :
\*        recent_msgs[A] = known_msgs[A]

\*    KnownRefs(a, m) == \A r \in m.refs : r \in known_msgs[a]

\*KnownMsgsSpec2 ==
\*    \A AL \in SafeAcceptor \cup Learner :
\*        /\ \A M \in known_msgs[AL] :
\*            /\ KnownRefs(AL, M)
\*            /\ WellFormed(M)
\*            /\ Tran(M) \in SUBSET known_msgs[AL]
\*            /\ \E b \in Ballot : B(M, b)

LEMMA ProposalReplyExistence ==
    ASSUME TypeOK,
           SentFinite,
           RecentMsgsSpec1,
           RecentMsgsSpec4,
           SafeAcceptorPrevSpec2,
           KnownMsgsSpec2,
           NEW acc \in SafeAcceptor,
           NEW p \in Message,
           Proposal(p),
           KnownRefs(acc, p),
           NEW bal \in Ballot,
           B(p, bal),
           BallotStrictUpperBound(recent_msgs[acc], bal)
    PROVE  \E msg \in Message : Reply(msg, p, acc)
PROOF
<1> acc \in Acceptor
    BY DEF Acceptor
<1> DEFINE reply == [ type |-> "1b", acc |-> acc, prev |-> prev_msg[acc], refs |-> recent_msgs[acc] \cup {p}, lrns |-> {} ]
<1> reply.lrns = {}
    OBVIOUS
<1> reply \in Message /\ OneB(reply)
  <2> IsFiniteSet(recent_msgs[acc] \cup {p})
      BY FS_Subset, FS_Union, FS_Singleton DEF RecentMsgsSpec1, SentFinite
  <2> QED BY OneB_Message DEF TypeOK
<1> p \in Tran(reply)
    BY Tran_refl, Tran_trans, Tran_eq
<1> Reply(reply, p, acc)
  <2> ReplyType(p, "1b")
      BY DEF ReplyType, OneA, Proposal
  <2> WellFormed(reply)
    <3>bal. \E b \in Ballot : B(reply, b)
      <4> QED BY B_exists DEF Proposal, OneA
    <3>chain. ChainRef(reply)
      <4> CASE prev_msg[acc] = NoMessage
          BY DEF ChainRef
      <4> CASE prev_msg[acc] # NoMessage
        <5> prev_msg[acc] \in Message
            BY DEF TypeOK
        <5> QED BY DEF ChainRef, SafeAcceptorPrevSpec2, SentBy
      <4> QED OBVIOUS
    <3>q. {} = { alpha \in Learner :
                [lr |-> alpha, q |-> {mm.acc : mm \in qd(alpha, reply, 1)}] \in TrustLive }
        <4> ~TwoA(reply)
            BY MessageTypeSpec
        <4> \A alpha \in Learner : qd(alpha, reply, 1) = {}
            BY Qd_eq
        <4> QED BY Zenon, TrustLiveNonEmpty
    <3>wf. WellFormed1b(reply)
      <4> PICK bal0 \in Ballot : B(reply, bal0)
          BY <3>bal
      <4> bal =< bal0
          BY TranBallot_bis DEF BallotUpperBound
      <4> SUFFICES ASSUME NEW y \in Tran(reply),
                          reply # y,
                          SameBallot(reply, y)
          PROVE  Proposal(y)
          BY DEF WellFormed1b
      <4>0. Tran(reply) = {reply} \cup (UNION {Tran(r) : r \in recent_msgs[acc] \cup {p}})
            BY Tran_eq
      <4>1. CASE y \in Tran(p)
        <5>0. CASE y = p
              BY <5>0
        <5>1. CASE \E r \in p.refs : y \in Tran(r)
          <6> PICK r \in p.refs : y \in Tran(r)
                BY <5>1
          <6> r \in Message
              BY MessageSpec
\*          <6>1. r \in Tran(p)
\*                BY Tran_refl, Tran_eq
          <6> PICK br \in Ballot : B(r, br)
              BY DEF KnownRefs, KnownMsgsSpec2
          <6> PICK by \in Ballot : B(y, by)
              BY DEF KnownRefs, KnownMsgsSpec2
            <6> QED BY DEF Proposal, OneA, RecentMsgsSpec3, KnownMsgsSpec2, KnownRefs
        <5> QED BY <4>1, <5>0, <5>1, Tran_eq
      <4>2. CASE \E r \in recent_msgs[acc] : y \in Tran(r)
        <5> PICK r \in recent_msgs[acc] : y \in Tran(r)
            BY <4>2
        <5> r \in known_msgs[acc]
            BY DEF RecentMsgsSpec3
        <5> r \in Message
            BY MessageSpec
        <5> r \in Tran(reply)
            BY Tran_eq, Tran_refl, Tran_trans
        <5> PICK br \in Ballot : B(r, br)
            BY DEF KnownMsgsSpec2
        <5> PICK by \in Ballot : B(y, by)
            BY DEF KnownRefs, KnownMsgsSpec2
        <5> by =< br
            BY TranBallot_bis DEF BallotUpperBound
        <5> br =< bal0
            BY TranBallot_bis DEF BallotUpperBound
        <5> by = bal0
            BY B_func DEF SameBallot
        <5> br = bal0
            BY DEF Ballot
        <5> br < bal
            BY DEF BallotStrictUpperBound
        \* Hence, br < bal <= bal0, contradiction with br = bal0.
        <5> QED BY DEF Ballot
      <4> QED BY <4>0, <4>1, <4>2
    <3> HIDE DEF reply
    <3> QED BY <3>bal, <3>chain, <3>q, <3>wf, MessageTypeSpec DEF WellFormed
  <2> QED BY DEF Reply
<1> HIDE DEF reply
<1> WITNESS reply \in Message
<1> QED OBVIOUS

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
        BY B_1a_refs, <2>1 DEF OneA, Proposal
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
        BY B_1a_refs, <2>1 DEF OneA, Proposal
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

\*LEMMA SameBallotValue ==
\*    ASSUME NEW x \in Message,
\*           NEW y \in Message,
\*           NEW bal \in Ballot, B(x, bal),
\*           SameBallot(x, y)
\*    PROVE  SameValue(x, y)

LEMMA OneB_reply ==
    ASSUME NEW alpha \in Learner,
           NEW p \in Message,
           Proposal(p),
           NEW bal \in Ballot,
           B(p, bal),
           \A m \in Latest({ mm \in Tran(p) : D(alpha, p, mm) }) : SameValue(m, p),
           NEW m1b \in Message,
           OneB(m1b),
           WellFormed(m1b),
           m1b \notin CaughtMsg(m1b), \* <--- !!!
           p \in m1b.refs,
           m1b.refs \in SUBSET Tran(p)
    PROVE  Fresh(alpha, m1b)
PROOF
<1> Tran(m1b) = {m1b} \cup Tran(p)
    BY Tran_eq, Tran_trans
<1> {mm \in Tran(p) : D(alpha, p, mm)} = {mm \in Tran(m1b) : D(alpha, m1b, mm)}
\*<1> {mm \in Tran(m1b) : D(alpha, m1b, mm)} \in SUBSET {mm \in Tran(p) : D(alpha, p, mm)}
  <2>1. ~D(alpha, m1b, m1b)
    <3> ~TwoA(m1b)
        BY MessageTypeSpec
    <3> \A beta \in Learner : qd(beta, m1b, 1) = {}
        BY Qd_eq
    <3> m1b.lrns = {}
        BY TrustLiveNonEmpty DEF WellFormed
    <3> QED BY DEF D
  <2>2. {mm \in Tran(m1b) : D(alpha, m1b, mm)} \in SUBSET {mm \in Tran(p) : D(alpha, p, mm)}
        BY <2>1, ConTran DEF D
  <2>3. {mm \in Tran(p) : D(alpha, p, mm)} \in SUBSET {mm \in Tran(m1b) : D(alpha, m1b, mm)}
    <3> SUFFICES ASSUME NEW mm \in Tran(p), D(alpha, p, mm)
                 PROVE  D(alpha, m1b, mm)
        OBVIOUS
    <3> SUFFICES Con(alpha, p) = Con(alpha, m1b)
        BY DEF D
    <3> SUFFICES Con(alpha, p) \in SUBSET Con(alpha, m1b)
        BY ConTran
    <3> SUFFICES Caught(p) = Caught(m1b)
        BY DEF Con, ConByQuorum
    <3> SUFFICES CaughtMsg(p) = CaughtMsg(m1b)
        BY DEF Caught
    <3> QED BY DEF CaughtMsg \* this step uses the assumption `m1b \notin CaughtMsg(m1b)`
  <2> QED BY <2>2, <2>3
<1> SameValue(p, m1b)
  <2> SameBallot(p, m1b)
    <3> SUFFICES B(m1b, bal)
        BY SameBallot_B
    <3> SUFFICES Get1a(m1b) = Get1a(p)
        BY DEF B
    <3> ~OneA(m1b)
        BY MessageTypeSpec
    <3> QED BY DEF Get1a
  <2> QED BY SameBallotValue
<1> QED BY DEF Fresh, SameValue

Prophecy(f) == \A acc \in SafeAcceptor : (known_msgs[acc] \in SUBSET f[acc])

MSpec(safe_msgs, bal, val, safe, M) ==
            \* (0) M is a subset of sent messages, and
            \* (1) M covers all the messages of the smaller ballot number that will ever be received by safe acceptors
            /\ (\A acc \in SafeAcceptor :
                \A x \in safe_msgs[acc] :
                \A xbal \in Ballot :
                    B(x, xbal) /\ xbal < bal => x \in M)
            \* (2) assume that the proposal p has "just" been proposed and it is the last proposal that will ever be heard by a safe acceptor
            /\ LET p == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ] IN
                /\ p \in msgs
                /\ V(p, val) \* val = BVal(bal)
                /\ (\A acc \in SafeAcceptor :
                    \A x \in safe_msgs[acc] :
                    \A xbal \in Ballot :
                        Proposal(x) /\ B(x, xbal) /\ bal =< xbal => x = p)
            /\ M \in SUBSET known_msgs[safe]
            ~> \E m1b \in msgs : OneB(m1b) /\ m1b.acc = safe /\ B(m1b, bal)


\*    ReplyType(m, t) ==
\*        \/ OneA(m) /\ t = "1b"
\*        \/ OneB(m) /\ t = "2a"
\*        \/ TwoA(m) /\ t = "2a"
\*
\*    Reply(new, m, acc) ==
\*        /\ ReplyType(m, new.type)
\*        /\ new.acc = acc
\*        /\ new.prev = prev_msg[acc]
\*        /\ new.refs = recent_msgs[acc] \cup {m}
\*        /\ WellFormed(new)

THEOREM Attempt1 ==
    ASSUME NEW safe_msgs \in [SafeAcceptor -> SUBSET Message],
           [] Prophecy(safe_msgs)
    PROVE  Spec /\ WF_vars(Next)
           =>
           \A bal \in Ballot :
           \A val \in Value :
           \A safe \in SafeAcceptor :
           \A M \in SUBSET msgs :
            MSpec(safe_msgs, bal, val, safe, M)
PROOF

<1> SUFFICES ASSUME NEW bal \in Ballot,
                    NEW val \in Value,
                    NEW safe \in SafeAcceptor,
                    NEW M \in SUBSET msgs
             PROVE  Spec /\ WF_vars(Next) => MSpec(safe_msgs, bal, val, safe, M)
    BY Isa
<1> safe \in Acceptor
    BY DEF Acceptor
<1> DEFINE F ==
        /\ (\A acc \in SafeAcceptor :
            \A x \in safe_msgs[acc] :
            \A xbal \in Ballot :
                B(x, xbal) /\ xbal < bal => x \in M)
        /\ LET p == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ] IN
            /\ p \in msgs
            /\ V(p, val)
            /\ (\A acc \in SafeAcceptor :
                    \A x \in safe_msgs[acc] :
                    \A xbal \in Ballot :
                        Proposal(x) /\ B(x, xbal) /\ bal =< xbal => x = p)
        /\ M \in SUBSET known_msgs[safe]
<1> DEFINE G == \E m1b \in msgs : OneB(m1b) /\ m1b.acc = safe /\ B(m1b, bal)
<1> SUFFICES []FullSafetyInvariant /\ [][Next]_vars /\ WF_vars(Next) => F ~> G
    BY PTL, FullSafetyInvariant_always DEF Spec, MSpec
<1> SUFFICES [][Next]_vars /\ WF_vars(Next) => ((FullSafetyInvariant /\ F) ~> G)
    BY PTL
\*  <2>2. (TypeOK /\ F) /\ [Next]_vars => ((TypeOK' /\ F') \/ G')
\*        BY invariant DEF Next, vars

\* F ~> G == [](F => <>G)
\* WF_vars(A) == []([] ENABLED A => <> <A>_vars)

\*  <2> SUFFICES []TypeOK /\ [][Next]_vars /\ WF_vars(Next) => (<>F => <>G)
\*      BY PTL
\*  <2> SUFFICES [][Next]_vars /\ WF_vars(Next) => ((TypeOK /\ F) ~> G)
\*      BY PTL
\*  <2>2. (TypeOK /\ F) /\ [Next]_vars => ((TypeOK' /\ F') \/ G')
\*        BY invariant DEF Next, vars
\*  <2>3. (TypeOK /\ F) /\ <<Next>>_vars => G'
\*        BY DEF Next, vars
\*  <2>4. TypeOK /\ F => ENABLED <<Next>>_vars
\*        BY enabled
\*  <2> HIDE DEF F, G
\*  <2> QED BY <2>2, <2>3, <2>4, PTL
<1>2. (FullSafetyInvariant /\ F) /\ [Next]_vars => ((FullSafetyInvariant' /\ F') \/ G')
\*      BY FullSafetyInvariantNext, Sent_monotone DEF Next, vars
<1>3. (FullSafetyInvariant /\ F) /\ <<Next>>_vars => G'
\*        BY DEF Next, vars
\*<1>4. FullSafetyInvariant /\ F => ENABLED <<Next>>_vars
<1>4. FullSafetyInvariant /\ F => ENABLED <<Process(safe, [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ])>>_vars
  <2> SUFFICES ASSUME FullSafetyInvariant, F
               PROVE  ENABLED <<Process(safe, [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ])>>_vars
      OBVIOUS
  <2> M \in SUBSET Message
      BY DEF FullSafetyInvariant, KnownMsgsSpec1, TypeOK
  <2> IsFiniteSet(M)
      BY FS_Subset DEF FullSafetyInvariant, KnownMsgsSpec1
\*MessageRec1(M, n) ==
\*    M
\*    \cup [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, refs : FINSUBSET(M) ]
\*    \cup [ type : {"1b", "2a"},
\*           acc  : Acceptor,
\*           prev : M \cup {NoMessage},
\*           refs : FINSUBSET(M),
\*           lrns : SUBSET Learner ]

\*    ReplyType(m, t) ==
\*        \/ OneA(m) /\ t = "1b"
\*        \/ OneB(m) /\ t = "2a"
\*        \/ TwoA(m) /\ t = "2a"
\*
\*    Reply(new, m, acc) ==
\*        /\ ReplyType(m, new.type)
\*        /\ new.acc = acc
\*        /\ new.prev = prev_msg[acc]
\*        /\ new.refs = recent_msgs[acc] \cup {m}
\*        /\ WellFormed(new)

      <2> p == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ]
      <2> p \in Message
          BY DEF FullSafetyInvariant, TypeOK
      <2> reply == [ type |-> "1b", acc |-> safe, prev |-> prev_msg[safe], refs |-> recent_msgs[safe] \cup {p}, lrns |-> {} ]
      <2> Reply(reply, p, safe)
        <3> ReplyType(p, reply.type)
            BY DEF ReplyType, OneA
        <3> WellFormed(reply)
          <4> prev_msg[safe] \in Message \cup {NoMessage}
              BY DEF FullSafetyInvariant, SafeAcceptorPrevSpec2, SentBy, TypeOK
          <4> recent_msgs[safe] \in SUBSET Message
              BY DEF FullSafetyInvariant, TypeOK
          <4> IsFiniteSet(recent_msgs[safe])
          <4> reply \in Message /\ OneB(reply)
              BY OneB_Message
          <4> QED BY DEF WellFormed
        <3> QED BY DEF Reply
      <2> QED BY ExpandENABLED DEF Process, Recv, vars

\*      BY enabled


<1> QED BY <1>2, <1>3, <1>4, PTL

=============================================================================
\* Modification History
\* Last modified Sat Jul 26 22:46:29 CEST 2025 by karbyshev
\* Created Wed Jun 25 11:47:50 CEST 2025 by karbyshev
