--------------------------- MODULE HPaxos_2_Specs ---------------------------
EXTENDS HPaxos_2

LOCAL INSTANCE FiniteSets

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor -> SUBSET Message]
    /\ prev_msg \in [Acceptor -> Message \cup {NoMessage}]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]

-----------------------------------------------------------------------------
SentBy(acc) == { mm \in msgs : mm.src = acc }

SentSpec ==
    \A A \in SafeAcceptor :
        \A m \in SentBy(A) : ~OneA(m)

SentFinite == IsFiniteSet(msgs)

KnownMsgsSpec1 ==
    \A AL \in SafeAcceptor \cup Learner :
        known_msgs[AL] \in SUBSET msgs

KnownMsgsSpec2 ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ \A M \in known_msgs[AL] :
            /\ KnownRefs(AL, M)
            /\ WellFormed(M)
            /\ Tran(M) \in SUBSET known_msgs[AL]
            /\ \E b \in Ballot : B(M, b)

RecentMsgsSpec1 ==
    \A A \in SafeAcceptor :
        recent_msgs[A] \in SUBSET msgs

\*RecentMsgsSpec2 ==
\*    \A A \in SafeAcceptor :
\*        \A M \in TranSet(recent_msgs[A]) :
\*            M \in known_msgs[A] \/ M = prev_msg[A]

\*RecentMsgsSpec3 ==
\*    \A A \in SafeAcceptor :
\*        known_msgs[A] \in SUBSET TranSet(recent_msgs[A])

RecentMsgsSpec3 ==
    \A A \in SafeAcceptor :
        LET P == IF prev_msg[A] = NoMessage THEN {} ELSE { prev_msg[A] } IN
        known_msgs[A] \cup P = TranSet(recent_msgs[A])

CaughtSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught(M) \cap SafeAcceptor = {}

DecisionSpec ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \in decision[L, BB] => ChosenIn(L, BB, VV)

\* TODO rename
SafeAcceptorPrevSpec1 ==
    \A A \in SafeAcceptor :
        SentBy(A) = {} <=> prev_msg[A] = NoMessage

\* TODO rename
SafeAcceptorPrevSpec2 ==
    \A A \in SafeAcceptor :
        prev_msg[A] # NoMessage =>
            /\ prev_msg[A] \in recent_msgs[A]
            /\ prev_msg[A] \in SentBy(A)
            /\ WellFormed(prev_msg[A])
            /\ \E bal \in Ballot : B(prev_msg[A], bal)
            /\ \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])

\* TODO rename
\* TODO not used with the current definition of Caught
MsgsSafeAcceptorSpec3 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1.prev = m2.prev => m1 = m2

\* TODO used only to prove MsgSafeAcceptorSpec3
\* TODO remove from the FullSafetyInvariant
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
Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

\* TODO check if all used
FullSafetyInvariant ==
    /\ TypeOK
    /\ SentFinite
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

-----------------------------------------------------------------------------
\* Liveness specs

\* TODO refactor
Prophecy_1(f) == \A acc \in SafeAcceptor : (known_msgs[acc] \in SUBSET f[acc])

\* This spec describes:
\* always the case that either the acceptor knows the last propsal P or the ballot of the last proposal is the strict upper bound of the all the messages
\* that the safe acceptor have learned so far (see RecentMsgsSpec3).
\*XXX ==
\*    \A safe \in SafeAcceptor, bal \in Ballot, M \in SUBSET msgs :
\*        \A safe_msgs \in [SafeAcceptor -> SUBSET Message] : \* <- ?
\*        LET p == proposal(pr, bal, M) IN
\*            (
\*            /\ Prophecy_1(safe_msgs)
\*            \* (1) M covers all the messages of the smaller ballot number that will ever be received by safe acceptors
\*            /\ (\A acc \in SafeAcceptor :
\*                \A x \in safe_msgs[acc] :
\*                \A xbal \in Ballot :
\*                    B(x, xbal) /\ xbal < bal => x \in M)
\*            \* (2) assume that the proposal p has "just" been proposed and it is the last proposal that will ever be heard by any safe acceptor
\*            /\ /\ V(p, val) \* val = BVal(bal)
\*               /\ (\A acc \in SafeAcceptor :
\*                   \A x \in safe_msgs[acc] :
\*                   \A xbal \in Ballot :
\*                       Proposal(x) /\ B(x, xbal) /\ bal =< xbal => x = p)
\*\*            /\ M \in SUBSET known_msgs[safe]
\*            ) =>
\*            p \in known_msgs[safe] \/ BallotStrictUpperBound(recent_msgs[acc], bal)

\* all sets of safe messages if propecy(safe_msgs) then
\* given a set of messages M,
\* p = proposal(src=safe, bal=bal, refs=M)
\* p \in known_msgs[safe] /\ ~BallotStrictUpperBound(recent_msgs[acc], bal) for bal = B(p) =>
\* \E reply \in msgs : Reply(reply, p, safe)


-----------------------------------------------------------------------------




\* TODO clean
FullLivenessInvariant ==
    /\ FullSafetyInvariant

=============================================================================
\* Modification History
\* Last modified Wed Jul 30 22:42:40 CEST 2025 by karbyshev
\* Created Tue May 20 23:34:17 CEST 2025 by karbyshev
