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
    /\ BVal \in [Ballot -> Value]

-----------------------------------------------------------------------------
SentBy(acc) == { mm \in msgs : ~OneA(mm) /\ mm.acc = acc }

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
\* TODO convert to a lemma
MaxDepthSpec ==
    \A alpha \in Learner: maxDepth(alpha) \in Nat /\ maxDepth(alpha) >= 1


=============================================================================
\* Modification History
\* Last modified Wed May 21 22:55:48 CEST 2025 by karbyshev
\* Created Tue May 20 23:34:17 CEST 2025 by karbyshev
