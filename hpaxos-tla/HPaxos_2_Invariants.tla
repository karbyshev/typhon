------------------------ MODULE HPaxos_2_Invariants ------------------------
EXTENDS HPaxos_2_Specs

-----------------------------------------------------------------------------

LEMMA WellFormedMessage ==
    ASSUME NEW M, WellFormed(M) PROVE M \in Message

LEMMA TypeOKInvariant ==
    TypeOK /\ NextTLA => TypeOK'

LEMMA Sent_monotone ==
    TypeOK /\ NextTLA => msgs \in SUBSET msgs'

LEMMA UniqueMessageSent ==
    TypeOK /\ NextTLA =>
    \A m1, m2 \in msgs' \ msgs : m1 = m2

LEMMA Qd_monotone ==
    ASSUME NEW alpha \in Learner,
           NEW m \in Message,
           NEW d \in Nat,
           BVal' = BVal
    PROVE  qd(alpha, m, d) = qd(alpha, m, d)'

LEMMA WellFormed_monotone ==
    ASSUME UNCHANGED BVal
    PROVE  \A m \in Message : WellFormed(m) <=> WellFormed(m)'

LEMMA KnownMsgMonotone ==
    TypeOK /\ NextTLA =>
    \A AL \in SafeAcceptor \cup Learner :
        known_msgs[AL] \in SUBSET known_msgs[AL]'

LEMMA Known2aMonotone ==
    TypeOK /\ NextTLA =>
    \A L \in Learner, bal \in Ballot, val \in Value :
        Known2a(L, bal, val) \in SUBSET Known2a(L, bal, val)'

LEMMA RecentMsgsSpec1Invariant ==
    TypeOK /\ RecentMsgsSpec1 /\ NextTLA =>
    RecentMsgsSpec1'

LEMMA DecisionSpecInvariant ==
    UNCHANGED BVal /\ MaxDepthSpec /\
    TypeOK /\ NextTLA /\
    KnownMsgsSpec2 /\
    DecisionSpec => DecisionSpec'

LEMMA SafeAcceptorPrevSpec1Invariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 =>
    SafeAcceptorPrevSpec1'

LEMMA SafeAcceptorPrevSpec2Invariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 =>
    SafeAcceptorPrevSpec2'

LEMMA KnownMsgsSpec1Invariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 =>
    KnownMsgsSpec1'

LEMMA KnownMsgsSpec2Invariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 /\
    KnownMsgsSpec2 =>
    KnownMsgsSpec2'

LEMMA MsgsSafeAcceptorPrevTranLinearSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevTranLinearSpec =>
    MsgsSafeAcceptorPrevTranLinearSpec'

LEMMA MsgsSafeAcceptorSpec3Invariant ==
    TypeOK /\ NextTLA /\
    MsgsSafeAcceptorPrevRefSpec /\
    MsgsSafeAcceptorPrevTranSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorSpec3 => MsgsSafeAcceptorSpec3'

LEMMA MsgsSafeAcceptorPrevRefSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevRefSpec =>
    MsgsSafeAcceptorPrevRefSpec'

LEMMA MsgsSafeAcceptorPrevTranSpecInvariant ==
    TypeOK /\ NextTLA /\
    SafeAcceptorPrevSpec2 /\
    MsgsSafeAcceptorPrevTranSpec =>
    MsgsSafeAcceptorPrevTranSpec'

LEMMA KnownMsgsPrevTranSpecInvariant ==
    TypeOK /\ NextTLA /\
    KnownMsgsSpec1 /\
    KnownMsgsSpec2 /\
    KnownMsgsPrevTranSpec =>
    KnownMsgsPrevTranSpec'

=============================================================================
\* Modification History
\* Last modified Tue May 20 23:35:11 CEST 2025 by karbyshev
\* Created Tue May 20 23:06:45 CEST 2025 by karbyshev
