------------------------- MODULE HPaxos_2_Liveness -------------------------

EXTENDS HMessage,
        HPaxos_2,
\*        HPaxos_2_Invariants,
        TLAPS

\*LEMMA enabled ==
\*    FullSafetyInvariant => ENABLED <<Next>>_vars
\*PROOF BY ExpandENABLED DEF Next, proposer, vars, TypeOK

\*<1> SUFFICES []FullSafetyInvariant /\ [][Next]_vars /\ WF_vars(Next) =>
\*                \A alpha \in Learner :
\*                \A bal \in Ballot :
\*                \A val \in Value :
\*                \A safe \in SafeAcceptor :
\*                \A M \in SUBSET msgs :
\*                    ((FullSafetyInvariant /\ F(bal, val, M)) ~> G(safe, bal))
\*    BY PTL
\*<1>2. \A alpha \in Learner :
\*      \A bal \in Ballot :
\*      \A val \in Value :
\*      \A safe \in SafeAcceptor :
\*      \A M \in SUBSET msgs :
\*     (FullSafetyInvariant /\ F) /\ [Next]_vars => ((FullSafetyInvariant' /\ F') \/ G')
\*        BY invariant DEF Next, vars

\*    ChosenIn(alpha, b, v) ==
\*        \E S \in SUBSET Known2a(alpha, b, v) :
\*            /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
\*            /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive

THEOREM Liveness ==
    Spec /\ WF_vars(Next) =>
    \A alpha \in Learner :
    \A bal \in Ballot :
    \A val \in Value :
    \A M \in SUBSET msgs :
        \* (0) M is a subset of sent messages, and
        \* (1) M covers all the messages of the smaller ballot number that will ever be received by safe acceptors
        /\ (\A acc \in SafeAcceptor :
            \A x \in Message :
            \A xbal \in Ballot :
                B(x, xbal) /\ xbal < bal /\ (<> (x \in known_msgs[acc])) =>
                x \in M)
        \* (2) assume that the proposal p has "just" been proposed and it is the last proposal that will be ever proposed
        /\ LET p == [ type |-> "1a", bal |-> bal, prev |-> NoMessage, refs |-> M ] IN
            /\ V(p, val) \* val = BVal(bal)
            /\ (\A x \in Message :
                \A xbal \in Ballot :
                    Proposal(x) /\ B(x, xbal) /\ bal =< xbal /\ (<> (x \in msgs)) =>
                    x = p)
        => <> ChosenIn(alpha, bal, val)
    \* We have time windows for every proposer. We assume that the current time window is long enough for:
    \* - every safe acceptor at the beginning of the frame sends all its known messages to the proposer
    \* - the proposer waits until the designated fraction of the time window to receive all the messages and includes them into the proposal.
    \* We can have safe acceptors refuse to listen to any msgs with a smaller ballot number except those message referenced (perhaps indirectly) by 1a sent by the leader
    \* and they forward their messages to the leader.
    \* The leader has to wait long enough so it learns about all messages known to safe acceptors and then propose the received set of messages. 

\*ChosenIn(alpha, b, v) ==
\*        \E S \in SUBSET Known2a(alpha, b, v) :
\*            /\ \A x \in S : [lr |-> alpha, q |-> { m.acc : m \in qd(alpha, x, maxDepth(alpha)) }] \in TrustLive
\*            /\ [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive

=============================================================================
\* Modification History
\* Last modified Mon Jul 07 22:19:10 CEST 2025 by karbyshev
\* Created Mon Jun 09 20:06:52 CEST 2025 by karbyshev
