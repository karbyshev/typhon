------------------------------ MODULE HMessage ------------------------------
EXTENDS HQuorum, HLearner, HBallotValue, Lib

-----------------------------------------------------------------------------
(* Messages *)

(* Non-message value *)
NoMessage == [ type |-> "null" ]

MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, refs : {{}} ]

MessageRec1(M, n) ==
    M
    \cup [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, refs : FINSUBSET(M) ]
    \cup [ type : {"1b", "2a"},
           acc  : Acceptor,
           prev : M \cup {NoMessage},
           refs : FINSUBSET(M),
           lrns : SUBSET Learner ]

MessageRec[n \in Nat] ==
    IF n = 0
    THEN MessageRec0
    ELSE MessageRec1(MessageRec[n-1], n)

Message == UNION { MessageRec[n] : n \in Nat }

-----------------------------------------------------------------------------
(* Message types *)

\* TODO clean
Proposal(m) == m.type = "1a"

OneA(m) == m.type = "1a"

OneB(m) == m.type = "1b"

TwoA(m) == m.type = "2a"

-----------------------------------------------------------------------------
(* Transitive references *)

\* Bounded transitive references
TranBound0 == [ m \in Message |-> {m} ]
TranBound1(tr, n) ==
    [m \in Message |-> {m} \cup UNION {tr[r] : r \in m.refs}]

TranBound[n \in Nat] ==
    IF n = 0
    THEN TranBound0
    ELSE TranBound1(TranBound[n-1], n)

Tran(m) == UNION {TranBound[n][m] : n \in Nat}

-----------------------------------------------------------------------------
(* Transitive references of prev *)

\* Bounded transitive references of prev
PrevTranBound0 == [m \in Message |-> {m}]
PrevTranBound1(tr, n) ==
    [m \in Message |-> {m} \cup IF m.prev = NoMessage THEN {} ELSE tr[m.prev]]

PrevTranBound[n \in Nat] ==
    IF n = 0
    THEN PrevTranBound0
    ELSE PrevTranBound1(PrevTranBound[n-1], n)

PrevTran(m) == UNION {PrevTranBound[n][m] : n \in Nat}

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 22:30:29 CEST 2025 by karbyshev
\* Created Tue May 14 16:39:44 CEST 2024 by karbyshev
