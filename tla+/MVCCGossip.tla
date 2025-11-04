------------------------------- MODULE MVCCGossip -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* MVCC + HWM + Gossip-based Safe GC (state-based, AP)                     *)
(***************************************************************************)

CONSTANTS 
    REPLICAS,     \* e.g., {A, B}
    KEYS,         \* e.g., {k}
    TSMAX         \* e.g., 3

ASSUME TSMAX \in Nat \ {0}

(***************************************************************************)
(* Types                                                                   *)
(***************************************************************************)
Version == [origin: REPLICAS, ts: 1..TSMAX, isDel: BOOLEAN]

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
    Store,     \* Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    HWM,       \* HWM   \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    PeerHWM,   \* PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    Removed    \* Removed \in [REPLICAS -> SUBSET Version]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
MaxS(S) == CHOOSE m \in S : \A x \in S : x <= m
MinS(S) == CHOOSE m \in S : \A x \in S : m <= x

VerSet(r, k) == Store[r][k]

\* Applied max ts for origin o at replica r (build the set by existence over keys/versions)
AppliedTS(r, o) == 
    LET S == { t \in 0..TSMAX : 
                 \E k \in KEYS :
                   \E v \in Store[r][k] : v["origin"] = o /\ v["ts"] = t }
    IN IF S = {} THEN 0 ELSE MaxS(S)

\* Visible timestamp for (r,k): max ts among versions present at r for key k
VisibleTS(r, k) == 
    LET S == { v["ts"] : v \in Store[r][k] } 
    IN IF S = {} THEN 0 ELSE MaxS(S)

\* Is current visible value a non-delete?
NonDeleteVisible(r, k) == 
    LET T == VisibleTS(r,k) IN 
    \E v \in Store[r][k] : v["ts"] = T /\ v["isDel"] = FALSE

\* Local GC safe watermark as known by r for origin o
SafeGC(r, o) == 
    LET C == { PeerHWM[r][p][o] : p \in REPLICAS } 
    IN MinS(C)

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)
Init ==
    /\ Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    /\ \A r \in REPLICAS : \A k \in KEYS : Store[r][k] = {}
    /\ HWM \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    /\ \A r \in REPLICAS : \A o \in REPLICAS : HWM[r][o] = 0
    /\ PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    /\ \A r \in REPLICAS : \A p \in REPLICAS : \A o \in REPLICAS : PeerHWM[r][p][o] = 0
    /\ \A r \in REPLICAS : PeerHWM[r] = [PeerHWM[r] EXCEPT ![r] = HWM[r]]
    /\ Removed \in [REPLICAS -> SUBSET Version]
    /\ \A r \in REPLICAS : Removed[r] = {}

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
ApplyOp ==
    \E r \in REPLICAS :
      \E o \in REPLICAS :
        \E k \in KEYS :
          \E ts \in 1..TSMAX :
            \E del \in BOOLEAN :
                LET v == [origin |-> o, ts |-> ts, isDel |-> del] IN
                /\ Store' = [Store EXCEPT ![r] = [Store[r] EXCEPT ![k] = Store[r][k] \cup {v}]]
                /\ HWM'   = [HWM   EXCEPT ![r] = [HWM[r] EXCEPT ![o] = IF ts > HWM[r][o] THEN ts ELSE HWM[r][o]]]
                /\ PeerHWM' = [PeerHWM EXCEPT ![r] = [PeerHWM[r] EXCEPT ![r] = HWM'[r]]]
                /\ Removed' = Removed

Gossip ==
    \E s \in REPLICAS :
      \E r \in REPLICAS :
        /\ s # r
        /\ PeerHWM' = [PeerHWM EXCEPT 
                         ![r] = [PeerHWM[r] EXCEPT 
                                   ![s] = [ o \in REPLICAS |-> 
                                           IF HWM[s][o] >= PeerHWM[r][s][o] 
                                              THEN HWM[s][o] ELSE PeerHWM[r][s][o] ] ] ]
        /\ UNCHANGED << Store, HWM, Removed >>

GC ==
    \E r \in REPLICAS :
      \E k \in KEYS :
        \E v \in Store[r][k] :
            /\ v["ts"] <= SafeGC(r, v["origin"])
            /\ Store'   = [Store EXCEPT ![r] = [Store[r] EXCEPT ![k] = Store[r][k] \ {v}]]
            /\ Removed' = [Removed EXCEPT ![r] = Removed[r] \cup {v}]
            /\ UNCHANGED << HWM, PeerHWM >>

Next == ApplyOp \/ Gossip \/ GC

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
HWMLowerBound == \A r \in REPLICAS : \A o \in REPLICAS : HWM[r][o] >= AppliedTS(r,o)

SelfMirror == \A r \in REPLICAS : PeerHWM[r][r] = HWM[r]

NoZombie == 
    \A r \in REPLICAS : \A k \in KEYS :
        NonDeleteVisible(r,k) => 
            LET T == VisibleTS(r,k) IN ~(\E v \in Store[r][k] : v["isDel"] = TRUE /\ v["ts"] > T)

SafeGCInvariant == 
    \A r \in REPLICAS : \A v \in Removed[r] :
        v["ts"] <= SafeGC(r, v["origin"])

TypeInv ==
    /\ Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    /\ HWM \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    /\ PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    /\ Removed \in [REPLICAS -> SUBSET Version]

Spec == Init /\ [][Next]_<<Store,HWM,PeerHWM,Removed>>

INV == TypeInv /\ HWMLowerBound /\ SelfMirror /\ NoZombie /\ SafeGCInvariant

=============================================================================
