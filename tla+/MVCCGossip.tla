------------------------------- MODULE MVCCGossip -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* MVCC + HWM + Gossip-based Safe GC (state-based, AP)                     *)
(*                                                                         *)
(* - Replicas apply MVCC versions: Version == [origin \in REPLICAS,        *)
(*                                   ts \in 1..TSMAX, isDel \in BOOLEAN]   *)
(* - Each replica r maintains HWM_r[o] = highest ts from origin o that     *)
(*   r has durably applied.                                                *)
(* - Replicas gossip their HWM vectors; each replica r keeps PeerHWM_r[p]  *)
(*   (the last HWM heard from peer p). We maintain PeerHWM_r[r] == HWM_r.  *)
(* - GC at replica r may remove any version v with v.ts <= Min_p PeerHWM_r[p][v.origin]. *)
(*                                                                         *)
(* Safety we check:                                                        *)
(*   1) NoZombie: if the visible value for (r,k) is non-delete at ts=T,    *)
(*      then there is no delete for (r,k) with ts' > T.                    *)
(*   2) SafeGC: any version that has been removed at r was only removed    *)
(*      after r had (for every peer p) PeerHWM_r[p][v.origin] >= v.ts.     *)
(*   3) MonotoneHWM: HWMs and PeerHWMs never decrease per origin.          *)
(***************************************************************************)

CONSTANTS 
    REPLICAS,     \* e.g., {A, B}
    KEYS,         \* e.g., {k}
    TSMAX         \* e.g., 3

ASSUME TSMAX \in Nat \ {0}

(***************************************************************************)
(* Basic types                                                             *)
(***************************************************************************)
Version == [origin: REPLICAS, ts: 1..TSMAX, isDel: BOOLEAN]

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
    \* Per replica MVCC store: key -> set of versions present at replica r
    Store,         \* Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    \* Per replica HWM (local apply frontier): HWM[r][o] \in 0..TSMAX
    HWM,           \* HWM \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    \* Last gossip heard from peers (for r's GC decisions)
    PeerHWM,       \* PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    \* Ghost set: versions that have been GC-removed at replica r
    Removed        \* Removed \in [REPLICAS -> SUBSET Version]

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
VerSet(r, k) == Store[r][k]

AllVersions == { v \in Version : TRUE }

\* Max ts for origin o at replica r (derived from Store)
AppliedTS(r, o) == 
    LET S == UNION { {v.ts : v \in VerSet(r,k) /\ v.origin = o} : k \in KEYS }
    IN IF S = {} THEN 0 ELSE Max(S)

\* Local visible timestamp for (r,k): max ts among versions present at r for key k
VisibleTS(r, k) == 
    LET S == { v.ts : v \in VerSet(r,k) } 
    IN IF S = {} THEN 0 ELSE Max(S)

\* Is the current visible version a non-delete?
NonDeleteVisible(r, k) == 
    LET T == VisibleTS(r,k) IN 
    \E v \in VerSet(r,k) : v.ts = T /\ v.isDel = FALSE

\* Local GC safe watermark vector as known by replica r:
SafeGC(r, o) == 
    LET C == { PeerHWM[r][p][o] : p \in REPLICAS } 
    IN Min(C)

SafeGCVec(r) == [ o \in REPLICAS |-> SafeGC(r,o) ]

(***************************************************************************)
(* Init                                                                    *)
(***************************************************************************)
Init ==
    /\ Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    /\ \A r \in REPLICAS : \A k \in KEYS : Store[r][k] = {}
    /\ HWM \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    /\ \A r \in REPLICAS : \A o \in REPLICAS : HWM[r][o] = 0
    /\ PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    /\ \A r,p,o \in REPLICAS : PeerHWM[r][p][o] = 0
    /\ \A r \in REPLICAS : PeerHWM[r] = [PeerHWM[r] EXCEPT ![r] = HWM[r]]
    /\ Removed \in [REPLICAS -> SUBSET Version]
    /\ \A r \in REPLICAS : Removed[r] = {}

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Non-deterministically generate a version at origin o with ts in 1..TSMAX, 
\* and deliver/apply it at some replica r (could be the origin or a peer).
ApplyOp ==
    \E r,o \in REPLICAS, k \in KEYS, ts \in 1..TSMAX, del \in BOOLEAN :
        /\ LET v == [origin |-> o, ts |-> ts, isDel |-> del] IN
           /\ Store' = [Store EXCEPT ![r][k] = Store[r][k] \cup {v}]
           /\ HWM'   = [HWM   EXCEPT ![r][o] = Max({HWM[r][o], ts})]
           /\ PeerHWM' = [PeerHWM EXCEPT ![r][r] = HWM'[r]]
           /\ Removed' = Removed
        /\ UNCHANGED << >>

\* Gossip HWM from sender s to receiver r; receiver updates its PeerHWM[s] pointwise-max
Gossip ==
    \E s,r \in REPLICAS :
        /\ s # r
        /\ PeerHWM' = [PeerHWM EXCEPT 
                         ![r][s] = [ o \in REPLICAS |-> 
                                      Max({PeerHWM[r][s][o], HWM[s][o]}) ] ]
        /\ UNCHANGED << Store, HWM, Removed >>

\* GC at replica r removes any version v whose ts <= SafeGC(r, v.origin)
GC ==
    \E r \in REPLICAS, k \in KEYS, v \in VerSet(r,k) :
        /\ v.ts <= SafeGC(r, v.origin)
        /\ Store' = [Store EXCEPT ![r][k] = Store[r][k] \ {v}]
        /\ Removed' = [Removed EXCEPT ![r] = Removed[r] \cup {v}]
        /\ UNCHANGED << HWM, PeerHWM >>

Next == ApplyOp \/ Gossip \/ GC

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* 1) Local HWM agrees with applied ts (lower bound) and never decreases (checked via next-state form)
HWMLowerBound == \A r,o \in REPLICAS : HWM[r][o] >= AppliedTS(r,o)

\* 2) PeerHWM[r][r] == HWM[r] (self mirror, needed for SafeGC min)
SelfMirror == \A r \in REPLICAS : PeerHWM[r][r] = HWM[r]

\* 3) NoZombie: if visible value is non-delete at (r,k), then no delete exists at a higher ts at r
NoZombie == 
    \A r \in REPLICAS : \A k \in KEYS :
        NonDeleteVisible(r,k) => 
            LET T == VisibleTS(r,k) IN ~(\E v \in VerSet(r,k) : v.isDel /\ v.ts > T)

\* 4) SafeGC: anything removed must have been <= min known frontier at the time it was removed.
SafeGCInvariant == 
    \A r \in REPLICAS : \A v \in Removed[r] :
        v.ts <= SafeGC(r, v.origin)

TypeInv ==
    /\ Store \in [REPLICAS -> [KEYS -> SUBSET Version]]
    /\ HWM \in [REPLICAS -> [REPLICAS -> 0..TSMAX]]
    /\ PeerHWM \in [REPLICAS -> [REPLICAS -> [REPLICAS -> 0..TSMAX]]]
    /\ Removed \in [REPLICAS -> SUBSET Version]

INV == TypeInv /\ HWMLowerBound /\ SelfMirror /\ NoZombie /\ SafeGCInvariant

(***************************************************************************)
(* Liveness (optional): exploration only — TLC can check invariants        *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<Store,HWM,PeerHWM,Removed>>

=============================================================================
