# MVCC + HWM + Gossip-based Safe GC (TLA+ Spec)

This is a TLA+ specification modeling a distributed storage system with
MVCC (Multi-Version Concurrency Control), HWM (High Water Mark) tracking,
and gossip-based safe garbage collection.

System Overview
---------------
The model represents a distributed store where:

Multiple replicas can store multiple versions of the same key
Each version has an origin replica, timestamp, and deletion flag
Replicas gossip their state to coordinate safe garbage collection

Key Components
--------------
State Variables:

Store:             Each replica maintains multiple versions per key
HWM:               High water marks tracking the highest timestamp each replica
                   has seen from each origin
PeerHWM:           Each replica's view of other replicas' HWMs (learned
                   through gossip)
Removed:           Tracks versions that have been garbage collected

Actions Being Modeled
---------------------

ApplyOp:          Apply a new write/delete operation, creating a new version
Gossip:           Replicas exchange HWM information to learn about each other's state
GC:               Safely remove old versions based on the minimum HWM across all replicas

Safety Properties Being Checked
-------------------------------
The model verifies several critical invariants:

HWMLowerBound:    HWM is always at least as high as the maximum applied timestamp
SelfMirror:       Each replica's view of its own HWM in PeerHWM matches its actual HWM
NoZombie:         No deleted version can "resurrect" - if a non-delete
                  is visible, no future delete with a higher timestamp exists
SafeGCInvariant:  Only versions below the safe GC watermark are removed

The Core Safety Guarantee
-------------------------
The SafeGC calculation - it takes the minimum HWM for each origin across all replicas
(as known through gossip). This ensures a version is only GC'd when all replicas
have seen at least that timestamp from that origin, preventing data loss in eventually
consistent scenarios. This is checking that the system maintains consistency while
allowing concurrent operations and garbage collection in a distributed, asynchronous
environment - typical challenges in AP (Available, Partition-tolerant) systems.

## 1. System Setup and Data Structures

### Constants and Basic Types
```tla
CONSTANTS
    REPLICAS,     \* e.g., {A, B}
    KEYS,         \* e.g., {k}
    TSMAX         \* e.g., 3
```
- We have multiple replicas (nodes) in the system
- Multiple keys that can be stored
- Timestamps range from 1 to TSMAX

### Version Structure
```tla
Version == [origin: REPLICAS, ts: 1..TSMAX, isDel: BOOLEAN]
```
Each version of a key contains:
- **origin**: Which replica created this version
- **ts**: Timestamp (logical clock)
- **isDel**: Whether this is a delete tombstone

## 2. State Variables Explained

### Store
```tla
Store[replica][key] = {set of versions}
```
Each replica maintains multiple versions for each key. For example:
- Replica A might have `k -> {[origin: A, ts: 1, isDel: FALSE], [origin: B, ts: 2, isDel: TRUE]}`

### HWM (High Water Mark)
```tla
HWM[replica][origin] = highest_timestamp
```
Each replica tracks the highest timestamp it has seen from each origin:
- `HWM[A][B] = 5` means replica A has seen operations from B up to timestamp 5

### PeerHWM (Peer's View of HWMs)
```tla
PeerHWM[replica][peer][origin] = timestamp
```
Three-level mapping tracking what each replica knows about other replicas' HWMs:
- `PeerHWM[A][B][C] = 3` means: "A knows that B has seen operations from C up to timestamp 3"
- This is crucial for safe garbage collection

### Removed
```tla
Removed[replica] = {set of removed versions}
```
Tracks what has been garbage collected (for verification purposes).

## 3. Initial State

```tla
Init ==
    /\ Store: all empty
    /\ HWM: all zeros
    /\ PeerHWM: all zeros except PeerHWM[r][r] = HWM[r]
    /\ Removed: all empty
```
The system starts with:
- No data in any replica
- No operations seen (all HWMs at 0)
- Each replica's self-view in PeerHWM mirrors its actual HWM

## 4. Actions (State Transitions)

### ApplyOp - Writing Data
```tla
ApplyOp ==
    \E r \in REPLICAS, o \in REPLICAS, k \in KEYS, ts \in 1..TSMAX, del \in BOOLEAN:
        1. Add version to Store[r][k]
        2. Update HWM[r][o] if ts is higher
        3. Update PeerHWM[r][r] to reflect new HWM
```

**Example**: Replica A applies a write from replica B with timestamp 3:
- Before: `Store[A][k] = {}`, `HWM[A][B] = 0`
- After: `Store[A][k] = {[origin: B, ts: 3, isDel: FALSE]}`, `HWM[A][B] = 3`

### Gossip - Sharing HWM Information
```tla
Gossip ==
    Sender S tells Receiver R about S's HWMs:
    PeerHWM[R][S][origin] = max(current, HWM[S][origin])
```

**Example**: B gossips to A about its HWMs:
- B has `HWM[B][C] = 5`
- A updates `PeerHWM[A][B][C] = 5`
- Now A knows that B has seen operations from C up to timestamp 5

### GC - Garbage Collection
```tla
GC ==
    Remove version v from Store[r][k] if:
    v.ts <= SafeGC(r, v.origin)
    
Where SafeGC(r, o) = min({PeerHWM[r][p][o] : p \in REPLICAS})
```

**The Safety Logic**: 
- `SafeGC(r, o)` finds the minimum HWM for origin `o` across all replicas (as known by `r`)
- This is the "safe line" - all replicas have seen at least this timestamp from origin `o`

**Example**:
- `PeerHWM[A][A][B] = 5` (A has seen B's ops up to 5)
- `PeerHWM[A][C][B] = 3` (A knows C has seen B's ops up to 3)
- `SafeGC(A, B) = min(5, 3) = 3`
- A can safely GC any version from B with timestamp ≤ 3

## 5. Helper Functions

### VisibleTS - What Version is Currently Visible
```tla
VisibleTS(r, k) = max({v.ts : v in Store[r][k]})
```
Returns the highest timestamp for a key (the "visible" version in MVCC).

### AppliedTS - Tracking Applied Operations
```tla
AppliedTS(r, o) = max timestamp from origin o present in any key at replica r
```
Used to verify HWM correctness.

## 6. Safety Invariants

### HWMLowerBound
```tla
HWM[r][o] >= AppliedTS(r, o)
```
**Ensures**: HWM never goes backwards; it's always at least as high as what we've actually applied.

### NoZombie
```tla
If a non-delete is visible, no delete with higher timestamp exists
```
**Prevents**: Resurrection bugs where deleted data reappears.

**Example violation** (that this prevents):
1. Version [ts: 2, isDel: FALSE] is visible
2. Version [ts: 3, isDel: TRUE] exists
3. If we GC the delete but keep the non-delete, the key resurrects!

### SafeGCInvariant
```tla
All removed versions have timestamp <= SafeGC at removal time
```
**Ensures**: We only GC versions that all replicas have seen, preventing data loss.

## 7. The Complete Flow

1. **Write happens**: Replica creates new version with timestamp
2. **Local HWM updates**: Replica updates its HWM for that origin
3. **Gossip spreads**: Replicas exchange HWM information
4. **Safe line advances**: As gossip spreads, the safe GC line moves forward
5. **GC occurs**: Old versions below the safe line are removed
6. **Safety maintained**: All invariants ensure no data loss or resurrection

## The Key Insight

Use the **minimum** across all replicas' HWMs for safe GC. This ensures:
- No replica will ever need a version that's been GC'd
- The system remains eventually consistent
- Old versions are cleaned up without coordination/consensus

This is required for AP (Available, Partition-tolerant) systems where replicas may be temporarily disconnected but need to maintain consistency when they reconnect.
