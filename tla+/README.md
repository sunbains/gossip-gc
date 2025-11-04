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
