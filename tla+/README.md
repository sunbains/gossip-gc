# MVCC + HWM + Gossip-based Safe GC (TLA+ Spec)

This package contains a small TLA+ specification that models **AP replication with MVCC delete versions**, **per-replica High-Water-Marks (HWM)**, **gossip of HWMs**, and **safe garbage collection** of historical versions (including deletes) using the **min across peer HWMs**.

It checks the key safety properties you care about:

- **NoZombie**: a stale non-delete value can never reappear if a later delete exists
- **SafeGC**: a version is only GC'd after *every* peer has advanced past it (according to the replica's known HWM gossip)
- **SelfMirror**: each replica treats its own HWM as part of the min frontier used for GC
- **HWMLowerBound**: each HWM is at least the maximum applied timestamp for that origin

> This is a finite, intentionally small model for TLC exploration—not a full protocol proof.

---

## Files

- `MVCCGossip.tla` — the specification
- `MVCCGossip.cfg` — TLC configuration (small model)
- `README.md` — this guide

---

## How the model works (high level)

- **Versions** are records: `[origin \in REPLICAS, ts \in 1..TSMAX, isDel \in BOOLEAN]`.
  - `isDel = TRUE` encodes the delete (⊥) version.

- Each replica `r` maintains:
  - `Store[r][k]`: a *set* of versions present locally for key `k`.
  - `HWM[r][o]`: the highest timestamp from origin `o` that `r` has applied.
  - `PeerHWM[r][p][o]`: the last gossiped HWM from peer `p` about origin `o` (with `PeerHWM[r][r] = HWM[r]`).
  - `Removed[r]`: a *ghost* set of versions that `r` has GC'd (for post-checking safety).

- **Gossip** copies HWMs pointwise-max from a sender to a receiver.
- **GC** may remove a version `v` at replica `r` if `v.ts <= Min_p PeerHWM[r][p][v.origin]`.
- **Visible** value for `(r,k)` is the version in `Store[r][k]` with the **max `ts`** (ties are irrelevant for this safety model).

The model non-deterministically:
1. Applies a version to some replica (`ApplyOp`).
2. Gossips HWMs between replicas (`Gossip`).
3. GC's eligible versions (`GC`).

---

## Running TLC

### Option A: VS Code + TLA+ extension
1. Install the "TLA+ (TLC/TLA+ Tools)" extension.
2. Open this folder.
3. Open `MVCCGossip.tla` and click "Run TLC".

### Option B: tla2tools.jar (CLI)
1. Download **tla2tools.jar** from the TLA⁺ site.
2. From this directory, run:

```bash
java -cp tla2tools.jar tlc2.TLC -config MVCCGossip.cfg MVCCGossip.tla
```

You should see TLC explore the state space and report that all listed **INVARIANTS** hold for the small model:
- `REPLICAS = {A, B}`
- `KEYS = {k}`
- `TSMAX = 3`

> Increase these constants to explore larger spaces (note the exponential blow-up).

---

## What to look for

- TLC checks:
  - **TypeInv**: well-typedness of all variables
  - **HWMLowerBound**: `HWM[r][o] >= max applied ts for o at r`
  - **SelfMirror**: `PeerHWM[r][r] = HWM[r]`
  - **NoZombie**: if the visible value is non-delete, there is no higher-timestamp delete present
  - **SafeGCInvariant**: any version in `Removed[r]` satisfies the GC condition: `ts <= min PeerHWM[r][*][origin]`

If you intentionally break the model (see below), TLC will produce a counterexample trace.

---

## How to see failures (mutate intentionally)

1. **Unsafe GC**  
   Change the `GC` guard to `v.ts < SafeGC(r, v.origin)` or remove the `PeerHWM[r][r] = HWM[r]` mirror.  
   TLC should violate `SafeGCInvariant`.

2. **Zombie resurrection**  
   Change `NoZombie` to include `>=` or change `VisibleTS` to min instead of max.  
   TLC should violate `NoZombie` quickly.

3. **Non-monotone HWM**  
   Modify `Gossip` to assign `PeerHWM[r][s] := HWM[s]` directly (without max).  
   While not an invariant itself, it undermines GC safety—add an invariant to check monotonicity if you want.

---

## Extending the model

- Add **range deletes** by recording versions with a `rangeId` instead of `key` and making visibility a predicate over ranges.
- Introduce **network partitions** explicitly and constrain `Gossip` to obey a partition graph.
- Model **per-shard GC** by indexing `Store`, `HWM`, `PeerHWM`, and `Removed` by a `SHARDS` constant.

---

## Mapping to the implementation

- `ts` corresponds to TiDB/TiKV `commit_ts` (monotone per origin).
- `HWM` is akin to `resolved-ts/apply-ts` per origin at a replica.
- `PeerHWM` mirrors the gossiped frontier a replica uses to compute **safe GC**.
- `SafeGC` is the computed **checkpoint/safe-ts** for purging history.

This spec demonstrates the core safety: **no zombies** and **GC only after everyone is past the version**, without Cassandra-style TTL guessing or a central coordinator.
