use std::collections::HashMap;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::time::{Duration, Instant};

/// What’s asserted (always on in debug builds via debug_assert!):
///
/// 1.	No zombie resurrection
/// After applying any op, if the visible state is Some(value), then there must not exist a delete for
/// that key with a strictly higher stamp than the winning version.
///
/// 2.	GC safety
/// When GC removes a version v, for every replica’s HWM we currently know, HWM[replica][v.origin] >= v.ts.
/// (We also assert against our own hwm.) This proves “removed only after all peers passed it”.
///
/// 3.	HWM monotonicity
///     • A replica’s local hwm[origin] never decreases.
///     • Gossiped HWMs from a peer never decrease per origin (if they do, it’s a protocol bug).
///
/// 4.	Winner correctness
///
/// The “visible” value is always produced by the max (ts, origin) version in the MVCC list.

#[derive(Clone)]
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self { Self(seed | 1) }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0
    }
    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        lo + (self.next() % (hi - lo))
    }
    fn coin(&mut self, p_num: u64, p_den: u64) -> bool {
        (self.next() % p_den) < p_num
    }
}

/// Value in MVCC store. None == ⊥ (delete version)
#[derive(Clone, Debug)]
struct Version {
    origin: usize,           // origin replica id
    ts: u64,                 // commit_ts (per-origin monotone)
    value: Option<String>,   // None => delete (⊥)
}

/// Messages flowing in the simulated system
#[derive(Clone, Debug)]
enum Msg {
    Op { key: String, ver: Version },          // mutation
    Gossip { from: usize, hwm: Vec<u64> },     // HWM frontier
    Shutdown,
}

#[derive(Clone, Debug)]
enum ToRouter {
    Gossip { from: usize, hwm: Vec<u64> },
}

/// Replica (node) thread

struct Replica {
    id: usize,
    n: usize,
    inbox: Receiver<Msg>,
    to_router: Sender<ToRouter>,
    table: HashMap<String, Vec<Version>>,        // MVCC: key -> versions
    hwm: Vec<u64>,                                // my applied HWM per origin
    peer_hwms: HashMap<usize, Vec<u64>>,          // last seen HWM per peer
    visible_cache: HashMap<String, Option<String>>,
    last_gossip: Instant,
}

impl Replica {
    fn new(id: usize, n: usize, inbox: Receiver<Msg>, to_router: Sender<ToRouter>) -> Self {
        // Initialize peer_hwms for ALL replicas to zeros (conservative for GC).
        let mut peer_hwms = HashMap::new();
        for rid in 0..n {
            peer_hwms.insert(rid, vec![0; n]);
        }
        let mut r = Self {
            id, n, inbox, to_router,
            table: HashMap::new(),
            hwm: vec![0; n],
            peer_hwms,
            visible_cache: HashMap::new(),
            last_gossip: Instant::now(),
        };
        r.peer_hwms.insert(id, r.hwm.clone()); // keep self mirrored
        r
    }

    fn apply_op(&mut self, key: String, ver: Version) {
        // Assert local HWM monotonic for this origin
        let old_hwm = self.hwm[ver.origin];

        // Append MVCC version
        let e = self.table.entry(key.clone()).or_default();
        e.push(ver.clone());

        // Advance local HWM for that origin
        if ver.ts > self.hwm[ver.origin] {
            self.hwm[ver.origin] = ver.ts;
        }
        debug_assert!(
            self.hwm[ver.origin] >= old_hwm,
            "HWM decreased for origin {} on R{}: {} -> {}",
            ver.origin, self.id, old_hwm, self.hwm[ver.origin]
        );

        // Keep self HWM reflected in peer_hwms for min() computation
        self.peer_hwms.insert(self.id, self.hwm.clone());

        // Winner & visible computation
        let vis_before = self.visible_cache.get(&key).cloned().unwrap_or(None);
        let (winner_origin, winner_ts, vis_after) = self.compute_winner_and_visible(&key);

        // Invariant #4: visible comes from the max (ts,origin) version
        if let Some(vers) = self.table.get(&key) {
            let true_max = vers.iter().max_by_key(|v| (v.ts, v.origin)).map(|v| (v.origin, v.ts));
            debug_assert_eq!(
                true_max,
                Some((winner_origin, winner_ts)),
                "Winner mismatch on R{} key {}",
                self.id, key
            );
        }

        // Invariant #1: no zombie resurrection: if visible is Some(..),
        // there must not exist a delete with ts > winner_ts.
        if let Some(vers) = self.table.get(&key) {
            if vis_after.is_some() {
                let max_delete = vers.iter()
                    .filter(|v| v.value.is_none())
                    .map(|v| v.ts)
                    .max()
                    .unwrap_or(0);
                debug_assert!(
                    winner_ts >= max_delete,
                    "Zombie resurrection on R{} key {}: visible from ts={}, but max delete ts={}",
                    self.id, key, winner_ts, max_delete
                );
            }
        }

        if vis_after != vis_before {
            println!(
                "[R{}] VISIBLE {} -> {} @ ({},{})",
                self.id,
                vis_before.as_deref().unwrap_or("∅"),
                vis_after.as_deref().unwrap_or("∅"),
                winner_origin, winner_ts
            );
            self.visible_cache.insert(key, vis_after);
        }
    }

    fn compute_winner_and_visible(&self, key: &str) -> (usize, u64, Option<String>) {
        if let Some(vers) = self.table.get(key) {
            if let Some(best) = vers.iter().max_by_key(|v| (v.ts, v.origin)) {
                return (best.origin, best.ts, best.value.clone());
            }
        }
        (usize::MAX, 0, None)
    }

    fn safe_gc_vector(&self) -> Vec<u64> {
        let mut safe = vec![u64::MAX; self.n];
        for origin in 0..self.n {
            let mut m = self.hwm[origin];
            for rid in 0..self.n {
                if let Some(vv) = self.peer_hwms.get(&rid) {
                    m = m.min(vv[origin]);
                } else {
                    m = 0; // missing peer info → conservative
                }
            }
            safe[origin] = m;
        }
        safe
    }

    fn gc(&mut self) {
        let safe = self.safe_gc_vector();
        let mut removed_total = 0usize;

        // Invariant #2 checked on each removal: removed only if <= safe[origin] for ALL peers
        self.table.retain(|_k, vers| {
            let before = vers.len();
            vers.retain(|v| {
                let keep = v.ts > safe[v.origin];
                if !keep {
                    // Check GC safety against ALL known HWMs, including self
                    for rid in 0..self.n {
                        let vv = if rid == self.id {
                            &self.hwm
                        } else {
                            self.peer_hwms.get(&rid).expect("peer_hwms pre-initialized")
                        };
                        debug_assert!(
                            vv[v.origin] >= v.ts,
                            "Unsafe GC on R{}: removing {:?} but peer R{} has HWM[{}]={} < v.ts={}",
                            self.id, v, rid, v.origin, vv[v.origin], v.ts
                        );
                    }
                }
                keep
            });
            removed_total += before - vers.len();
            true
        });

        if removed_total > 0 {
            println!("[R{}] GC removed {} versions; safe_gc={:?}", self.id, removed_total, safe);
        }
    }

    fn maybe_gossip(&mut self, period_ms: u64) {
        if self.last_gossip.elapsed() >= Duration::from_millis(period_ms) {
            let _ = self.to_router.send(ToRouter::Gossip { from: self.id, hwm: self.hwm.clone() });
            self.last_gossip = Instant::now();
        }
    }

    fn on_gossip(&mut self, from: usize, hwm: Vec<u64>) {
        // Invariant #3: peer HWM monotone non-decreasing per origin
        if let Some(prev) = self.peer_hwms.get(&from) {
            debug_assert_eq!(prev.len(), hwm.len(), "HWM vector length mismatch");
            for (i, (&old, &newv)) in prev.iter().zip(hwm.iter()).enumerate() {
                debug_assert!(
                    newv >= old,
                    "Peer HWM decreased for origin {} from R{}: {} -> {}",
                    i, from, old, newv
                );
            }
        }
        self.peer_hwms.insert(from, hwm);
        self.peer_hwms.insert(self.id, self.hwm.clone()); // keep self mirrored
        self.gc(); // try GC after improved frontier
    }

    fn run(mut self, gossip_period_ms: u64) {
        loop {
            match self.inbox.recv_timeout(Duration::from_millis(20)) {
                Ok(Msg::Op { key, ver }) => self.apply_op(key, ver),
                Ok(Msg::Gossip { from, hwm }) => self.on_gossip(from, hwm),
                Ok(Msg::Shutdown) => break,
                Err(_timeout) => { /* tick */ }
            }
            self.maybe_gossip(gossip_period_ms);
        }
        self.gc();
        println!("[R{}] stopped.", self.id);
    }
}

/// Router thread (broadcast)

fn router_thread(
    from_gen_rx: Receiver<Msg>,
    from_replicas_rx: Receiver<ToRouter>,
    replica_txs: Vec<Sender<Msg>>,
) {
    loop {
        if let Ok(msg) = from_gen_rx.recv_timeout(Duration::from_millis(10)) {
            match msg.clone() {
                Msg::Shutdown => {
                    for tx in &replica_txs { let _ = tx.send(Msg::Shutdown); }
                    break;
                }
                _ => {
                    for tx in &replica_txs { let _ = tx.send(msg.clone()); }
                }
            }
        }
        while let Ok(cmd) = from_replicas_rx.try_recv() {
            match cmd {
                ToRouter::Gossip { from, hwm } => {
                    for (rid, tx) in replica_txs.iter().enumerate() {
                        if rid == from { continue; }
                        let _ = tx.send(Msg::Gossip { from, hwm: hwm.clone() });
                    }
                }
            }
        }
    }
    println!("[Router] stopped.");
}

/// Generator thread (workload)

fn generator_thread(
    n: usize,
    keys: Vec<String>,
    duration_secs: u64,
    send_to_router: Sender<Msg>,
) {
    let start = Instant::now();
    let mut rng = Lcg::new(0xC0FFEE);
    let mut counters = vec![1u64; n]; // per-origin monotone commit_ts

    while start.elapsed() < Duration::from_secs(duration_secs) {
        let origin = rng.gen_range(0, n as u64) as usize;
        let key = keys[(rng.gen_range(0, keys.len() as u64)) as usize].clone();
        let is_delete = rng.coin(3, 10); // 30% deletes

        let ts = counters[origin];
        counters[origin] += 1;

        let ver = Version {
            origin,
            ts,
            value: if is_delete { None } else { Some(format!("v{}_{}", origin, ts)) },
        };

        let _ = send_to_router.send(Msg::Op { key, ver });
        thread::sleep(Duration::from_millis(30));
    }

    let _ = send_to_router.send(Msg::Shutdown);
    println!("[Gen] stopped.");
}

fn main() {
    // Config
    let n_replicas = 4usize;
    let gossip_period_ms: u64 = 200;
    let sim_secs: u64 = 6;
    let keys: Vec<String> = (0..8).map(|i| format!("k{}", i)).collect();

    // Channels
    let (gen_tx, gen_rx) = mpsc::channel::<Msg>();
    let (rep_to_router_tx, rep_to_router_rx) = mpsc::channel::<ToRouter>();

    // Per-replica inboxes
    let mut replica_inboxes = Vec::with_capacity(n_replicas);
    let mut replica_txs = Vec::with_capacity(n_replicas);
    for _ in 0..n_replicas {
        let (tx, rx) = mpsc::channel::<Msg>();
        replica_txs.push(tx);
        replica_inboxes.push(rx);
    }

    // Router
    let router_handle = {
        let replica_txs_clone = replica_txs.clone();
        thread::spawn(move || router_thread(gen_rx, rep_to_router_rx, replica_txs_clone))
    };

    // Replicas
    let mut repl_handles = Vec::new();
    for rid in 0..n_replicas {
        let inbox = replica_inboxes.remove(0);
        let to_router = rep_to_router_tx.clone();
        let h = thread::spawn(move || {
            let r = Replica::new(rid, n_replicas, inbox, to_router);
            r.run(gossip_period_ms);
        });
        repl_handles.push(h);
    }

    // Generator
    let gen_handle = {
        let tx = gen_tx.clone();
        thread::spawn(move || generator_thread(n_replicas, keys, sim_secs, tx))
    };

    // Join
    let _ = gen_handle.join();
    let _ = router_handle.join();
    for h in repl_handles { let _ = h.join(); }
    println!("Simulation complete.");
}

