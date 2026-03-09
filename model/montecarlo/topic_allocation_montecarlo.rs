#!/usr/bin/env rust-script
//! ```cargo
//! [dependencies]
//! rand = "0.8"
//! ```

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet, VecDeque};
use std::ops::RangeInclusive;
use std::path::PathBuf;
use std::time::{Duration, Time};

#[derive(Debug, Clone)]
struct Topic {
    hash: u32,
    evictions: u16, // Large values imply convergence issues.
    origin: Duration,
}

impl Topic {
    fn age(&self, now: Duration) -> Duration {
        now - self.origin
    }

    fn lage(&self, now: Duration) -> i8 {
        lage_from_duration(self.age(now))
    }

    /// Adjusts the local topic age estimate based on a received gossip. This implements lage propagation.
    fn merge_lage(&mut self, lage: i8, now: Duration) {
        self.origin = min(self.origin, now - lage_to_duration(lage));
    }

    fn subject_id(&self, modulus: u16) -> u16 {
        topic_subject_id(self.hash, self.evictions, modulus)
    }
}

#[derive(Debug, Clone)]
struct PeerEntry {
    remote_id: u16,
    last_seen: Duration,
}

#[derive(Debug, Clone)]
struct GossipDedupEntry {
    hash: u32,
    last_seen: Duration,
}

#[derive(Debug, Clone)]
struct GossipMessage {
    sender_id: u16,

    /// Message propagation parameters for forwarding.
    ttl: u8,
    outdegree: u8,

    /// Gossiped topic details.
    hash: u32,
    evictions: u16,
    lage: i8,
}

impl GossipMessage {
    fn dedup_hash(&self) -> u32 {
        gossip_dedup_hash(self.hash, self.evictions, self.lage)
    }
}

#[derive(Debug, Clone)]
enum CrdtMergeOutcome {
    Consensus,
    LocalWin,
    LocalLoss,
}

#[derive(Debug, Clone)]
struct Node {
    id: u16,
    topics_by_hash: BTreeMap<u32, Topic>,

    /// Peers to exchange unicast gossips with (periodic non-broadcast and urgent).
    peers: Vec<PeerEntry>,
    peer_moratorium_until: Duration,

    /// Gossips are sent at a fixed rate with dither (default period 1±0.125 s).
    /// Every nth gossip is broadcast, others are epidemic unicast; the gossip counter tracks that;
    /// as long as the peer set is not full or has at least one dead entry, every periodic gossip is broadcast.
    /// Urgent gossips have no schedule and are sent immediately when needed.
    gossip_at: Duration,
    gossip_counter: u64,
    gossip_dedup: Vec<DedupEntry>,
}

impl Node {
    fn next_update_at(&self) -> Duration {
        self.gossip_at
    }

    fn step(&mut self, now: Duration) {
        // TODO
    }
}

#[derive(Debug, Clone)]
struct SimulationConfig {
    node_count: usize,

    /// Limit simulation time.
    time_max: Duration,

    /// Use smaller values to increase allocation collisions. We use a simplified subject-ID function here;
    /// refer to proof.md for the equivalence notes between the simplified and full models.
    /// For quadrating probing, this has to be a prime; use sympy.prevprime()/nextprime().
    /// For quadrating probing, max topic count is half of this.
    subject_id_modulus: u16;

    gossip_period: Duration,
    gossip_dither: Duration,    // true interval is in [period-dither, period+dither]
    gossip_broadcast_every: u8, // every Nth gossip is broadcast instead of epidemic

    peer_count: usize,
    peer_age_reachable: Duration,      // ok to send gossips unless older than this
    peer_age_replaceable: Duration,    // replace unconditionally if older than this
    peer_replace_probability: f64,     // even if not replaceable, replace with this probability
    peer_replace_moratorium: Duration, // after replacement, no more replacements for a while to manage churn

    dedup_capacity: usize,
    dedup_timeout: Duration,

    /// This is for unicast gossips only; broadcast always have zero TTL and infinite outdegree.
    /// For unicast gossips, outdegree cannot exceed the peer count.
    periodic_ttl: u8,
    urgent_ttl: u8,
    periodic_outdegree: u8,
    urgent_outdegree: u8,

    /// Imperfect network simulation.
    network_delay_range: RangeInclusive<Duration>,
    network_loss_probability: f64,
}

/// Each time step creates a full state snapshot.
struct Snapshot {
    time: Duration,
    nodes: Vec<Node>,
}

impl Snapshot {
    fn count_collisions(&self, config: &SimulationConfig) -> usize {
        // TODO mirror the logic of FindCollisions() from Core.tla
    }

    fn count_divergences(&self, config: &SimulationConfig) -> usize {
        // TODO mirror the logic of FindDivergent() from Core.tla
    }
}

struct Simulation {
    config: SimulationConfig,
    nodes: Vec<Node>,
    now: Duration,
    snaps: Vec<Snapshot>,
    converged_at: Option<Duration>,
}

enum SimulationOutcome {
    Converged(Duration),
    TimeLimitReached,
}

impl Simulation {
    fn step(&mut self) -> Option<SimulationOutcome> {
        // Step all nodes.
        for node in &mut self.nodes {
            node.step(self.now);
        }

        // Snapshot.
        self.snaps.push(Snapshot {
            time: self.now,
            nodes: self.nodes.clone()
        });

        // Update the convergence state.
        match self.converged_at {
            Some(t) => {
                if self.count_collisions() > 0 || self.count_divergences() > 0 {
                    self.converged_at = None;
                }
            },
            None => {
                if self.count_collisions() == 0 && self.count_divergences() == 0 {
                    self.converged_at = Some(self.now);
                }
            }
        }

        // Check the simulation stop condition -- when stable state is reached.
        // Stable state is when the network stayed convergent for more than (node count times max delay).
        if let Some(t) = self.converged_at {
            let stability_window = self.config.node_count as u32 * self.config.network_delay_range.end();
            if self.now - t > stability_window {
                return SimulationOutcome::Converged(t);
            }
        }

        // Advance the time to the next event by mapping over all nodes.
        let next_time = self.nodes.iter().map(|node| node.next_update_at()).min().unwrap();
        self.now = next_time;
        if self.now >= self.config.time_max {
            return SimulationOutcome::TimeLimitReached;
        }

        None
    }
}

fn topic_subject_id(hash: u32, evictions: u16, modulus: u16) -> u16 {
    ((hash as u64 + (evictions as u64).pow(2)) % (modulus as u64)) as u16
}

fn left_wins_collision(local: &Topic, now_us: i64, remote_lage: i8, remote_hash: u64) -> bool {
    let local_lage = topic_lage(local, now_us);
    if local_lage != remote_lage {
        local_lage > remote_lage
    } else {
        local.hash < remote_hash
    }
}

/// lage is ⌊log₂(age in seconds)⌋, or -1 for age=0; range from -1 to about ~35.
fn lage_from_duration(duration: Duration) -> i8 {
    log2_floor(duration.as_secs())
}

fn lage_to_duration(lage: i8) -> Duration {
    if lage < 0 {
        Duration::ZERO
    } else if lage > 62 {
        Duration::MAX
    } else {
        Duration::from_secs(1_i64 << (lage as u32))
    }
}

/// ⌊log₂(x)⌋ for x > 0, otherwise -1
fn log2_floor(x: u64) -> i8 {
    if x == 0 {
        -1
    } else {
        (63 - x.leading_zeros()) as i8
    }
}

fn gossip_dedup_hash(hash: u32, evictions: u8, lage: i8) -> u32 {
    let other = ((evictions as u32) << 8) | (((lage + 1) as u32) << 24);
    hash ^ other
}
