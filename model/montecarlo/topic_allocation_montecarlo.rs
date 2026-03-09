#!/usr/bin/env rust-script
//! ```cargo
//! [dependencies]
//! rand = "0.8"
//! clap = { version = "4.0", features = ["derive"] }
//! ```

use clap::Parser;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::BTreeMap;
use std::ops::RangeInclusive;
use std::time::Duration;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
struct Config {
    /// Topics are generated with random hash values, then randomly assigned to nodes.
    /// Each topic is used by any number of nodes ranging from 1 to node_count inclusive, chosen randomly.
    /// The subject-ID modulus defines the subject-ID collision rate.
    #[arg(long, default_value = "10")]
    node_count: usize,

    #[arg(long, default_value = "20")]
    topic_count: usize,

    /// Use smaller values to increase allocation collisions. We use a simplified subject-ID function here;
    /// refer to proof.md for the equivalence notes between the simplified and full models.
    /// For quadrating probing, this has to be a prime; use sympy.prevprime()/nextprime().
    /// For quadrating probing, max topic count is half of this.
    #[arg(long, default_value = "1999")]
    subject_id_modulus: u16,

    /// Limit simulation time. Expect convergence before this.
    #[arg(long, value_parser = parse_duration, default_value = "60")]
    time_limit: Duration,

    /// ---------------------------------------------------------------------------------------------------------------
    /// Gossip parameters.
    /// Broadcast always have zero TTL and infinite outdegree (by definition).
    /// For unicast gossips, outdegree cannot exceed the peer count.
    /// Every gossip_broadcast_every-th gossip is broadcast instead of epidemic.
    /// Chosen gossip interval is in [period-dither, period+dither].
    #[arg(long, value_parser = parse_duration, default_value = "1")]
    gossip_period: Duration,

    #[arg(long, value_parser = parse_duration, default_value = "0.125")]
    gossip_dither: Duration,

    #[arg(long, default_value = "10")]
    gossip_broadcast_every: u8,

    #[arg(long, default_value = "1")]
    gossip_ttl_periodic: u8,

    #[arg(long, default_value = "10")]
    gossip_ttl_urgent: u8,

    #[arg(long, default_value = "1")]
    gossip_outdegree_periodic: u8,

    #[arg(long, default_value = "2")]
    gossip_outdegree_urgent: u8,

    /// ---------------------------------------------------------------------------------------------------------------
    /// Epidemic peer sampler parameters.
    #[arg(long, default_value = "8")]
    peer_count: usize,

    #[arg(long, value_parser = parse_duration, default_value = "30")]
    peer_age_reachable: Duration, // ok to send gossips unless older than this

    #[arg(long, value_parser = parse_duration, default_value = "15")]
    peer_age_replaceable: Duration, // replace unconditionally if older than this

    #[arg(long, default_value = "0.125")]
    peer_replacement_probability: f64, // even if not replaceable, replace with this probability

    #[arg(long, value_parser = parse_duration_range, default_value = "0..1")]
    peer_moratorium_range: RangeInclusive<Duration>, // after replacement, hold for random time from this range

    /// ---------------------------------------------------------------------------------------------------------------
    /// Epidemic duplicate gossip drop cache. Necessary for network load regulation; see the model.
    #[arg(long, default_value = "16")]
    dedup_capacity: usize,

    #[arg(long, value_parser = parse_duration, default_value = "1")]
    dedup_timeout: Duration,

    /// ---------------------------------------------------------------------------------------------------------------
    /// Imperfect network simulation.
    #[arg(long, value_parser = parse_duration_range, default_value = "0..0.1")]
    network_delay_range: RangeInclusive<Duration>,

    #[arg(long, default_value = "0.0001")]
    network_loss_probability: f64,
}

#[derive(Debug, Clone)]
struct Topic {
    hash: u64,
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
    hash: u64,
    last_seen: Duration,
}

#[derive(Debug, Clone)]
struct GossipMessage {
    sender_id: u16,

    /// Message propagation parameters for forwarding.
    ttl: u8,
    outdegree: u8,

    /// Gossiped topic details.
    hash: u64,
    evictions: u16,
    lage: i8,
}

impl GossipMessage {
    fn dedup_hash(&self) -> u64 {
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
    topics_by_hash: BTreeMap<u64, Topic>,

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

    fn add_topic(&mut self, topic_hash: u64) {
        // TODO insert topic using local collision arbitration (like topic_allocate() in cy.c)
    }

    fn step(&mut self, now: Duration) {
        // TODO
    }
}

/// Each time step creates a full state snapshot.
struct Snapshot {
    time: Duration,
    nodes: Vec<Node>,
}

impl Snapshot {
    fn count_collisions(&self, subject_id_modulus: u16) -> usize {
        // TODO mirror the logic of FindCollisions() from Core.tla
    }

    fn count_divergent(&self, subject_id_modulus: u16) -> usize {
        // TODO mirror the logic of FindDivergent() from Core.tla
    }
}

struct Simulation {
    config: Config,
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
            nodes: self.nodes.clone(),
        });

        // Update the convergence state.
        match self.converged_at {
            Some(t) => {
                if self.count_collisions() > 0 || self.count_divergences() > 0 {
                    self.converged_at = None;
                }
            }
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
        if self.now >= self.config.time_limit {
            return SimulationOutcome::TimeLimitReached;
        }

        None
    }

    fn run(&mut self) -> SimulationOutcome {
        loop {
            if let Some(outcome) = self.step() {
                return outcome;
            }
        }
    }
}

fn topic_subject_id(hash: u64, evictions: u16, modulus: u16) -> u16 {
    ((hash + (evictions as u64).pow(2)) % (modulus as u64)) as u16
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
    if x <= 0 {
        -1
    } else {
        (63 - (x as u64).leading_zeros()) as i8
    }
}

fn gossip_dedup_hash(hash: u64, evictions: u8, lage: i8) -> u64 {
    let other = ((evictions as u64) << 16) | (((lage + 1) as u64) << 56);
    hash ^ other
}

fn parse_duration_range(s: &str) -> Result<RangeInclusive<Duration>, String> {
    let (start, end) = s.split_once("..").ok_or_else(|| "expected MIN..MAX".to_string())?;
    let start = parse_duration(start)?;
    let end = parse_duration(end)?;
    if start > end {
        return Err("range start must be <= range end".to_string());
    }
    Ok(start..=end)
}

/// The duration is given as a real number of seconds.
fn parse_duration(s: &str) -> Result<Duration, String> {
    let seconds = s.parse::<f64>().map_err(|e| e.to_string())?;
    Ok(Duration::from_secs_f64(seconds))
}
