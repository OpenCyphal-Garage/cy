//! Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#![allow(dead_code, unused_variables, unused_mut)]

use clap::{error::ErrorKind, CommandFactory, Parser};
use rand::rngs::SmallRng;
use rand::SeedableRng;
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// All durations are specified in seconds unless explicitly noted otherwise.
#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
struct Config {
    #[arg(long, default_value = "10")]
    node_count: usize,

    /// Topics are generated with random hash values, then randomly assigned to nodes.
    /// The subject-ID modulus defines the subject-ID collision rate.
    #[arg(long, default_value = "20")]
    topic_count: usize,

    /// Use smaller values to increase allocation collisions. We use a simplified subject-ID function here;
    /// refer to proof.md for the equivalence notes between the simplified and full models.
    /// For quadratic probing, max topic count is half of this number, and it has to be a prime;
    /// use sympy.prevprime()/nextprime().
    #[arg(long, default_value = "1999")]
    subject_id_modulus: u16,

    /// Optional seed for reproducible random initialization. If omitted, current time is used.
    #[arg(long)]
    seed: Option<u64>,

    /// Limit simulation time. Expect convergence before this.
    #[arg(long, value_parser = parse_duration, default_value = "60")]
    time_limit: Duration,

    // ----------------------------------------------------------------------------------------------------------------
    /// Gossip parameters.
    /// Broadcast always have zero TTL and infinite outdegree (by definition).
    /// Chosen gossip interval is in [period-dither, period+dither].
    #[arg(long, value_parser = parse_duration, default_value = "1")]
    gossip_period: Duration,

    #[arg(long, value_parser = parse_duration, default_value = "0.125")]
    gossip_dither: Duration,

    /// Every nth gossip is broadcast instead of epidemic.
    #[arg(long, default_value = "10")]
    gossip_broadcast_every: u8,

    #[arg(long, default_value = "1")]
    gossip_ttl_periodic: u8,

    #[arg(long, default_value = "10")]
    gossip_ttl_urgent: u8,

    /// For unicast gossips, outdegree cannot exceed the peer count.
    #[arg(long, default_value = "1")]
    gossip_outdegree_periodic: u8,

    #[arg(long, default_value = "2")]
    gossip_outdegree_urgent: u8,

    // ----------------------------------------------------------------------------------------------------------------
    /// Epidemic peer sample set size.
    #[arg(long, default_value = "8")]
    peer_count: usize,

    /// A peer is eligible to receive gossips unless it was last seen longer than this ago.
    #[arg(long, value_parser = parse_duration, default_value = "30")]
    peer_age_reachable: Duration,

    /// A peer will be replaced unconditionally at next opportunity (bypassing probabilistic sampling)
    /// if it was last seen longer than this ago.
    #[arg(long, value_parser = parse_duration, default_value = "15")]
    peer_age_replaceable: Duration,

    /// Peers that are still reachable (which are all peers during normal operation) will be replaced anyway
    /// with this probability at each gossip outside of the moratorium period to ensure mixing.
    #[arg(long, default_value = "0.125")]
    peer_replacement_probability: f64,

    /// After a peer replacement, there is a moratorium period during which the new peer cannot be replaced again to
    /// make the peer churn rate less dependent on the network size, ensuring more consistent parameters across
    /// networks of various sizes.
    #[arg(long, value_parser = parse_duration_range, default_value = "0..1")]
    peer_moratorium_range: RangeInclusive<Duration>,

    // ----------------------------------------------------------------------------------------------------------------
    /// Epidemic duplicate gossip drop cache is necessary for network load regulation; see the model.
    #[arg(long, default_value = "16")]
    dedup_capacity: usize,

    /// Gossips that have been seen more than this long ago are considered fresh.
    #[arg(long, value_parser = parse_duration, default_value = "1")]
    dedup_timeout: Duration,

    // ----------------------------------------------------------------------------------------------------------------
    /// Imperfect network simulation. Packets take a random time in this range to be delivered.
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
    gossip_dedup: Vec<GossipDedupEntry>,
}

impl Node {
    /// Creates an empty node with no topics.
    fn new(id: u16) -> Self {
        Self {
            id,
            topics_by_hash: BTreeMap::new(),
            peers: Vec::new(),
            peer_moratorium_until: Duration::ZERO,
            gossip_at: Duration::ZERO,
            gossip_counter: 0,
            gossip_dedup: Vec::new(),
        }
    }

    fn add_topic(&mut self, topic_hash: u64, subject_id_modulus: u16) {
        let mut moving = self.topics_by_hash.remove(&topic_hash).unwrap_or(Topic {
            hash: topic_hash,
            evictions: 0,
            origin: Duration::ZERO,
        });
        loop {
            let subject_id = moving.subject_id(subject_id_modulus);
            let collided_hash = self.topics_by_hash.iter().find_map(|(hash, topic)| {
                if topic.subject_id(subject_id_modulus) == subject_id {
                    Some(*hash)
                } else {
                    None
                }
            });
            match collided_hash {
                Some(hash) => {
                    let displaced =
                        self.topics_by_hash.remove(&hash).expect("collision peer disappeared during local allocation");
                    if left_wins_collision(&moving, Duration::ZERO, displaced.lage(Duration::ZERO), displaced.hash) {
                        self.topics_by_hash.insert(moving.hash, moving);
                        moving = Topic {
                            evictions: displaced.evictions.checked_add(1).expect("eviction counter too large"),
                            ..displaced
                        };
                    } else {
                        moving.evictions = moving.evictions.checked_add(1).expect("eviction counter too large");
                        self.topics_by_hash.insert(displaced.hash, displaced);
                    }
                }
                None => {
                    self.topics_by_hash.insert(moving.hash, moving);
                    break;
                }
            }
        }
        assert_eq!(0, self.count_local_collisions(subject_id_modulus), "local allocation incorrect");
    }

    fn count_local_collisions(&self, subject_id_modulus: u16) -> usize {
        count_colliding_subjects(self.topics_by_hash.values(), subject_id_modulus)
    }

    fn next_update_at(&self) -> Duration {
        self.gossip_at
    }

    fn step(&mut self, _now: Duration) {
        todo!("simulation step is not implemented yet")
    }
}

#[derive(Debug, Clone)]
struct Snapshot {
    time: Duration,
    nodes: Vec<Node>,
}

impl Snapshot {
    fn count_collisions(&self, subject_id_modulus: u16) -> usize {
        count_colliding_subjects(self.nodes.iter().flat_map(|node| node.topics_by_hash.values()), subject_id_modulus)
    }

    fn count_divergent(&self) -> usize {
        let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
        for topic in self.nodes.iter().flat_map(|node| node.topics_by_hash.values()) {
            by_hash.entry(topic.hash).or_default().insert(topic.evictions);
        }
        by_hash.values().filter(|evictions| evictions.len() > 1).count()
    }
}

struct Simulation {
    config: Config,
    nodes: Vec<Node>,
    now: Duration,
    snaps: Vec<Snapshot>,
    converged_at: Option<Duration>,
    rng: SmallRng,
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
        self.snaps.push(Snapshot { time: self.now, nodes: self.nodes.clone() });

        // Update the convergence state.
        let collisions = self.snaps.last().unwrap().count_collisions(self.config.subject_id_modulus);
        let divergences = self.snaps.last().unwrap().count_divergent();
        match self.converged_at {
            Some(_) => {
                if collisions > 0 || divergences > 0 {
                    self.converged_at = None;
                }
            }
            None => {
                if collisions == 0 && divergences == 0 {
                    self.converged_at = Some(self.now);
                }
            }
        }

        // Check the simulation stop condition -- when stable state is reached.
        // Stable state is when the network stayed convergent for more than (node count times max delay).
        if let Some(t) = self.converged_at {
            let stability_window =
                Duration::from_secs_f64(self.nodes.len() as f64 * self.config.network_delay_range.end().as_secs_f64());
            if self.now - t > stability_window {
                return Some(SimulationOutcome::Converged(t));
            }
        }

        // Advance the time to the next event by mapping over all nodes.
        let next_time = self.nodes.iter().map(|node| node.next_update_at()).min().unwrap();
        self.now = next_time;
        if self.now >= self.config.time_limit {
            return Some(SimulationOutcome::TimeLimitReached);
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

fn main() -> ExitCode {
    // Set up the configuration.
    let mut config = Config::parse();
    if !is_prime_u16(config.subject_id_modulus) {
        Config::command().error(ErrorKind::ValueValidation, "subject-ID modulus must be prime").exit();
    }
    if config.topic_count >= (config.subject_id_modulus as usize) / 2 {
        Config::command().error(ErrorKind::ValueValidation, "too many topics for this modulus").exit();
    }
    if let None = config.seed {
        config.seed = Some(generate_seed());
        eprintln!("Using automatic --seed={0}", config.seed.unwrap());
    }

    // Set up the simulation.
    let mut sim = Simulation {
        config: config.clone(),
        nodes: (0..config.node_count as u16).map(Node::new).collect(),
        now: Duration::ZERO,
        snaps: Vec::new(),
        converged_at: None,
        rng: SmallRng::seed_from_u64(config.seed.unwrap()),
    };
    drop(config);

    ExitCode::SUCCESS
}

fn count_colliding_subjects<'a, I>(topics: I, subject_id_modulus: u16) -> usize
where
    I: IntoIterator<Item = &'a Topic>,
{
    let mut by_subject: BTreeMap<u16, BTreeSet<u64>> = BTreeMap::new();
    for topic in topics {
        by_subject.entry(topic.subject_id(subject_id_modulus)).or_default().insert(topic.hash);
    }
    by_subject.values().filter(|hashes| hashes.len() > 1).count()
}

fn topic_subject_id(hash: u64, evictions: u16, modulus: u16) -> u16 {
    ((hash + (evictions as u64).pow(2)) % (modulus as u64)) as u16
}

fn left_wins_collision(local: &Topic, now: Duration, remote_lage: i8, remote_hash: u64) -> bool {
    let local_lage = local.lage(now);
    if local_lage != remote_lage {
        local_lage > remote_lage
    } else {
        local.hash < remote_hash
    }
}

fn generate_seed() -> u64 {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or(Duration::ZERO);
    now.as_secs() ^ ((now.subsec_nanos() as u64) << 32)
}

fn is_prime_u16(value: u16) -> bool {
    if value < 2 {
        return false;
    }
    if value == 2 {
        return true;
    }
    if value % 2 == 0 {
        return false;
    }
    let mut divisor = 3_u32;
    let value = u32::from(value);
    while divisor * divisor <= value {
        if value % divisor == 0 {
            return false;
        }
        divisor += 2;
    }
    true
}

/// lage is ⌊log₂(age in seconds)⌋, or -1 for age=0; range from -1 to about ~35.
fn lage_from_duration(duration: Duration) -> i8 {
    match duration.as_secs() {
        0 => -1,
        s => s.ilog2() as i8,
    }
}

fn lage_to_duration(lage: i8) -> Duration {
    match lage {
        ..0 => Duration::ZERO,
        63.. => Duration::MAX,
        v => Duration::from_secs(1_u64 << (v as u32)),
    }
}

fn gossip_dedup_hash(hash: u64, evictions: u16, lage: i8) -> u64 {
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
    if !seconds.is_finite() || seconds < 0.0 {
        return Err("duration must be finite and non-negative".to_string());
    }
    Ok(Duration::from_secs_f64(seconds))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lage_conversion_matches_model_examples() {
        assert_eq!(-1, lage_from_duration(Duration::ZERO));
        assert_eq!(0, lage_from_duration(Duration::from_secs(1)));
        assert_eq!(1, lage_from_duration(Duration::from_secs(2)));
        assert_eq!(1, lage_from_duration(Duration::from_secs(3)));
        assert_eq!(Duration::ZERO, lage_to_duration(-1));
        assert_eq!(Duration::from_secs(1), lage_to_duration(0));
        assert_eq!(Duration::from_secs(2), lage_to_duration(1));
        assert_eq!(Duration::from_secs(8), lage_to_duration(3));
    }

    #[test]
    fn topic_subject_id_uses_quadratic_probing() {
        assert_eq!(4, topic_subject_id(3, 1, 11));
        assert_eq!(4, topic_subject_id(4, 0, 11));
        assert_eq!(5, topic_subject_id(12, 2, 11));
    }

    #[test]
    fn parse_duration_accepts_fractional_seconds() {
        assert_eq!(Duration::from_millis(125), parse_duration("0.125").unwrap());
        assert!(parse_duration("-1").is_err());
        assert!(parse_duration("nan").is_err());
    }

    #[test]
    fn parse_duration_range_requires_ordered_bounds() {
        let range = parse_duration_range("0.25..1.5").unwrap();
        assert_eq!(Duration::from_millis(250), *range.start());
        assert_eq!(Duration::from_millis(1500), *range.end());
        assert!(parse_duration_range("2..1").is_err());
    }

    #[test]
    fn add_topic_resolves_local_collision_cascade() {
        let mut node = Node::new(0);
        node.add_topic(2, 11);
        node.add_topic(12, 11);
        node.add_topic(1, 11);

        let subjects = node
            .topics_by_hash
            .values()
            .map(|topic| (topic.hash, topic.subject_id(11), topic.evictions))
            .collect::<Vec<_>>();
        assert_eq!(0, node.count_local_collisions(11));
        assert!(subjects.contains(&(1, 1, 0)));
        assert!(subjects.contains(&(2, 2, 0)));
        assert!(subjects.contains(&(12, 5, 2)));
    }
}
