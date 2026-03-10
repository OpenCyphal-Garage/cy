//! Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#![allow(dead_code, unused_variables, unused_mut)]

pub mod message;
pub mod network;
pub mod node;
pub mod simulation;
pub mod topic;

use network::NetworkConfig;
use node::NodeConfig;
use simulation::{Simulation, SimulationConfig, SimulationOutcome};

use clap::{CommandFactory, Parser, error::ErrorKind};
use duration_str::parse_time;
use rand::SeedableRng;
use rand::rngs::SmallRng;
use std::cell::RefCell;
use std::ops::RangeInclusive;
use std::process::ExitCode;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};
use time::Duration;

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
    #[arg(long, default_value_t = NodeConfig::default().subject_id_modulus)]
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
    #[arg(long, value_parser = parse_duration, default_value_t = NodeConfig::default().gossip_period)]
    gossip_period: Duration,

    #[arg(long, value_parser = parse_duration, default_value_t = NodeConfig::default().gossip_dither)]
    gossip_dither: Duration,

    /// Every nth gossip is broadcast instead of epidemic.
    #[arg(long, default_value_t = NodeConfig::default().gossip_broadcast_every)]
    gossip_broadcast_every: u8,

    #[arg(long, default_value_t = NodeConfig::default().gossip_ttl_periodic)]
    gossip_ttl_periodic: u8,

    #[arg(long, default_value_t = NodeConfig::default().gossip_ttl_urgent)]
    gossip_ttl_urgent: u8,

    /// For unicast gossips, outdegree cannot exceed the peer count.
    #[arg(long, default_value_t = NodeConfig::default().gossip_outdegree_periodic)]
    gossip_outdegree_periodic: u8,

    #[arg(long, default_value_t = NodeConfig::default().gossip_outdegree_urgent)]
    gossip_outdegree_urgent: u8,

    // ----------------------------------------------------------------------------------------------------------------
    /// Epidemic peer sample set size.
    #[arg(long, default_value_t = NodeConfig::default().peer_count)]
    peer_count: usize,

    /// A peer is eligible to receive gossips unless it was last seen longer than this ago.
    #[arg(long, value_parser = parse_duration, default_value_t = NodeConfig::default().peer_age_reachable)]
    peer_age_reachable: Duration,

    /// A peer will be replaced unconditionally at next opportunity (bypassing probabilistic sampling)
    /// if it was last seen longer than this ago.
    #[arg(long, value_parser = parse_duration, default_value_t = NodeConfig::default().peer_age_replaceable)]
    peer_age_replaceable: Duration,

    /// Peers that are still reachable (which are all peers during normal operation) will be replaced anyway
    /// with this probability at each gossip outside of the moratorium period to ensure mixing.
    #[arg(long, default_value_t = NodeConfig::default().peer_replacement_probability)]
    peer_replacement_probability: f64,

    /// After a peer replacement, there is a moratorium period during which the new peer cannot be replaced again to
    /// make the peer churn rate less dependent on the network size, ensuring more consistent parameters across
    /// networks of various sizes.
    #[arg(long, value_parser = parse_duration_range, default_value = "0..1")]
    peer_moratorium_range: RangeInclusive<Duration>,

    // ----------------------------------------------------------------------------------------------------------------
    /// Epidemic duplicate gossip drop cache is necessary for network load regulation; see the model.
    #[arg(long, default_value_t = NodeConfig::default().dedup_capacity)]
    dedup_capacity: usize,

    /// Gossips that have been seen more than this long ago are considered fresh.
    #[arg(long, value_parser = parse_duration, default_value_t = NodeConfig::default().dedup_timeout)]
    dedup_timeout: Duration,

    // ----------------------------------------------------------------------------------------------------------------
    /// Imperfect network simulation. Packets take a random time in this range to be delivered.
    #[arg(long, value_parser = parse_duration_range, default_value = "0..0.1")]
    network_delay_range: RangeInclusive<Duration>,

    #[arg(long, default_value = "0.0001")]
    network_loss_probability: f64,
}

impl Config {
    fn network(&self) -> NetworkConfig {
        NetworkConfig {
            node_count: self.node_count,
            delay_range: self.network_delay_range.clone(),
            loss_probability: self.network_loss_probability,
        }
    }

    fn node(&self) -> NodeConfig {
        NodeConfig {
            subject_id_modulus: self.subject_id_modulus,
            gossip_period: self.gossip_period,
            gossip_dither: self.gossip_dither,
            gossip_broadcast_every: self.gossip_broadcast_every,
            gossip_ttl_periodic: self.gossip_ttl_periodic,
            gossip_ttl_urgent: self.gossip_ttl_urgent,
            gossip_outdegree_periodic: self.gossip_outdegree_periodic,
            gossip_outdegree_urgent: self.gossip_outdegree_urgent,
            peer_count: self.peer_count,
            peer_age_reachable: self.peer_age_reachable,
            peer_age_replaceable: self.peer_age_replaceable,
            peer_replacement_probability: self.peer_replacement_probability,
            peer_moratorium_range: self.peer_moratorium_range.clone(),
            dedup_capacity: self.dedup_capacity,
            dedup_timeout: self.dedup_timeout,
        }
    }

    fn simulation(&self) -> SimulationConfig {
        SimulationConfig { time_limit: self.time_limit }
    }
}

fn main() -> ExitCode {
    let mut config = Config::parse();
    if config.topic_count >= (config.subject_id_modulus as usize) / 2 {
        Config::command().error(ErrorKind::ValueValidation, "too many topics for this modulus").exit();
    }
    if let None = config.seed {
        config.seed = Some(generate_seed());
        eprintln!("Using automatic --seed={0}", config.seed.unwrap());
    }
    let node_count = config.node_count;
    let topic_count = config.topic_count;
    let node_config = config.node();
    let network_config = config.network();
    let simulation_config = config.simulation();
    let mut rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(config.seed.unwrap())));
    drop(config);

    // Set up the simulation.
    let mut sim =
        Simulation::generate(node_count, topic_count, rng.clone(), network_config, node_config, simulation_config)
            .unwrap_or_else(|e| {
                eprintln!("Error generating simulation: {0}", e);
                std::process::exit(1);
            });

    // Run the simulation until convergence or time limit.
    // TODO: report the initial network configuration and the final state.
    let outcome = sim.run();

    match outcome {
        SimulationOutcome::TimeLimitReached => {
            eprintln!("Simulation did not converge within the time limit.");
            ExitCode::FAILURE
        }
        SimulationOutcome::Converged(time) => {
            println!("Simulation converged at {0:.3} seconds.", time.as_seconds_f64());
            ExitCode::SUCCESS
        }
    }
}

fn generate_seed() -> u64 {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    now.as_secs() ^ ((now.subsec_nanos() as u64) << 32)
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

fn parse_duration(s: &str) -> Result<Duration, String> {
    let trimmed = s.trim();
    if let Ok(seconds) = trimmed.parse::<f64>() {
        if !seconds.is_finite() || seconds < 0.0 {
            return Err("duration must be finite and non-negative".to_string());
        }
        return Ok(Duration::seconds_f64(seconds));
    }
    let parsed = parse_time(trimmed).map_err(|e| e.to_string())?;
    if parsed.is_negative() {
        return Err("duration must be finite and non-negative".to_string());
    }
    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_duration_accepts_fractional_seconds() {
        assert_eq!(Duration::milliseconds(125), parse_duration("0.125").unwrap());
        assert!(parse_duration("-1").is_err());
        assert!(parse_duration("nan").is_err());
    }

    #[test]
    fn parse_duration_accepts_human_units() {
        assert_eq!(Duration::seconds(123), parse_duration("123s").unwrap());
        assert_eq!(Duration::seconds(123), parse_duration("123").unwrap());
        assert_eq!(Duration::milliseconds(125), parse_duration("125ms").unwrap());
        assert_eq!(Duration::seconds(62), parse_duration("1m2s").unwrap());
    }

    #[test]
    fn parse_duration_accepts_time_display_output() {
        let rendered = Duration::seconds(62).to_string(); // "1m2s"
        assert_eq!(Duration::seconds(62), parse_duration(&rendered).unwrap());
    }

    #[test]
    fn parse_duration_range_requires_ordered_bounds() {
        let range = parse_duration_range("0.25..1.5").unwrap();
        assert_eq!(Duration::milliseconds(250), *range.start());
        assert_eq!(Duration::milliseconds(1500), *range.end());
        assert!(parse_duration_range("2..1").is_err());
    }

    #[test]
    fn parse_duration_range_accepts_human_units() {
        let range = parse_duration_range("125ms..1m2s").unwrap();
        assert_eq!(Duration::milliseconds(125), *range.start());
        assert_eq!(Duration::seconds(62), *range.end());
    }
}
