//! Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#![allow(dead_code, unused_variables, unused_mut)]

pub mod message;
pub mod node;
pub mod simulation;
pub mod topic;
mod util;

use node::NodeConfig;
use simulation::{NetworkConfig, Simulation, SimulationConfig, SimulationOutcome, Snapshot};
use util::{generate_seed, parse_duration, parse_duration_range};

use clap::{CommandFactory, Parser, error::ErrorKind};
use rand::SeedableRng;
use rand::rngs::SmallRng;
use std::cell::RefCell;
use std::ops::RangeInclusive;
use std::process::ExitCode;
use std::rc::Rc;
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

    /// Interval between network snapshot captures.
    #[arg(long, value_parser = parse_duration, default_value = "1")]
    snapshot_period: Duration,

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
        let network = NetworkConfig {
            node_count: self.node_count,
            delay_range: self.network_delay_range.clone(),
            loss_probability: self.network_loss_probability,
        };
        SimulationConfig { time_limit: self.time_limit, network }
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
    let snapshot_period = config.snapshot_period;
    let simulation_config = config.simulation();
    let mut rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(config.seed.unwrap())));
    drop(config);

    // Set up the simulation.
    let mut sim = Simulation::generate(node_count, topic_count, rng.clone(), &node_config, &simulation_config)
        .unwrap_or_else(|e| {
            eprintln!("Error generating simulation: {0}", e);
            std::process::exit(1);
        });

    // Snapshot processor.
    eprintln!(
        "│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^25}│{:^25}│",
        "time [s]",
        "steps",
        "collision",
        "divergent",
        "tx cumul",
        "rx cumul",
        "loss cumul",
        "rx/node cumul [msg/node]",
        "arrival load [msg/s/node]"
    );
    let process_snapshot = Box::new(move |snap: &Snapshot| {
        let t = snap.time.as_seconds_f64();
        let node_count = snap.nodes.len();
        let rx_per_node_cumulative = snap.rx_total as f64 / (node_count as f64);
        let arrival_load_per_node = if t > 0.0 { rx_per_node_cumulative / t } else { 0.0 };
        eprintln!(
            "│{:10.3}│{:10}│{:10}│{:10}│{:10}│{:10}│{:10}│{:25.1}│{:25.1}│",
            t,
            snap.steps,
            snap.count_collisions(),
            snap.count_divergent(),
            snap.tx_total,
            snap.rx_total,
            snap.loss_total,
            rx_per_node_cumulative,
            arrival_load_per_node
        );
    });

    // Run the simulation until convergence or time limit.
    // TODO: report the initial network configuration and the final state.
    let outcome = sim.run(process_snapshot, snapshot_period);

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
