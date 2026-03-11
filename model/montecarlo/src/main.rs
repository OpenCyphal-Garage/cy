//! Copyright (c) Pavel Kirienko <pavel@opencyphal.org>

#![allow(dead_code, unused_variables, unused_mut)]

pub mod message;
pub mod node;
pub mod simulation;
pub mod topic;
mod util;

use node::NodeConfig;
use simulation::{Simulation, SimulationConfig, SimulationOutcome, Snapshot};
use util::{
    TimeStats, derive_seed, generate_seed, parse_duration, parse_duration_range, print_convergence_histogram,
    worker_count,
};

use clap::{CommandFactory, Parser, error::ErrorKind};
use rand::SeedableRng;
use rand::rngs::SmallRng;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::BTreeSet;
use std::ops::RangeInclusive;
use std::process::ExitCode;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;
use time::Duration;

const PROGRESS_REPORT_PERIOD: std::time::Duration = std::time::Duration::from_secs(10);

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
    /// The largest 16-bit prime is 65521.
    #[arg(long, default_value_t = NodeConfig::default().subject_id_modulus)]
    subject_id_modulus: u16,

    /// Optional seed for reproducible random initialization. If omitted, current time is used.
    #[arg(long)]
    seed: Option<u64>,

    /// Number of independent simulation runs.
    #[arg(long, default_value_t = 1)]
    runs: usize,

    /// Limit simulation time. Expect convergence before this.
    #[arg(long, value_parser = parse_duration, default_value = "60")]
    time_limit: Duration,

    /// Interval between network snapshot captures. Zero to capture a snapshot at every step (needs a lot of memory).
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

#[derive(Debug)]
enum RunStatus {
    Completed(SimulationOutcome),
    GenerationError(String),
}

#[derive(Debug)]
struct RunResult {
    run_index: usize,
    status: RunStatus,
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
        SimulationConfig {
            time_limit: self.time_limit,
            node_count: self.node_count,
            network_delay_range: self.network_delay_range.clone(),
            network_loss_probability: self.network_loss_probability,
        }
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

    if config.runs > 1 { run_parallel(config) } else { run_single(config) }
}

fn run_single(config: Config) -> ExitCode {
    let node_config = config.node();
    let simulation_config = config.simulation();
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(config.seed.unwrap())));

    // Set up the simulation.
    let mut sim = Simulation::generate(config.node_count, config.topic_count, rng, &node_config, &simulation_config)
        .unwrap_or_else(|e| {
            eprintln!("Error generating simulation: {0}", e);
            std::process::exit(1);
        });

    // Snapshot processor.
    let mut snap_last: Option<Snapshot> = None;
    let mut snap_first: Option<Snapshot> = None;
    let process_snapshot = Box::new(|snap: &Snapshot| {
        if let None = snap_last {
            snap_last = Some(snap.clone());
            snap_first = Some(snap.clone());
            let unique_topic_count =
                snap.nodes.iter().flat_map(|n| n.topics.iter().map(|t| t.hash())).collect::<BTreeSet<_>>().len();
            eprintln!(
                "Total nodes: {}, topics: {}, subject ID modulus: {}",
                snap.nodes.len(),
                unique_topic_count,
                snap.nodes[0].subject_id_modulus
            );
            let mut topics_by_node = snap.nodes.iter().map(|n| n.topics.len()).collect::<Vec<_>>();
            topics_by_node.sort();
            let topics_by_node_head = topics_by_node.iter().take(min(10, topics_by_node.len() / 3));
            let topics_by_node_tail = topics_by_node.iter().rev().take(min(10, topics_by_node.len() / 3)).rev();
            eprintln!(
                "Topic counts by node, sorted: {} ... {}",
                topics_by_node_head.map(|n| n.to_string()).collect::<Vec<_>>().join(", "),
                topics_by_node_tail.map(|n| n.to_string()).collect::<Vec<_>>().join(", ")
            );
            eprintln!(
                "│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^10}│{:^25}│{:^25}│",
                "time [s]",
                "steps",
                "steps/s",
                "collision",
                "divergent",
                "Σ tx",
                "Δ tx",
                "tx/s",
                "Σ rx",
                "Σ loss",
                "Σ rx/node [msg/node]",
                "arrival load [msg/s/node]"
            );
        }
        let t = snap.time.as_seconds_f64();
        let dt = t - snap_last.as_ref().expect("last snapshot must be available").time.as_seconds_f64();
        let step_rate = if dt > 0.0 {
            ((snap.steps - snap_last.as_ref().expect("last snapshot must be available").steps) as f64) / dt
        } else {
            0.0
        };
        let tx_delta = snap.tx_total - snap_last.as_ref().expect("last snapshot must be available").tx_total;
        let tx_rate = if dt > 0.0 { (tx_delta as f64) / dt } else { 0.0 };
        let node_count = snap.nodes.len();
        let rx_per_node_cumulative = snap.rx_total as f64 / (node_count as f64);
        let arrival_load_per_node = if t > 0.0 { rx_per_node_cumulative / t } else { 0.0 };
        eprintln!(
            "│{:10.3}│{:10}│{:10.1}│{:10}│{:10}│{:10}│{:10}│{:10.1}│{:10}│{:10}│{:25.1}│{:25.1}│",
            t,
            snap.steps,
            step_rate,
            snap.count_collisions(),
            snap.count_divergent(),
            snap.tx_total,
            tx_delta,
            tx_rate,
            snap.rx_total,
            snap.loss_total,
            rx_per_node_cumulative,
            arrival_load_per_node
        );
        snap_last = Some(snap.clone());
    });

    // Run the simulation until convergence or time limit.
    let outcome = sim.run(process_snapshot, config.snapshot_period);

    // Generate reports.
    let snap_first = snap_first.unwrap();
    let snap_last = snap_last.unwrap();
    // TODO

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

fn run_parallel(config: Config) -> ExitCode {
    let run_count = config.runs;
    let base_seed = config.seed.expect("seed must be set in main");
    let node_count = config.node_count;
    let topic_count = config.topic_count;
    let node_config = config.node();
    let simulation_config = config.simulation();

    let worker_count = worker_count();
    eprintln!("Running {run_count} simulations using {worker_count} workers (base --seed={base_seed}).");

    // Set up the worker pool.
    let next_job = Arc::new(AtomicUsize::new(0));
    let (result_tx, result_rx) = mpsc::channel::<RunResult>();
    let mut handles = Vec::with_capacity(worker_count);
    for _ in 0..worker_count {
        let next_job = Arc::clone(&next_job);
        let result_tx = result_tx.clone();
        let node_config = node_config.clone();
        let simulation_config = simulation_config.clone();
        handles.push(thread::spawn(move || {
            loop {
                let run_index = next_job.fetch_add(1, Ordering::Relaxed);
                if run_index >= run_count {
                    break;
                }
                let seed = derive_seed(base_seed, run_index);
                let status = run_one_simulation(node_count, topic_count, seed, &node_config, &simulation_config);
                if result_tx.send(RunResult { run_index, status }).is_err() {
                    break;
                }
            }
        }));
    }
    drop(result_tx);

    // Collect results and report progress until all runs are completed.
    let mut completed = 0usize;
    let mut time_limit_failures = 0usize;
    let mut generation_failures = 0usize;
    let mut converged_times = Vec::<Duration>::with_capacity(run_count);
    let mut next_report_at = Instant::now() + PROGRESS_REPORT_PERIOD;
    while completed < run_count {
        let now = Instant::now();
        if now >= next_report_at {
            report_parallel_progress(completed, run_count, time_limit_failures + generation_failures);
            next_report_at += PROGRESS_REPORT_PERIOD;
            continue;
        }
        let wait_duration = next_report_at.saturating_duration_since(now);
        match result_rx.recv_timeout(wait_duration) {
            Ok(result) => {
                completed += 1;
                match result.status {
                    RunStatus::Completed(SimulationOutcome::Converged(time)) => converged_times.push(time),
                    RunStatus::Completed(SimulationOutcome::TimeLimitReached) => time_limit_failures += 1,
                    RunStatus::GenerationError(err) => {
                        generation_failures += 1;
                        eprintln!("run {} failed during setup: {err}", result.run_index);
                    }
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                continue;
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                break;
            }
        }
    }

    // Collect the results of all workers to detect any panics.
    let mut panicked_workers = 0usize;
    for handle in handles {
        if handle.join().is_err() {
            panicked_workers += 1;
        }
    }

    // Final report.
    if completed < run_count {
        let missing = run_count - completed;
        generation_failures += missing;
        eprintln!("Only {completed}/{run_count} runs produced outcomes; treating the remaining {missing} as failures.");
    }
    let failure_count = time_limit_failures + generation_failures;
    if panicked_workers > 0 {
        eprintln!("{panicked_workers} worker thread(s) panicked.");
    }
    eprintln!("Completed: converged={}, failed={}, remaining=0", converged_times.len(), failure_count);
    if let Some(stats) = TimeStats::compute(&converged_times) {
        eprintln!(
            "Convergence time stats [s] (successful runs only): min={:.3}, mean={:.3}, median={:.3}, max={:.3}",
            stats.min, stats.mean, stats.median, stats.max
        );
    } else {
        eprintln!("Convergence time stats [s]: n/a (no successful runs)");
    }
    if time_limit_failures > 0 {
        eprintln!("Runs that did not converge before time limit: {time_limit_failures}");
    }
    print_convergence_histogram(&converged_times, simulation_config.time_limit);

    if (failure_count > 0) || (panicked_workers > 0) { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

fn run_one_simulation(
    node_count: usize,
    topic_count: usize,
    seed: u64,
    node_config: &NodeConfig,
    simulation_config: &SimulationConfig,
) -> RunStatus {
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(seed)));
    let mut sim = match Simulation::generate(node_count, topic_count, rng, node_config, simulation_config) {
        Ok(sim) => sim,
        Err(err) => return RunStatus::GenerationError(err),
    };
    RunStatus::Completed(sim.run_quiet())
}

fn report_parallel_progress(completed: usize, total: usize, failures: usize) {
    let remaining = total - completed;
    eprintln!("Progress: completed={completed}/{total}, remaining={remaining}, failed={failures}");
}
