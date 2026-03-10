use crate::network::Network;
use crate::node::{Node, count_colliding_subjects};
use rand::prelude::SmallRng;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct SimulationConfig {
    pub time_limit: Duration,
}

#[derive(Debug, Clone)]
pub struct Simulation<'a> {
    network: Network<'a>,
    nodes: Vec<Node>,
    now: Duration,
    snaps: Vec<Snapshot>,
    converged_at: Option<Duration>,
    rng: Rc<RefCell<SmallRng>>,
    cfg: SimulationConfig,
}

pub enum SimulationOutcome {
    Converged(Duration),
    TimeLimitReached,
}

impl<'a> Simulation<'a> {
    pub fn new(network: Network<'a>, nodes: Vec<Node>, cfg: SimulationConfig, rng: Rc<RefCell<SmallRng>>) -> Self {
        Self { network, nodes, now: Duration::ZERO, snaps: Vec::new(), converged_at: None, rng, cfg }
    }

    pub fn step(&mut self) -> Option<SimulationOutcome> {
        // Step all nodes.
        for node in &mut self.nodes {
            node.step(self.now);
        }

        // Snapshot.
        self.snaps.push(Snapshot { time: self.now, nodes: self.nodes.clone() });

        // Update the convergence state.
        let collisions = self.snaps.last().unwrap().count_collisions();
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
            let stability_window = Duration::from_secs_f64(
                self.nodes.len() as f64 * self.network.config().delay_range.end().as_secs_f64(),
            );
            if self.now - t > stability_window {
                return Some(SimulationOutcome::Converged(t));
            }
        }

        // Advance the time to the next event.
        let next_time = min(
            self.nodes.iter().map(|node| node.next_update_at()).min().unwrap(),
            self.network.soonest_arrival_at().unwrap_or(Duration::MAX),
        );
        assert!(next_time >= self.now);
        self.now = next_time;
        if self.now >= self.cfg.time_limit {
            return Some(SimulationOutcome::TimeLimitReached);
        }

        None
    }

    pub fn run(&mut self) -> SimulationOutcome {
        loop {
            if let Some(outcome) = self.step() {
                return outcome;
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Snapshot {
    time: Duration,
    nodes: Vec<Node>,
}

impl Snapshot {
    pub fn count_collisions(&self) -> usize {
        if self.nodes.len() == 0 {
            return 0;
        }
        let subject_id_modulus = self.nodes[0].subject_id_modulus();
        count_colliding_subjects(self.nodes.iter().flat_map(|node| node.topics()), subject_id_modulus)
    }

    pub fn count_divergent(&self) -> usize {
        let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
        for topic in self.nodes.iter().flat_map(|node| node.topics()) {
            by_hash.entry(topic.hash()).or_default().insert(topic.evictions());
        }
        by_hash.values().filter(|evictions| evictions.len() > 1).count()
    }
}
