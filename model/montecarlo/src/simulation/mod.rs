mod network;

use self::network::{Network, NetworkConfig};
use crate::message::Transmit;
use crate::node::{Node, NodeConfig, count_colliding_subjects};
use crate::topic::Topic;
use rand::Rng;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;
use std::rc::Rc;
use time::Duration;

const MIN_STEP: Duration = Duration::microseconds(10);

/// This has to be not larger than the smallest bin in the output convergence time histogram,
/// otherwise the histogram will show gaps, which can be highly misleading!
const CONVERGENCE_CHECK_PERIOD: Duration = Duration::seconds(1);

#[derive(Debug, Clone)]
pub struct SimulationConfig {
    pub time_limit: Duration,
    pub node_count: usize,
    pub network_delay_range: RangeInclusive<Duration>,
    pub network_loss_probability: f64,
}

pub struct Simulation<'a> {
    network: Rc<RefCell<Network>>,
    nodes: Vec<Node<'a>>,
    node_update_queue: BTreeSet<(Duration, usize)>,
    node_update_deadlines: Vec<Duration>,
    now: Rc<RefCell<Duration>>,
    step_count: u64,
    converged_at: Option<Duration>,
    next_convergence_check_at: Duration,
    cfg: SimulationConfig,
}

#[derive(Debug)]
pub enum SimulationOutcome {
    Converged(Duration),
    TimeLimitReached,
}

impl<'a> Simulation<'a> {
    pub fn generate(
        node_count: usize,
        topic_count: usize,
        rng: Rc<RefCell<dyn Rng>>,
        node_config: &NodeConfig,
        cfg: &SimulationConfig,
    ) -> Result<Self, String> {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let network_now_provider: Rc<dyn Fn() -> Duration + 'static> = {
            let now = now.clone();
            Rc::new(move || *now.borrow())
        };
        let node_now_provider: Rc<dyn Fn() -> Duration + 'a> = {
            let now = now.clone();
            Rc::new(move || *now.borrow())
        };
        let network_config = NetworkConfig {
            node_count,
            delay_range: cfg.network_delay_range.clone(),
            loss_probability: cfg.network_loss_probability,
        };
        let network = Rc::new(RefCell::new(Network::new(&network_config, network_now_provider, rng.clone())));
        let nodes =
            generate_network(node_count, topic_count, node_now_provider, rng.clone(), network.clone(), node_config)?;
        let mut node_update_queue = BTreeSet::new();
        let mut node_update_deadlines = vec![Duration::MAX; nodes.len()];
        for (index, node) in nodes.iter().enumerate() {
            let deadline = node.next_update_at();
            node_update_deadlines[index] = deadline;
            node_update_queue.insert((deadline, index));
        }
        Ok(Self {
            network,
            nodes,
            node_update_queue,
            node_update_deadlines,
            now,
            step_count: 0,
            converged_at: None,
            next_convergence_check_at: Duration::ZERO,
            cfg: cfg.clone(),
        })
    }

    pub fn step(&mut self) -> Option<SimulationOutcome> {
        let now = *self.now.borrow();
        self.process_due_events(now);

        let now = *self.now.borrow();
        self.maybe_recompute_convergence_state(now);
        if let Some(outcome) = self.try_convergence_outcome(now) {
            return Some(outcome);
        }

        // Advance the time to the next node/network/convergence-check event.
        let next_node_update = self.next_node_update_at();
        let next_arrival = self.network.borrow().soonest_arrival_at().unwrap_or(Duration::MAX);
        let mut next_time = min(min(next_node_update, next_arrival), self.next_convergence_check_at);
        if next_time < now {
            next_time = now;
        }
        if next_time >= self.cfg.time_limit {
            *self.now.borrow_mut() = self.cfg.time_limit;
            self.recompute_convergence_state(self.cfg.time_limit);
            return Some(SimulationOutcome::TimeLimitReached);
        }
        *self.now.borrow_mut() = if next_time > now { next_time } else { now + MIN_STEP };

        None
    }

    pub fn run<'z>(
        &mut self,
        mut reporter: Box<dyn FnMut(&Snapshot) -> () + 'z>,
        report_period: Duration,
    ) -> SimulationOutcome {
        let mut snap = self.capture();
        reporter(&snap);
        loop {
            if *self.now.borrow() - snap.time >= report_period {
                snap = self.capture();
                reporter(&snap);
            }
            let outcome = self.step();
            if let Some(outcome) = outcome {
                snap = self.capture();
                reporter(&snap); // Always capture the final state.
                return outcome;
            }
        }
    }

    pub fn run_quiet(&mut self) -> SimulationOutcome {
        loop {
            if let Some(outcome) = self.step() {
                return outcome;
            }
        }
    }

    fn capture(&self) -> Snapshot {
        let net = self.network.borrow().stats();
        Snapshot {
            time: *self.now.borrow(),
            steps: self.step_count,
            nodes: self.nodes.iter().map(NodeSnapshot::new).collect(),
            tx_total: net.sent_total(),
            broadcast_tx_total: net.broadcast_sent_total(),
            shard_tx_total: net.shard_sent_total(),
            rx_total: net.received_total(),
            broadcast_rx_total: net.broadcast_received_total(),
            shard_rx_total: net.shard_received_total(),
            loss_total: net.lost,
        }
    }

    fn process_due_events(&mut self, now: Duration) {
        // Periodic updates are evaluated exactly once at this timestamp.
        let mut periodic_due_nodes = self.take_periodic_due_nodes(now);
        periodic_due_nodes.sort_unstable();
        let mut include_periodic_due = true;
        loop {
            let mut arrivals = self
                .network
                .borrow_mut()
                .drain_due(now)
                .into_iter()
                .map(|(destination, messages)| {
                    let index = destination as usize;
                    debug_assert!(index < self.nodes.len(), "arrival destination does not match any node");
                    (index, messages)
                })
                .collect::<Vec<_>>();
            let periodic = if include_periodic_due { &periodic_due_nodes[..] } else { &[] };
            if periodic.is_empty() && arrivals.is_empty() {
                break;
            }

            let mut periodic_index = 0_usize;
            let mut arrival_index = 0_usize;
            while (periodic_index < periodic.len()) || (arrival_index < arrivals.len()) {
                let (index, incoming) = if arrival_index >= arrivals.len() {
                    let index = periodic[periodic_index];
                    periodic_index += 1;
                    (index, Vec::new())
                } else if periodic_index >= periodic.len() {
                    let index = arrivals[arrival_index].0;
                    let incoming = std::mem::take(&mut arrivals[arrival_index].1);
                    arrival_index += 1;
                    (index, incoming)
                } else {
                    let periodic_index_value = periodic[periodic_index];
                    let arrival_index_value = arrivals[arrival_index].0;
                    if periodic_index_value < arrival_index_value {
                        periodic_index += 1;
                        (periodic_index_value, Vec::new())
                    } else if arrival_index_value < periodic_index_value {
                        let incoming = std::mem::take(&mut arrivals[arrival_index].1);
                        arrival_index += 1;
                        (arrival_index_value, incoming)
                    } else {
                        periodic_index += 1;
                        let incoming = std::mem::take(&mut arrivals[arrival_index].1);
                        arrival_index += 1;
                        (arrival_index_value, incoming)
                    }
                };
                self.nodes[index].step(incoming);
                self.refresh_node_update(index);
            }

            self.step_count = self.step_count.wrapping_add(1);
            // Periodic updates are checked only on entry at this timestamp.
            include_periodic_due = false;
            periodic_due_nodes.clear();
        }
    }

    fn next_node_update_at(&mut self) -> Duration {
        self.node_update_queue.first().map(|(time, _)| *time).unwrap_or(Duration::MAX)
    }

    fn take_periodic_due_nodes(&mut self, now: Duration) -> Vec<usize> {
        let mut due = Vec::new();
        while let Some((time, index)) = self.node_update_queue.first().copied() {
            if time > now {
                break;
            }
            self.node_update_queue.pop_first();
            due.push(index);
        }
        due
    }

    fn refresh_node_update(&mut self, index: usize) {
        let previous = self.node_update_deadlines[index];
        self.node_update_queue.remove(&(previous, index));
        let updated = self.nodes[index].next_update_at();
        self.node_update_deadlines[index] = updated;
        self.node_update_queue.insert((updated, index));
    }

    fn maybe_recompute_convergence_state(&mut self, now: Duration) {
        while now >= self.next_convergence_check_at {
            self.recompute_convergence_state(now);
            self.next_convergence_check_at += CONVERGENCE_CHECK_PERIOD;
        }
    }

    fn recompute_convergence_state(&mut self, now: Duration) {
        let collisions = count_collisions(&self.nodes);
        let divergences = count_divergent(&self.nodes);
        match self.converged_at {
            Some(_) => {
                if collisions > 0 || divergences > 0 {
                    self.converged_at = None;
                }
            }
            None => {
                if collisions == 0 && divergences == 0 {
                    self.converged_at = Some(now);
                }
            }
        }
    }

    fn try_convergence_outcome(&mut self, now: Duration) -> Option<SimulationOutcome> {
        let stability_window = Duration::seconds_f64(
            self.nodes.len() as f64 * self.network.borrow().config().delay_range.end().as_seconds_f64(),
        );
        let required_stability = min(stability_window, Duration::seconds(10));
        if let Some(t) = self.converged_at {
            if now - t > required_stability {
                // Ensure final outcome uses freshly recomputed full-state consensus status.
                self.recompute_convergence_state(now);
                if let Some(updated) = self.converged_at {
                    if now - updated > required_stability {
                        return Some(SimulationOutcome::Converged(updated));
                    }
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct NodeSnapshot {
    pub id: u16,
    pub subject_id_modulus: u32,
    pub topics: Vec<Topic>,
}

impl NodeSnapshot {
    pub fn new(node: &Node<'_>) -> Self {
        Self {
            id: node.id(),
            subject_id_modulus: node.subject_id_modulus(),
            topics: node.topics_iter().cloned().collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Snapshot {
    pub time: Duration,
    pub steps: u64,
    pub nodes: Vec<NodeSnapshot>,
    pub tx_total: u64,
    pub broadcast_tx_total: u64,
    pub shard_tx_total: u64,
    pub rx_total: u64,
    pub broadcast_rx_total: u64,
    pub shard_rx_total: u64,
    pub loss_total: u64,
}

impl Snapshot {
    pub fn count_collisions(&self) -> usize {
        if self.nodes.is_empty() {
            return 0;
        }
        let subject_id_modulus = self.nodes[0].subject_id_modulus;
        count_colliding_subjects(self.nodes.iter().flat_map(|node| node.topics.iter()), subject_id_modulus)
    }

    pub fn count_divergent(&self) -> usize {
        let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
        for topic in self.nodes.iter().flat_map(|node| node.topics.iter()) {
            by_hash.entry(topic.hash()).or_default().insert(topic.evictions());
        }
        by_hash.values().filter(|evictions| evictions.len() > 1).count()
    }
}

fn count_collisions(nodes: &[Node<'_>]) -> usize {
    if nodes.is_empty() {
        return 0;
    }
    let subject_id_modulus = nodes[0].subject_id_modulus();
    count_colliding_subjects(nodes.iter().flat_map(|node| node.topics_iter()), subject_id_modulus)
}

fn count_divergent(nodes: &[Node<'_>]) -> usize {
    let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
    for topic in nodes.iter().flat_map(|node| node.topics_iter()) {
        by_hash.entry(topic.hash()).or_default().insert(topic.evictions());
    }
    by_hash.values().filter(|evictions| evictions.len() > 1).count()
}

/// Generates a random network of nodes and returns them.
fn generate_network<'a>(
    node_count: usize,
    topic_count: usize,
    now: Rc<dyn Fn() -> Duration + 'a>,
    rng: Rc<RefCell<dyn Rng>>,
    network: Rc<RefCell<dyn Transmit + 'a>>,
    node_config: &NodeConfig,
) -> Result<Vec<Node<'a>>, String> {
    if topic_count == 0 {
        return Err("topic_count must be positive".to_string());
    }
    let shard_count = u32::try_from(topic_count).map_err(|_| "topic_count is too large for u32 shard IDs")?;

    // Generate random topics to choose from later.
    let mut topic_hashes = Vec::new();
    for _ in 0..topic_count {
        topic_hashes.push(rng.borrow_mut().next_u64());
    }

    // Generate nodes utilizing those topics.
    let mut nodes = Vec::new();
    assert!(node_count <= u16::MAX as usize);
    for id in 0..(node_count as u16) {
        nodes.push(Node::new(id, shard_count, network.clone(), rng.clone(), now.clone(), node_config)?);
        let node = nodes.last_mut().expect("node was just pushed");
        let node_topic_count = (rng.borrow_mut().next_u64() % (topic_count as u64)) + 1;
        assert!(node_topic_count >= 1 && node_topic_count <= topic_count as u64);
        for _ in 0..node_topic_count {
            // We may accidentally draw the same topic multiple times, which is fine as it just means the node will
            // have fewer topics -- add_topic() on an existing topic is a no-op.
            let topic_hash = topic_hashes[rng.borrow_mut().next_u64() as usize % topic_count];
            node.add_topic(topic_hash);
        }
        network.borrow_mut().set_node_shards(id, node.shard_ids());
    }
    Ok(nodes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    fn make_snapshot(evictions_by_node: &[Vec<(u64, u16)>]) -> Snapshot {
        Snapshot {
            time: Duration::ZERO,
            steps: 0,
            nodes: evictions_by_node
                .iter()
                .enumerate()
                .map(|(id, topics)| NodeSnapshot {
                    id: id as u16,
                    subject_id_modulus: 1999,
                    topics: topics
                        .iter()
                        .map(|(hash, evictions)| {
                            let mut topic = Topic::new(*hash, Duration::ZERO);
                            topic.set_evictions(*evictions);
                            topic
                        })
                        .collect(),
                })
                .collect(),
            tx_total: 0,
            broadcast_tx_total: 0,
            shard_tx_total: 0,
            rx_total: 0,
            broadcast_rx_total: 0,
            shard_rx_total: 0,
            loss_total: 0,
        }
    }

    #[test]
    fn count_divergent_counts_hashes_with_distinct_eviction_values() {
        let snapshot = make_snapshot(&[vec![(1, 0), (2, 0)], vec![(1, 1), (2, 0)], vec![(1, 1), (2, 0)]]);
        assert_eq!(1, snapshot.count_divergent());
    }

    #[test]
    fn step_advances_to_convergence_check_without_other_events() {
        let node_cfg = NodeConfig::default();
        let sim_cfg = SimulationConfig {
            time_limit: Duration::seconds(20),
            node_count: 1,
            network_delay_range: Duration::ZERO..=Duration::milliseconds(10),
            network_loss_probability: 0.0,
        };
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(1)));
        let mut sim = Simulation::generate(1, 1, rng, &node_cfg, &sim_cfg).expect("simulation generation failed");

        sim.converged_at = None;
        sim.next_convergence_check_at = Duration::seconds(1);
        sim.node_update_queue.clear();
        sim.node_update_queue.insert((Duration::seconds(10), 0));
        sim.node_update_deadlines[0] = Duration::seconds(10);

        assert!(sim.step().is_none());
        assert_eq!(Duration::seconds(1), *sim.now.borrow());

        assert_eq!(None, sim.converged_at);
        assert!(sim.step().is_none());
        assert_eq!(Some(Duration::seconds(1)), sim.converged_at);
    }

    #[test]
    fn contested_network_does_not_linger_unresolved_without_active_repairs() {
        let node_cfg = NodeConfig { subject_id_modulus: 127, ..NodeConfig::default() };
        let sim_cfg = SimulationConfig {
            time_limit: Duration::seconds(10),
            node_count: 60,
            network_delay_range: Duration::ZERO..=Duration::milliseconds(10),
            network_loss_probability: 0.0,
        };
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(4009897536515330144)));
        let mut sim = Simulation::generate(60, 60, rng, &node_cfg, &sim_cfg).expect("simulation generation failed");
        let startup_cutoff = node_cfg.gossip_startup_delay + Duration::seconds(1);
        let max_quiet_gap = Duration::seconds(1);
        let mut found = None;

        loop {
            let now = *sim.now.borrow();
            let collisions = count_collisions(&sim.nodes);
            let divergences = count_divergent(&sim.nodes);
            let pending_urgent = sim.nodes.iter().map(Node::pending_urgent_count).sum::<usize>();
            let next_arrival = sim.network.borrow().soonest_arrival_at().unwrap_or(Duration::MAX);
            let next_node = sim.next_node_update_at();
            let next_event_at = min(next_node, next_arrival);
            let quiet_gap = if next_event_at == Duration::MAX { Duration::MAX } else { next_event_at - now };

            if now >= startup_cutoff
                && (collisions > 0 || divergences > 0)
                && pending_urgent == 0
                && next_arrival == Duration::MAX
                && quiet_gap >= max_quiet_gap
            {
                found = Some((now, collisions, divergences, quiet_gap));
                break;
            }

            if sim.step().is_some() {
                break;
            }
        }

        assert_eq!(None, found, "entered a quiescent unresolved state after startup: {:?}", found);
    }
}
