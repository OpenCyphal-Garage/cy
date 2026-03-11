mod network;

use self::network::Network;
use crate::message::Transmit;
use crate::node::{Node, NodeConfig, count_colliding_subjects};
use crate::topic::Topic;
use rand::Rng;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use time::Duration;

pub use self::network::{NetworkConfig, NetworkStats};

const MIN_STEP: Duration = Duration::microseconds(50);
const CONVERGENCE_CHECK_PERIOD: Duration = Duration::seconds(1);

#[derive(Debug, Clone)]
pub struct SimulationConfig {
    pub time_limit: Duration,
    pub network: NetworkConfig,
}

pub struct Simulation<'a> {
    network: Rc<RefCell<Network>>,
    nodes: Vec<Node<'a>>,
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
        let network = Rc::new(RefCell::new(Network::new(&cfg.network, network_now_provider, rng.clone())));
        let nodes =
            generate_network(node_count, topic_count, node_now_provider, rng.clone(), network.clone(), node_config)?;
        Ok(Self {
            network,
            nodes,
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

        // Advance the time to the next event.
        let next_node_update = self.nodes.iter().map(|node| node.next_update_at()).min().unwrap_or(Duration::MAX);
        let next_arrival = self.network.borrow().soonest_arrival_at().unwrap_or(Duration::MAX);
        let next_time = min(next_node_update, next_arrival);
        assert!(next_time >= now);
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
            nodes: self.nodes.iter().map(|node| NodeSnapshot::new(node)).collect(),
            tx_total: net.sent_total(),
            rx_total: net.received_total(),
            loss_total: net.lost,
        }
    }

    fn process_due_events(&mut self, now: Duration) {
        // Periodic updates are evaluated exactly once at this timestamp.
        let mut periodic_due = self.nodes.iter().map(|node| node.next_update_at() <= now).collect::<Vec<bool>>();
        loop {
            let arrivals = self.network.borrow_mut().drain_due(now);
            let mut arrivals_iter = arrivals.into_iter().peekable();
            let mut processed_any = false;

            for (index, node) in self.nodes.iter_mut().enumerate() {
                let incoming = if let Some((destination, _)) = arrivals_iter.peek() {
                    if *destination == node.id() {
                        arrivals_iter.next().expect("peeked arrival vanished").1
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };
                if periodic_due[index] || !incoming.is_empty() {
                    node.step(incoming);
                    processed_any = true;
                }
            }
            debug_assert!(arrivals_iter.next().is_none(), "arrival destination does not match any node");
            if !processed_any {
                break;
            }
            self.step_count = self.step_count.wrapping_add(1);
            periodic_due.fill(false);
        }
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
    pub subject_id_modulus: u16,
    pub topics: Vec<Topic>,
    pub peers: Vec<u16>,
}

impl NodeSnapshot {
    pub fn new(node: &Node<'_>) -> Self {
        Self {
            id: node.id(),
            subject_id_modulus: node.subject_id_modulus(),
            topics: node.topics().into_iter().cloned().collect(),
            peers: node.peer_ids(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Snapshot {
    pub time: Duration,
    pub steps: u64,
    pub nodes: Vec<NodeSnapshot>,
    pub tx_total: u64,
    pub rx_total: u64,
    pub loss_total: u64,
}

impl Snapshot {
    pub fn count_collisions(&self) -> usize {
        if self.nodes.len() == 0 {
            return 0;
        }
        let subject_id_modulus = self.nodes[0].subject_id_modulus;
        count_colliding_subjects(self.nodes.iter().flat_map(|node| node.topics.iter().map(|x| x)), subject_id_modulus)
    }

    pub fn count_divergent(&self) -> usize {
        let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
        for topic in self.nodes.iter().flat_map(|node| node.topics.iter()) {
            by_hash.entry(topic.hash()).or_default().insert(topic.evictions());
        }
        by_hash.values().filter(|evictions| evictions.len() > 1).count()
    }
}

fn count_collisions(nodes: &[Node]) -> usize {
    if nodes.len() == 0 {
        return 0;
    }
    let subject_id_modulus = nodes[0].subject_id_modulus();
    count_colliding_subjects(nodes.iter().flat_map(|node| node.topics()), subject_id_modulus)
}

fn count_divergent(nodes: &[Node]) -> usize {
    let mut by_hash: BTreeMap<u64, BTreeSet<u16>> = BTreeMap::new();
    for topic in nodes.iter().flat_map(|node| node.topics()) {
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
    // Generate random topics to choose from later.
    let mut topic_hashes = Vec::new();
    for _ in 0..topic_count {
        topic_hashes.push(rng.borrow_mut().next_u64());
    }

    // Generate nodes utilizing those topics.
    let mut nodes = Vec::new();
    assert!(node_count <= u16::MAX as usize);
    for id in 0..(node_count as u16) {
        nodes.push(Node::new(id, network.clone(), rng.clone(), now.clone(), node_config)?);
        let mut node = nodes.last_mut().unwrap();
        let node_topic_count = (rng.borrow_mut().next_u64() % (topic_count as u64)) + 1;
        assert!(node_topic_count >= 1 && node_topic_count <= topic_count as u64);
        for _ in 0..node_topic_count {
            // We may accidentally draw the same topic multiple times, which is fine as it just means the node will
            // have fewer topics -- add_topic() on an existing topic is a no-op.
            let topic_hash = topic_hashes[rng.borrow_mut().next_u64() as usize % topic_count];
            node.add_topic(topic_hash);
        }
    }
    Ok(nodes)
}
