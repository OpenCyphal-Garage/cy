use crate::network::{Network, Transmit};
use crate::node::{Node, NodeConfig, count_colliding_subjects};
use crate::topic::Topic;
use rand::Rng;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use time::Duration;

#[derive(Debug, Clone)]
pub struct SimulationConfig {
    pub time_limit: Duration,
}

pub struct Simulation<'a> {
    network: Rc<RefCell<Network>>,
    nodes: Vec<Node<'a>>,
    now: Duration,
    snaps: Vec<Snapshot>,
    converged_at: Option<Duration>,
    rng: Rc<RefCell<dyn Rng>>,
    cfg: SimulationConfig,
}

pub enum SimulationOutcome {
    Converged(Duration),
    TimeLimitReached,
}

impl<'a> Simulation<'a> {
    pub fn new(
        network: Rc<RefCell<Network>>,
        nodes: Vec<Node<'a>>,
        cfg: SimulationConfig,
        rng: Rc<RefCell<dyn Rng>>,
    ) -> Self {
        Self { network, nodes, now: Duration::ZERO, snaps: Vec::new(), converged_at: None, rng, cfg }
    }

    pub fn generate(
        node_count: usize,
        topic_count: usize,
        rng: Rc<RefCell<dyn Rng>>,
        network: Rc<RefCell<Network>>,
        node_config: NodeConfig,
        cfg: SimulationConfig,
    ) -> Result<Self, String> {
        let nodes = generate_network(node_count, topic_count, rng.clone(), network.clone(), node_config)?;
        Ok(Self::new(network.clone(), nodes, cfg, rng))
    }

    pub fn step(&mut self) -> Option<SimulationOutcome> {
        self.network.borrow_mut().set_now(self.now);
        // Step all nodes.
        for node in &mut self.nodes {
            let incoming = self.network.borrow_mut().pull(self.now, node.id());
            node.step(self.now, incoming);
        }

        // Snapshot.
        self.snaps
            .push(Snapshot { time: self.now, nodes: self.nodes.iter().map(|node| NodeSnapshot::new(node)).collect() });

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
            let stability_window = Duration::seconds_f64(
                self.nodes.len() as f64 * self.network.borrow().config().delay_range.end().as_seconds_f64(),
            );
            if self.now - t > stability_window {
                return Some(SimulationOutcome::Converged(t));
            }
        }

        // Advance the time to the next event.
        let next_time = min(
            self.nodes.iter().map(|node| node.next_update_at()).min().unwrap(),
            self.network.borrow().soonest_arrival_at().unwrap_or(Duration::MAX),
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
pub struct NodeSnapshot {
    id: u16,
    subject_id_modulus: u16,
    topics: Vec<Topic>,
    peers: Vec<u16>,
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
    time: Duration,
    nodes: Vec<NodeSnapshot>,
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

/// Generates a random network of nodes and returns them.
fn generate_network<'a>(
    node_count: usize,
    topic_count: usize,
    rng: Rc<RefCell<dyn Rng>>,
    network: Rc<RefCell<dyn Transmit + 'a>>,
    node_config: NodeConfig,
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
        nodes.push(Node::new(id, network.clone(), rng.clone(), node_config.clone())?);
        let mut node = nodes.last_mut().unwrap();
        let node_topic_count = (rng.borrow_mut().next_u64() % (topic_count as u64)) + 1;
        assert!(node_topic_count >= 1 && node_topic_count <= topic_count as u64);
        for _ in 0..node_topic_count {
            // We may accidentally draw the same topic multiple times, which is fine as it just means the node will
            // have fewer topics -- add_topic() on an existing topic is a no-op.
            let topic_hash = topic_hashes[rng.borrow_mut().next_u64() as usize % topic_count];
            node.add_topic(topic_hash);
        }
        eprintln!("Node {} has {} topics", node.id(), node.topics().len());
    }
    Ok(nodes)
}
