use crate::message::GossipMessage;
use crate::network::Transmit;
use crate::topic::{Topic, left_wins_collision};
use rand::Rng;
use smart_default::SmartDefault;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;
use std::rc::Rc;
use std::time::Duration;

#[derive(Debug, Clone, SmartDefault)]
pub struct NodeConfig {
    #[default(_code = "1999")]
    pub subject_id_modulus: u16,

    #[default(_code = "Duration::from_secs_f64(1.0)")]
    pub gossip_period: Duration,
    #[default(_code = "Duration::from_secs_f64(0.125)")]
    pub gossip_dither: Duration,
    #[default(_code = "10")]
    pub gossip_broadcast_every: u8,
    #[default(_code = "1")]
    pub gossip_ttl_periodic: u8,
    #[default(_code = "10")]
    pub gossip_ttl_urgent: u8,
    #[default(_code = "1")]
    pub gossip_outdegree_periodic: u8,
    #[default(_code = "2")]
    pub gossip_outdegree_urgent: u8,

    #[default(_code = "8")]
    pub peer_count: usize,
    #[default(_code = "Duration::from_secs(30)")]
    pub peer_age_reachable: Duration,
    #[default(_code = "Duration::from_secs(15)")]
    pub peer_age_replaceable: Duration,
    #[default(_code = "0.125")]
    pub peer_replacement_probability: f64,
    #[default(_code = "Duration::ZERO..=Duration::from_secs_f64(0.1)")]
    pub peer_moratorium_range: RangeInclusive<Duration>,

    #[default(_code = "16")]
    pub dedup_capacity: usize,
    #[default(_code = "Duration::from_secs_f64(0.5)")]
    pub dedup_timeout: Duration,
}

pub struct Node<'a> {
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

    /// Shared components.
    network: Rc<RefCell<dyn Transmit + 'a>>,
    rng: Rc<RefCell<dyn Rng>>,

    cfg: NodeConfig,
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
pub enum CrdtMergeOutcome {
    Consensus,
    LocalWin,
    LocalLoss,
}

impl<'a> Node<'a> {
    /// Creates an empty node with no topics.
    pub fn new(
        id: u16,
        network: Rc<RefCell<dyn Transmit + 'a>>,
        rng: Rc<RefCell<dyn Rng>>,
        cfg: NodeConfig,
    ) -> Result<Self, String> {
        if !is_prime_u16(cfg.subject_id_modulus) {
            return Err(format!("subject_id_modulus must be prime, got {}", cfg.subject_id_modulus));
        }
        Ok(Self {
            id,
            topics_by_hash: BTreeMap::new(),
            peers: Vec::new(),
            peer_moratorium_until: Duration::ZERO,
            gossip_at: Duration::ZERO,
            gossip_counter: 0,
            gossip_dedup: Vec::new(),
            network,
            rng,
            cfg,
        })
    }

    pub fn id(&self) -> u16 {
        self.id
    }

    pub fn topics(&self) -> Vec<&Topic> {
        self.topics_by_hash.values().collect()
    }

    pub fn peer_ids(&self) -> Vec<u16> {
        self.peers.iter().map(|peer| peer.remote_id).collect()
    }

    pub fn subject_id_modulus(&self) -> u16 {
        self.cfg.subject_id_modulus
    }

    /// If the topic already exists, does nothing.
    pub fn add_topic(&mut self, topic_hash: u64) {
        let mut moving = self.topics_by_hash.remove(&topic_hash).unwrap_or(Topic::new(topic_hash, Duration::ZERO));
        loop {
            let subject_id = moving.subject_id(self.cfg.subject_id_modulus);
            let collided_hash = self.topics_by_hash.iter().find_map(|(hash, topic)| {
                if topic.subject_id(self.cfg.subject_id_modulus) == subject_id { Some(*hash) } else { None }
            });
            match collided_hash {
                Some(hash) => {
                    let displaced =
                        self.topics_by_hash.remove(&hash).expect("collision peer disappeared during local allocation");
                    if left_wins_collision(&moving, Duration::ZERO, displaced.lage(Duration::ZERO), displaced.hash()) {
                        self.topics_by_hash.insert(moving.hash(), moving);
                        moving = displaced;
                        moving.evict();
                    } else {
                        moving.evict();
                        self.topics_by_hash.insert(displaced.hash(), displaced);
                    }
                }
                None => {
                    self.topics_by_hash.insert(moving.hash(), moving);
                    break;
                }
            }
        }
        assert_eq!(0, self.count_local_collisions(), "local allocation incorrect");
    }

    pub fn count_local_collisions(&self) -> usize {
        count_colliding_subjects(self.topics_by_hash.values(), self.cfg.subject_id_modulus)
    }

    pub fn next_update_at(&self) -> Duration {
        self.gossip_at
    }

    pub fn step(&mut self, _now: Duration, _incoming: Vec<GossipMessage>) {
        todo!("simulation step is not implemented yet")
    }
}

pub fn count_colliding_subjects<'a, I>(topics: I, subject_id_modulus: u16) -> usize
where
    I: IntoIterator<Item = &'a Topic>,
{
    let mut by_subject: BTreeMap<u16, BTreeSet<u64>> = BTreeMap::new();
    for topic in topics {
        by_subject.entry(topic.subject_id(subject_id_modulus)).or_default().insert(topic.hash());
    }
    by_subject.values().filter(|hashes| hashes.len() > 1).count()
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    struct StubNetwork;

    impl Transmit for StubNetwork {
        fn unicast_gossip(&mut self, _destination: u16, _message: GossipMessage) {}
        fn broadcast_gossip(&mut self, _message: GossipMessage) {}
    }

    #[test]
    fn add_topic_resolves_local_collision_cascade() {
        let cfg = NodeConfig { subject_id_modulus: 11, ..NodeConfig::default() };
        let network = Rc::new(RefCell::new(StubNetwork));
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0)));
        let mut node = Node::new(0, network, rng, cfg).unwrap();
        node.add_topic(2);
        node.add_topic(12);
        node.add_topic(1);

        let subjects = node
            .topics_by_hash
            .values()
            .map(|topic| (topic.hash(), topic.subject_id(11), topic.evictions()))
            .collect::<Vec<_>>();
        assert_eq!(0, node.count_local_collisions());
        assert!(subjects.contains(&(1, 1, 0)));
        assert!(subjects.contains(&(2, 2, 0)));
        assert!(subjects.contains(&(12, 5, 2)));
    }
}
