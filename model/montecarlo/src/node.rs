use crate::message::{GossipMessage, gossip_dedup_hash};
use crate::network::Transmit;
use crate::topic::{Topic, left_wins_collision, topic_subject_id};
use rand::{Rng, RngExt};
use smart_default::SmartDefault;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;
use std::rc::Rc;
use time::Duration;

#[derive(Debug, Clone, SmartDefault)]
pub struct NodeConfig {
    #[default(_code = "1999")]
    pub subject_id_modulus: u16,

    #[default(_code = "Duration::seconds_f64(1.0)")]
    pub gossip_period: Duration,
    #[default(_code = "Duration::seconds_f64(0.125)")]
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
    #[default(_code = "Duration::seconds(30)")]
    pub peer_age_reachable: Duration,
    #[default(_code = "Duration::seconds(15)")]
    pub peer_age_replaceable: Duration,
    #[default(_code = "0.125")]
    pub peer_replacement_probability: f64,
    #[default(_code = "Duration::ZERO..=Duration::seconds_f64(0.1)")]
    pub peer_moratorium_range: RangeInclusive<Duration>,

    #[default(_code = "16")]
    pub dedup_capacity: usize,
    #[default(_code = "Duration::seconds_f64(0.5)")]
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

    fn sample_duration_between(&mut self, low: Duration, high: Duration) -> Duration {
        if low >= high {
            return low;
        }
        let sampled_seconds = self.rng.borrow_mut().random_range(low.as_seconds_f64()..=high.as_seconds_f64());
        Duration::seconds_f64(sampled_seconds)
    }

    fn schedule_next_periodic(&mut self, now: Duration) {
        let interval_low = if self.cfg.gossip_period > self.cfg.gossip_dither {
            self.cfg.gossip_period - self.cfg.gossip_dither
        } else {
            Duration::ZERO
        };
        let interval_high = self.cfg.gossip_period + self.cfg.gossip_dither;
        self.gossip_at = now + self.sample_duration_between(interval_low, interval_high);
    }

    fn sample_peer_moratorium(&mut self) -> Duration {
        self.sample_duration_between(*self.cfg.peer_moratorium_range.start(), *self.cfg.peer_moratorium_range.end())
    }

    fn is_peer_reachable(&self, now: Duration, peer: &PeerEntry) -> bool {
        (now - peer.last_seen) <= self.cfg.peer_age_reachable
    }

    fn update_peer_sample(&mut self, now: Duration, remote_id: u16) {
        if (remote_id == self.id) || (self.cfg.peer_count == 0) {
            return;
        }
        if let Some(peer) = self.peers.iter_mut().find(|peer| peer.remote_id == remote_id) {
            peer.last_seen = now;
            return;
        }
        if self.peers.len() < self.cfg.peer_count {
            self.peers.push(PeerEntry { remote_id, last_seen: now });
            return;
        }
        let oldest_index = self
            .peers
            .iter()
            .enumerate()
            .min_by_key(|(_, peer)| peer.last_seen)
            .map(|(index, _)| index)
            .expect("peer set cannot be empty when selecting the oldest");
        let oldest_age = now - self.peers[oldest_index].last_seen;
        let replacement_index = if oldest_age > self.cfg.peer_age_replaceable {
            Some(oldest_index)
        } else if (now >= self.peer_moratorium_until)
            && self.rng.borrow_mut().random_bool(self.cfg.peer_replacement_probability)
        {
            Some(self.rng.borrow_mut().random_range(0..self.peers.len()))
        } else {
            None
        };
        if let Some(index) = replacement_index {
            self.peers[index] = PeerEntry { remote_id, last_seen: now };
            self.peer_moratorium_until = now + self.sample_peer_moratorium();
        }
    }

    fn sample_peer_targets(&mut self, now: Duration, outdegree: u8, blacklist: &[u16]) -> Vec<u16> {
        if outdegree == 0 {
            return Vec::new();
        }
        let mut eligible = self
            .peers
            .iter()
            .filter_map(|peer| {
                let blocked = blacklist.iter().any(|peer_id| *peer_id == peer.remote_id);
                if !blocked && self.is_peer_reachable(now, peer) { Some(peer.remote_id) } else { None }
            })
            .collect::<Vec<_>>();
        let mut targets = Vec::new();
        while (targets.len() < outdegree as usize) && !eligible.is_empty() {
            let index = self.rng.borrow_mut().random_range(0..eligible.len());
            targets.push(eligible.swap_remove(index));
        }
        targets
    }

    fn send_epidemic_topic(
        &mut self,
        now: Duration,
        hash: u64,
        evictions: u16,
        lage: i8,
        ttl: u8,
        outdegree: u8,
        blacklist: &[u16],
    ) -> bool {
        let targets = self.sample_peer_targets(now, outdegree, blacklist);
        if targets.is_empty() {
            return false;
        }
        let mut network = self.network.borrow_mut();
        for destination in targets {
            network.unicast_gossip(destination, GossipMessage::new(self.id, ttl, outdegree, hash, evictions, lage));
        }
        true
    }

    fn touch_dedup_hash(&mut self, now: Duration, hash: u64) {
        if self.cfg.dedup_capacity == 0 {
            return;
        }
        if let Some(entry) = self.gossip_dedup.iter_mut().find(|entry| entry.hash == hash) {
            entry.last_seen = now;
            return;
        }
        if self.gossip_dedup.len() < self.cfg.dedup_capacity {
            self.gossip_dedup.push(GossipDedupEntry { hash, last_seen: now });
            return;
        }
        let oldest_index = self
            .gossip_dedup
            .iter()
            .enumerate()
            .min_by_key(|(_, entry)| entry.last_seen)
            .map(|(index, _)| index)
            .expect("dedup cache cannot be empty when replacing LRU entry");
        self.gossip_dedup[oldest_index] = GossipDedupEntry { hash, last_seen: now };
    }

    fn touch_dedup(&mut self, now: Duration, hash: u64, evictions: u16, lage: i8) {
        self.touch_dedup_hash(now, gossip_dedup_hash(hash, evictions, lage));
    }

    fn dedup_should_forward(&mut self, now: Duration, hash: u64, ttl: u8) -> bool {
        if self.cfg.dedup_capacity == 0 {
            return ttl > 0;
        }
        let stale_before = now - self.cfg.dedup_timeout;
        if let Some(entry) = self.gossip_dedup.iter_mut().find(|entry| entry.hash == hash) {
            let fresh = entry.last_seen < stale_before;
            entry.last_seen = now;
            return fresh && (ttl > 0);
        }
        self.touch_dedup_hash(now, hash);
        ttl > 0
    }

    fn find_topic_by_subject_id(&self, subject_id: u16) -> Option<u64> {
        self.topics_by_hash.iter().find_map(|(hash, topic)| {
            if topic.subject_id(self.cfg.subject_id_modulus) == subject_id { Some(*hash) } else { None }
        })
    }

    fn allocate_topic(&mut self, topic_hash: u64, new_evictions: u16, now: Duration, urgent: &mut BTreeSet<u64>) {
        let mut moving = self.topics_by_hash.remove(&topic_hash).expect("missing topic for local reallocation");
        moving.set_evictions(new_evictions);
        loop {
            let subject_id = moving.subject_id(self.cfg.subject_id_modulus);
            let collided_hash = self.find_topic_by_subject_id(subject_id);
            match collided_hash {
                Some(hash) => {
                    let displaced =
                        self.topics_by_hash.remove(&hash).expect("collision peer disappeared during local allocation");
                    if left_wins_collision(&moving, now, displaced.lage(now), displaced.hash()) {
                        let hash = moving.hash();
                        self.topics_by_hash.insert(hash, moving);
                        urgent.insert(hash);
                        moving = displaced;
                        moving.evict();
                    } else {
                        moving.evict();
                        self.topics_by_hash.insert(displaced.hash(), displaced);
                    }
                }
                None => {
                    let hash = moving.hash();
                    self.topics_by_hash.insert(hash, moving);
                    urgent.insert(hash);
                    break;
                }
            }
        }
        assert_eq!(0, self.count_local_collisions(), "local allocation incorrect");
    }

    fn on_gossip_known_topic(
        &mut self,
        now: Duration,
        hash: u64,
        evictions: u16,
        lage: i8,
        urgent: &mut BTreeSet<u64>,
    ) -> CrdtMergeOutcome {
        let (local_evictions, local_lage) = {
            let topic = self.topics_by_hash.get(&hash).expect("known topic missing from local state");
            (topic.evictions(), topic.lage(now))
        };
        let outcome = if local_evictions != evictions {
            if (local_lage > lage) || ((local_lage == lage) && (local_evictions > evictions)) {
                urgent.insert(hash);
                CrdtMergeOutcome::LocalWin
            } else {
                self.topics_by_hash
                    .get_mut(&hash)
                    .expect("known topic disappeared while merging gossip")
                    .merge_lage(lage, now);
                self.allocate_topic(hash, evictions, now, urgent);
                CrdtMergeOutcome::LocalLoss
            }
        } else {
            CrdtMergeOutcome::Consensus
        };
        self.topics_by_hash
            .get_mut(&hash)
            .expect("known topic disappeared while finalizing merge")
            .merge_lage(lage, now);
        outcome
    }

    fn on_gossip_unknown_topic(
        &mut self,
        now: Duration,
        hash: u64,
        evictions: u16,
        lage: i8,
        urgent: &mut BTreeSet<u64>,
    ) -> CrdtMergeOutcome {
        let subject_id = topic_subject_id(hash, evictions, self.cfg.subject_id_modulus);
        let Some(local_hash) = self.find_topic_by_subject_id(subject_id) else {
            return CrdtMergeOutcome::Consensus;
        };
        let (local_win, local_evictions) = {
            let local =
                self.topics_by_hash.get(&local_hash).expect("colliding local topic disappeared while merging gossip");
            (left_wins_collision(local, now, lage, hash), local.evictions())
        };
        if local_win {
            urgent.insert(local_hash);
            CrdtMergeOutcome::LocalWin
        } else {
            self.allocate_topic(local_hash, local_evictions.checked_add(1).expect("too many evictions"), now, urgent);
            CrdtMergeOutcome::LocalLoss
        }
    }

    fn forward_received_gossip(
        &mut self,
        now: Duration,
        original: &GossipMessage,
        hash: u64,
        evictions: u16,
        lage: i8,
    ) {
        if original.ttl() == 0 {
            return;
        }
        let ttl = original.ttl() - 1;
        let blacklist = [original.sender_id()];
        let _ = self.send_epidemic_topic(now, hash, evictions, lage, ttl, original.outdegree(), &blacklist);
    }

    fn emit_urgent_gossip(&mut self, now: Duration, topics: &BTreeSet<u64>) {
        for hash in topics {
            let Some(topic) = self.topics_by_hash.get(hash) else {
                continue;
            };
            let evictions = topic.evictions();
            let lage = topic.lage(now);
            let sent = self.send_epidemic_topic(
                now,
                *hash,
                evictions,
                lage,
                self.cfg.gossip_ttl_urgent,
                self.cfg.gossip_outdegree_urgent,
                &[],
            );
            if sent {
                self.touch_dedup(now, *hash, evictions, lage);
            }
        }
    }

    fn periodic_should_broadcast(&self, now: Duration) -> bool {
        if self.peers.len() < self.cfg.peer_count {
            return true;
        }
        if self.peers.iter().any(|peer| !self.is_peer_reachable(now, peer)) {
            return true;
        }
        if self.cfg.gossip_broadcast_every == 0 {
            return false;
        }
        (self.gossip_counter % (self.cfg.gossip_broadcast_every as u64)) == 0
    }

    fn emit_periodic_gossip(&mut self, now: Duration) {
        if self.topics_by_hash.is_empty() {
            return;
        }
        self.gossip_counter = self.gossip_counter.wrapping_add(1);
        let hashes = self.topics_by_hash.keys().copied().collect::<Vec<_>>();
        let index = self.rng.borrow_mut().random_range(0..hashes.len());
        let hash = hashes[index];
        let topic = self.topics_by_hash.get(&hash).expect("selected topic disappeared during periodic gossip");
        let evictions = topic.evictions();
        let lage = topic.lage(now);
        if self.periodic_should_broadcast(now) {
            self.network.borrow_mut().broadcast_gossip(GossipMessage::new(self.id, 0, 0, hash, evictions, lage));
            self.touch_dedup(now, hash, evictions, lage);
        } else if self.send_epidemic_topic(
            now,
            hash,
            evictions,
            lage,
            self.cfg.gossip_ttl_periodic,
            self.cfg.gossip_outdegree_periodic,
            &[],
        ) {
            self.touch_dedup(now, hash, evictions, lage);
        }
    }

    pub fn step(&mut self, now: Duration, incoming: Vec<GossipMessage>) {
        let mut urgent_topics = BTreeSet::<u64>::new();
        for message in incoming {
            self.update_peer_sample(now, message.sender_id());
            let should_forward = self.dedup_should_forward(now, message.dedup_hash(), message.ttl());
            if self.topics_by_hash.contains_key(&message.topic_hash()) {
                let outcome = self.on_gossip_known_topic(
                    now,
                    message.topic_hash(),
                    message.topic_evictions(),
                    message.topic_lage(),
                    &mut urgent_topics,
                );
                if should_forward && matches!(outcome, CrdtMergeOutcome::Consensus) {
                    let (evictions, lage) = {
                        let topic = self.topics_by_hash.get(&message.topic_hash()).expect("topic lost after merge");
                        (topic.evictions(), topic.lage(now))
                    };
                    self.forward_received_gossip(now, &message, message.topic_hash(), evictions, lage);
                }
            } else {
                let outcome = self.on_gossip_unknown_topic(
                    now,
                    message.topic_hash(),
                    message.topic_evictions(),
                    message.topic_lage(),
                    &mut urgent_topics,
                );
                if should_forward && matches!(outcome, CrdtMergeOutcome::Consensus | CrdtMergeOutcome::LocalLoss) {
                    self.forward_received_gossip(
                        now,
                        &message,
                        message.topic_hash(),
                        message.topic_evictions(),
                        message.topic_lage(),
                    );
                }
            }
        }
        self.emit_urgent_gossip(now, &urgent_topics);
        if now >= self.gossip_at {
            self.emit_periodic_gossip(now);
            self.schedule_next_periodic(now);
        }
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
    use rand::RngExt;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    struct StubNetwork;

    impl Transmit for StubNetwork {
        fn unicast_gossip(&mut self, _destination: u16, _message: GossipMessage) {}
        fn broadcast_gossip(&mut self, _message: GossipMessage) {}
    }

    #[derive(Default)]
    struct TxLog {
        unicasts: Vec<(u16, GossipMessage)>,
        broadcasts: Vec<GossipMessage>,
    }

    struct RecordingNetwork {
        log: Rc<RefCell<TxLog>>,
    }

    impl Transmit for RecordingNetwork {
        fn unicast_gossip(&mut self, destination: u16, message: GossipMessage) {
            self.log.borrow_mut().unicasts.push((destination, message));
        }

        fn broadcast_gossip(&mut self, message: GossipMessage) {
            self.log.borrow_mut().broadcasts.push(message);
        }
    }

    fn make_test_node(modulus: u16) -> Node<'static> {
        let cfg = NodeConfig { subject_id_modulus: modulus, ..NodeConfig::default() };
        let network = Rc::new(RefCell::new(StubNetwork));
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0xD00D_F00D)));
        Node::new(0, network, rng, cfg).unwrap()
    }

    fn snapshot(node: &Node<'_>, modulus: u16) -> Vec<(u64, u16, u16)> {
        node.topics_by_hash.values().map(|topic| (topic.hash(), topic.subject_id(modulus), topic.evictions())).collect()
    }

    fn make_recording_node(cfg: NodeConfig) -> (Node<'static>, Rc<RefCell<TxLog>>) {
        let log = Rc::new(RefCell::new(TxLog::default()));
        let network: Rc<RefCell<dyn Transmit>> = Rc::new(RefCell::new(RecordingNetwork { log: log.clone() }));
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0xBAD5_EED0)));
        (Node::new(0, network, rng, cfg).unwrap(), log)
    }

    fn make_message(sender: u16, ttl: u8, outdegree: u8, hash: u64, evictions: u16, lage: i8) -> GossipMessage {
        GossipMessage::new(sender, ttl, outdegree, hash, evictions, lage)
    }

    #[test]
    fn new_rejects_non_prime_modulus() {
        let cfg = NodeConfig { subject_id_modulus: 12, ..NodeConfig::default() };
        let network = Rc::new(RefCell::new(StubNetwork));
        let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0)));
        assert!(Node::new(0, network, rng, cfg).is_err());
    }

    #[test]
    fn add_topic_inserts_without_collision() {
        let mut node = make_test_node(11);
        node.add_topic(2);
        assert_eq!(vec![(2, 2, 0)], snapshot(&node, 11));
        assert_eq!(0, node.count_local_collisions());
    }

    #[test]
    fn add_topic_collision_moving_topic_loses() {
        let mut node = make_test_node(11);
        node.add_topic(1);
        node.add_topic(12); // Same subject as 1, higher hash loses and is evicted.

        let subjects = snapshot(&node, 11);
        assert_eq!(0, node.count_local_collisions());
        assert!(subjects.contains(&(1, 1, 0)));
        assert!(subjects.contains(&(12, 2, 1)));
    }

    #[test]
    fn add_topic_collision_moving_topic_wins_and_displaces_existing() {
        let mut node = make_test_node(11);
        node.add_topic(12);
        node.add_topic(1); // Same subject as 12, lower hash wins.

        let subjects = snapshot(&node, 11);
        assert_eq!(0, node.count_local_collisions());
        assert!(subjects.contains(&(1, 1, 0)));
        assert!(subjects.contains(&(12, 2, 1)));
    }

    #[test]
    fn add_topic_resolves_local_collision_cascade() {
        let mut node = make_test_node(11);
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

    #[test]
    fn add_topic_existing_hash_is_noop() {
        let mut node = make_test_node(11);
        node.add_topic(2);
        node.add_topic(12);
        node.add_topic(1);
        let before = snapshot(&node, 11);

        node.add_topic(2);
        let after = snapshot(&node, 11);

        assert_eq!(before, after);
        assert_eq!(0, node.count_local_collisions());
    }

    #[test]
    fn add_topic_randomized_stress_preserves_invariants() {
        const MODULUS: u16 = 101;
        const TOPIC_SPACE: u64 = 40;
        const OPS: usize = 1000;

        let mut op_rng = SmallRng::seed_from_u64(0x1BAD_5EED);
        let mut sequence = Vec::with_capacity(OPS);
        for _ in 0..OPS {
            sequence.push(op_rng.random::<u64>() % TOPIC_SPACE);
        }

        let mut node_a = make_test_node(MODULUS);
        let mut expected_hashes = BTreeSet::<u64>::new();
        for &hash in &sequence {
            node_a.add_topic(hash);
            expected_hashes.insert(hash);

            let actual_hashes = node_a.topics().into_iter().map(|topic| topic.hash()).collect::<BTreeSet<u64>>();
            assert_eq!(expected_hashes, actual_hashes);
            assert_eq!(0, node_a.count_local_collisions());
        }

        let mut node_b = make_test_node(MODULUS);
        for &hash in &sequence {
            node_b.add_topic(hash);
        }
        assert_eq!(snapshot(&node_a, MODULUS), snapshot(&node_b, MODULUS));
    }

    #[test]
    fn gossip_known_topic_local_win_sends_urgent_without_forwarding() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            gossip_ttl_urgent: 9,
            gossip_outdegree_urgent: 1,
            ..NodeConfig::default()
        };
        let (mut node, log) = make_recording_node(cfg);
        node.add_topic(1);
        node.gossip_at = Duration::MAX;

        node.step(Duration::seconds(8), vec![make_message(42, 3, 2, 1, 1, 2)]);

        let log = log.borrow();
        assert!(log.broadcasts.is_empty());
        assert_eq!(1, log.unicasts.len());
        assert_eq!(42, log.unicasts[0].0);
        let message = &log.unicasts[0].1;
        assert_eq!(9, message.ttl());
        assert_eq!(1, message.outdegree());
        assert_eq!(1, message.topic_hash());
        assert_eq!(0, message.topic_evictions());
    }

    #[test]
    fn gossip_known_topic_local_loss_updates_local_and_sends_urgent() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            gossip_ttl_urgent: 9,
            gossip_outdegree_urgent: 1,
            ..NodeConfig::default()
        };
        let (mut node, log) = make_recording_node(cfg);
        node.add_topic(1);
        node.gossip_at = Duration::MAX;

        node.step(Duration::seconds(2), vec![make_message(7, 2, 1, 1, 4, 3)]);

        let topic = node.topics_by_hash.get(&1).expect("topic must survive divergence merge");
        assert_eq!(4, topic.evictions());
        let log = log.borrow();
        assert_eq!(1, log.unicasts.len());
        assert!(log.broadcasts.is_empty());
        let message = &log.unicasts[0].1;
        assert_eq!(9, message.ttl());
        assert_eq!(4, message.topic_evictions());
    }

    #[test]
    fn gossip_unknown_topic_local_loss_forwards_remote_message() {
        let cfg = NodeConfig { subject_id_modulus: 11, gossip_outdegree_urgent: 0, ..NodeConfig::default() };
        let (mut node, log) = make_recording_node(cfg);
        node.add_topic(2);
        node.gossip_at = Duration::MAX;
        node.peers = vec![
            PeerEntry { remote_id: 5, last_seen: Duration::seconds(1) },
            PeerEntry { remote_id: 7, last_seen: Duration::seconds(1) },
        ];

        node.step(Duration::seconds(1), vec![make_message(5, 3, 1, 1, 1, 3)]);

        let topic = node.topics_by_hash.get(&2).expect("topic should remain allocated after local loss");
        assert_eq!(1, topic.evictions());
        let log = log.borrow();
        assert!(log.broadcasts.is_empty());
        assert_eq!(1, log.unicasts.len());
        assert_eq!(7, log.unicasts[0].0);
        let message = &log.unicasts[0].1;
        assert_eq!(2, message.ttl());
        assert_eq!(1, message.outdegree());
        assert_eq!(1, message.topic_hash());
        assert_eq!(1, message.topic_evictions());
        assert_eq!(3, message.topic_lage());
    }

    #[test]
    fn gossip_dedup_suppresses_reforward_until_timeout() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            dedup_timeout: Duration::seconds(5),
            gossip_outdegree_urgent: 0,
            ..NodeConfig::default()
        };
        let (mut node, log) = make_recording_node(cfg);
        node.gossip_at = Duration::MAX;
        node.peers = vec![
            PeerEntry { remote_id: 5, last_seen: Duration::ZERO },
            PeerEntry { remote_id: 7, last_seen: Duration::ZERO },
        ];
        let message = make_message(5, 3, 1, 42, 0, -1);

        node.step(Duration::seconds(0), vec![message.clone()]);
        node.step(Duration::seconds(1), vec![message.clone()]);
        node.step(Duration::seconds(7), vec![message]);

        let log = log.borrow();
        assert_eq!(2, log.unicasts.len());
        assert!(log.unicasts.iter().all(|(destination, _)| *destination == 7));
    }

    #[test]
    fn forwarding_respects_message_outdegree_and_excludes_sender() {
        let cfg = NodeConfig { subject_id_modulus: 11, gossip_outdegree_urgent: 0, ..NodeConfig::default() };
        let (mut node, log) = make_recording_node(cfg);
        node.gossip_at = Duration::MAX;
        node.peers = vec![
            PeerEntry { remote_id: 1, last_seen: Duration::ZERO },
            PeerEntry { remote_id: 2, last_seen: Duration::ZERO },
            PeerEntry { remote_id: 3, last_seen: Duration::ZERO },
        ];

        node.step(Duration::seconds(1), vec![make_message(1, 4, 2, 99, 0, -1)]);

        let log = log.borrow();
        assert_eq!(2, log.unicasts.len());
        let destinations = log.unicasts.iter().map(|(destination, _)| *destination).collect::<BTreeSet<u16>>();
        assert_eq!(BTreeSet::from([2, 3]), destinations);
        for (_, message) in &log.unicasts {
            assert_eq!(3, message.ttl());
            assert_eq!(2, message.outdegree());
        }
    }

    #[test]
    fn stale_peer_is_replaced_even_during_moratorium() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            peer_count: 1,
            peer_age_replaceable: Duration::seconds(5),
            peer_replacement_probability: 0.0,
            gossip_outdegree_urgent: 0,
            ..NodeConfig::default()
        };
        let (mut node, _) = make_recording_node(cfg);
        node.gossip_at = Duration::MAX;
        node.peers = vec![PeerEntry { remote_id: 1, last_seen: Duration::ZERO }];
        node.peer_moratorium_until = Duration::seconds(1000);

        node.step(Duration::seconds(10), vec![make_message(2, 0, 0, 12, 0, -1)]);
        assert_eq!(vec![2], node.peer_ids());
    }

    #[test]
    fn probabilistic_peer_replacement_is_gated_by_moratorium() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            peer_count: 1,
            peer_age_replaceable: Duration::seconds(100),
            peer_replacement_probability: 1.0,
            peer_moratorium_range: Duration::seconds(10)..=Duration::seconds(10),
            gossip_outdegree_urgent: 0,
            ..NodeConfig::default()
        };
        let (mut node, _) = make_recording_node(cfg);
        node.gossip_at = Duration::MAX;
        node.peers = vec![PeerEntry { remote_id: 1, last_seen: Duration::ZERO }];
        node.peer_moratorium_until = Duration::seconds(5);

        node.step(Duration::seconds(1), vec![make_message(2, 0, 0, 12, 0, -1)]);
        assert_eq!(vec![1], node.peer_ids());
        node.step(Duration::seconds(6), vec![make_message(2, 0, 0, 13, 0, -1)]);
        assert_eq!(vec![2], node.peer_ids());
        assert_eq!(Duration::seconds(16), node.peer_moratorium_until);
    }

    #[test]
    fn periodic_gossip_broadcasts_when_peer_set_is_incomplete() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            peer_count: 2,
            gossip_broadcast_every: 100,
            gossip_outdegree_urgent: 0,
            ..NodeConfig::default()
        };
        let (mut node, log) = make_recording_node(cfg);
        node.add_topic(1);
        node.gossip_at = Duration::ZERO;

        node.step(Duration::ZERO, Vec::new());

        let log = log.borrow();
        assert_eq!(1, log.broadcasts.len());
        assert!(log.unicasts.is_empty());
        assert_eq!(0, log.broadcasts[0].ttl());
        assert!(node.next_update_at() > Duration::ZERO);
    }

    #[test]
    fn periodic_gossip_uses_epidemic_when_peer_set_is_healthy() {
        let cfg = NodeConfig {
            subject_id_modulus: 11,
            peer_count: 1,
            gossip_broadcast_every: 10,
            gossip_ttl_periodic: 2,
            gossip_outdegree_periodic: 1,
            gossip_outdegree_urgent: 0,
            ..NodeConfig::default()
        };
        let (mut node, log) = make_recording_node(cfg);
        node.add_topic(1);
        node.peers = vec![PeerEntry { remote_id: 9, last_seen: Duration::ZERO }];
        node.gossip_at = Duration::ZERO;

        node.step(Duration::ZERO, Vec::new());

        let log = log.borrow();
        assert!(log.broadcasts.is_empty());
        assert_eq!(1, log.unicasts.len());
        assert_eq!(9, log.unicasts[0].0);
        assert_eq!(2, log.unicasts[0].1.ttl());
        assert_eq!(1, log.unicasts[0].1.outdegree());
    }
}
