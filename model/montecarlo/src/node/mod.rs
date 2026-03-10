mod gossip_dedup;
mod peer_sampler;

use self::gossip_dedup::{GossipDedup, GossipDedupConfig};
use self::peer_sampler::{PeerSampler, PeerSamplerConfig};
use crate::message::{GossipMessage, Transmit};
use crate::topic::{Topic, left_wins_collision, topic_subject_id};
use crate::util::is_prime;
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
    peer_sampler: PeerSampler,

    /// Gossips are sent at a fixed rate with dither (default period 1±0.125 s).
    /// Every nth gossip is broadcast, others are epidemic unicast; the gossip counter tracks that;
    /// as long as the peer set is not full or has at least one dead entry, every periodic gossip is broadcast.
    /// Urgent gossips have no schedule and are sent immediately when needed.
    gossip_at: Duration,
    gossip_counter: u64,
    gossip_dedup: GossipDedup,

    /// Shared components.
    network: Rc<RefCell<dyn Transmit + 'a>>,
    rng: Rc<RefCell<dyn Rng>>,
    now: Rc<dyn Fn() -> Duration + 'a>,

    cfg: NodeConfig,
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
        now: Rc<dyn Fn() -> Duration + 'a>,
        cfg: &NodeConfig,
    ) -> Result<Self, String> {
        if !is_prime(cfg.subject_id_modulus) {
            return Err(format!("subject_id_modulus must be prime, got {}", cfg.subject_id_modulus));
        }
        let peer_sampler_cfg = PeerSamplerConfig {
            self_id: id,
            peer_count: cfg.peer_count,
            peer_age_reachable: cfg.peer_age_reachable,
            peer_age_replaceable: cfg.peer_age_replaceable,
            peer_replacement_probability: cfg.peer_replacement_probability,
            peer_moratorium_range: cfg.peer_moratorium_range.clone(),
        };
        let gossip_dedup_cfg = GossipDedupConfig { capacity: cfg.dedup_capacity, timeout: cfg.dedup_timeout };
        Ok(Self {
            id,
            topics_by_hash: BTreeMap::new(),
            peer_sampler: PeerSampler::new(peer_sampler_cfg),
            gossip_at: Duration::ZERO,
            gossip_counter: 0,
            gossip_dedup: GossipDedup::new(gossip_dedup_cfg),
            network,
            rng,
            now,
            cfg: cfg.clone(),
        })
    }

    pub fn id(&self) -> u16 {
        self.id
    }

    pub fn topics(&self) -> Vec<&Topic> {
        self.topics_by_hash.values().collect()
    }

    pub fn peer_ids(&self) -> Vec<u16> {
        self.peer_sampler.peer_ids()
    }

    pub fn subject_id_modulus(&self) -> u16 {
        self.cfg.subject_id_modulus
    }

    /// If the topic already exists, does nothing.
    pub fn add_topic(&mut self, topic_hash: u64) {
        assert!(self.topics_by_hash.len() < (self.cfg.subject_id_modulus / 2) as usize);
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

    pub fn step(&mut self, incoming: Vec<GossipMessage>) {
        let now = self.now();
        let mut urgent_topics = BTreeSet::<u64>::new();
        for message in incoming {
            self.observe_peer(now, message.sender_id());
            let should_forward = self.gossip_dedup.should_forward_hash(now, message.dedup_hash(), message.ttl());
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

    fn now(&self) -> Duration {
        (self.now)()
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

    fn observe_peer(&mut self, now: Duration, remote_id: u16) {
        let mut rng = self.rng.borrow_mut();
        self.peer_sampler.observe(now, remote_id, &mut *rng);
    }

    fn sample_peer_targets(&mut self, now: Duration, outdegree: u8, blacklist: &[u16]) -> Vec<u16> {
        let mut rng = self.rng.borrow_mut();
        self.peer_sampler.sample_targets(now, outdegree, blacklist, &mut *rng)
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

    fn touch_dedup(&mut self, now: Duration, hash: u64, evictions: u16, lage: i8) {
        self.gossip_dedup.touch_gossip(now, hash, evictions, lage);
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
        if self.peer_sampler.needs_broadcast_bootstrap(now) {
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

    #[cfg(test)]
    fn set_peers_for_test(&mut self, peers: Vec<(u16, Duration)>) {
        self.peer_sampler.set_peers_for_test(peers);
    }

    #[cfg(test)]
    fn set_peer_moratorium_until_for_test(&mut self, until: Duration) {
        self.peer_sampler.set_moratorium_until_for_test(until);
    }

    #[cfg(test)]
    fn peer_moratorium_until_for_test(&self) -> Duration {
        self.peer_sampler.moratorium_until_for_test()
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

#[cfg(test)]
mod tests;
