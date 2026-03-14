use crate::message::{GossipMessage, GossipScope, Transmit};
use crate::topic::{Topic, left_wins_collision, topic_subject_id};
use crate::util::is_prime;
use rand::{Rng, RngExt};
use smart_default::SmartDefault;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use time::Duration;

#[derive(Debug, Clone, SmartDefault)]
pub struct NodeConfig {
    #[default(_code = "122867")]
    pub subject_id_modulus: u32,

    /// Mean period between consecutive local sends of a topic (default 5 s = 0.2 Hz).
    #[default(_code = "Duration::seconds_f64(5.0)")]
    pub gossip_period: Duration,

    /// Dither around gossip_period, producing [period-dither, period+dither].
    #[default(_code = "Duration::seconds_f64(1.0)")]
    pub gossip_dither: Duration,

    /// Fraction of periodic topic gossips that are broadcast (default 10%).
    #[default(_code = "0.1")]
    pub gossip_broadcast_fraction: f64,

    #[default(_code = "Duration::seconds_f64(0.05)")]
    pub gossip_urgent_delay: Duration,
}

#[derive(Debug, Clone)]
pub enum CrdtMergeOutcome {
    Consensus,
    LocalWin,
    LocalLoss,
}

#[derive(Debug, Clone, Copy, Default)]
struct TopicScheduleState {
    next_gossip_at: Duration,
    periodic_emissions: u64,
    first_periodic_broadcast_pending: bool,
}

impl TopicScheduleState {
    fn new(next_gossip_at: Duration) -> Self {
        Self { next_gossip_at, periodic_emissions: 0, first_periodic_broadcast_pending: true }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UrgentScope {
    Shard,
    Broadcast,
}

#[derive(Debug, Clone, Copy)]
struct PendingUrgentGossip {
    deadline: Duration,
    scope: UrgentScope,
}

pub struct Node<'a> {
    id: u16,
    shard_count: u32,
    topics_by_hash: BTreeMap<u64, Topic>,
    topic_hash_by_subject_id: HashMap<u32, u64>,

    /// Local topics are scheduled independently by per-topic next-gossip timestamps.
    topic_schedule_by_hash: BTreeMap<u64, TopicScheduleState>,
    pending_urgent_by_hash: BTreeMap<u64, PendingUrgentGossip>,
    next_topic_update_at: Cell<Duration>,
    next_topic_update_at_stale: Cell<bool>,
    next_urgent_update_at: Cell<Duration>,
    next_urgent_update_at_stale: Cell<bool>,

    /// Shared components.
    network: Rc<RefCell<dyn Transmit + 'a>>,
    rng: Rc<RefCell<dyn Rng>>,
    now: Rc<dyn Fn() -> Duration + 'a>,

    cfg: NodeConfig,
}

impl<'a> Node<'a> {
    /// Creates an empty node with no topics.
    pub fn new(
        id: u16,
        shard_count: u32,
        network: Rc<RefCell<dyn Transmit + 'a>>,
        rng: Rc<RefCell<dyn Rng>>,
        now: Rc<dyn Fn() -> Duration + 'a>,
        cfg: &NodeConfig,
    ) -> Result<Self, String> {
        if !is_prime(cfg.subject_id_modulus) {
            return Err(format!("subject_id_modulus must be prime, got {}", cfg.subject_id_modulus));
        }
        if shard_count == 0 {
            return Err("shard_count must be positive".to_string());
        }
        Ok(Self {
            id,
            shard_count,
            topics_by_hash: BTreeMap::new(),
            topic_hash_by_subject_id: HashMap::new(),
            topic_schedule_by_hash: BTreeMap::new(),
            pending_urgent_by_hash: BTreeMap::new(),
            next_topic_update_at: Cell::new(Duration::MAX),
            next_topic_update_at_stale: Cell::new(false),
            next_urgent_update_at: Cell::new(Duration::MAX),
            next_urgent_update_at_stale: Cell::new(false),
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
        self.topics_iter().collect()
    }

    pub fn topics_iter(&self) -> impl Iterator<Item = &Topic> {
        self.topics_by_hash.values()
    }

    pub fn subject_id_modulus(&self) -> u32 {
        self.cfg.subject_id_modulus
    }

    pub fn shard_ids(&self) -> Vec<u32> {
        self.topics_by_hash
            .keys()
            .copied()
            .map(|hash| self.shard_for_topic(hash))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// If the topic already exists, does nothing.
    pub fn add_topic(&mut self, topic_hash: u64) {
        assert!(self.topics_by_hash.len() < (self.cfg.subject_id_modulus / 2) as usize);
        if self.topics_by_hash.contains_key(&topic_hash) {
            return;
        }
        let mut moving = Topic::new(topic_hash, Duration::ZERO);
        loop {
            let subject_id = moving.subject_id(self.cfg.subject_id_modulus);
            let collided_hash = self.find_topic_by_subject_id(subject_id);
            match collided_hash {
                Some(hash) => {
                    let displaced = self.remove_topic_by_hash(hash);
                    if left_wins_collision(&moving, Duration::ZERO, displaced.lage(Duration::ZERO), displaced.hash()) {
                        self.insert_topic(moving);
                        moving = displaced;
                        moving.evict();
                    } else {
                        moving.evict();
                        self.insert_topic(displaced);
                    }
                }
                None => {
                    self.insert_topic(moving);
                    break;
                }
            }
        }
        self.ensure_topic_schedule_entry(topic_hash);
        debug_assert_eq!(0, self.count_local_collisions(), "local allocation incorrect");
    }

    pub fn count_local_collisions(&self) -> usize {
        count_colliding_subjects(self.topics_by_hash.values(), self.cfg.subject_id_modulus)
    }

    pub fn next_update_at(&self) -> Duration {
        let next_topic = self.cached_next_topic_update_at();
        let next_urgent = self.cached_next_urgent_update_at();
        let next = std::cmp::min(next_topic, next_urgent);
        debug_assert_eq!(next, self.next_update_at_full_scan(), "cached next-update deadline diverged from full scan");
        next
    }

    pub fn step(&mut self, incoming: Vec<GossipMessage>) {
        let now = self.now();
        for message in incoming {
            self.process_gossip(now, message);
        }
        self.emit_due_urgent(now);
        self.emit_periodic_gossip(now);
    }

    fn process_gossip(&mut self, now: Duration, message: GossipMessage) {
        if self.topics_by_hash.contains_key(&message.topic_hash()) {
            self.on_gossip_known_topic(now, message.topic_hash(), message.topic_evictions(), message.topic_lage());
            self.schedule_after_heard(now, message.topic_hash());
            self.cancel_pending_urgent_if_up_to_date(now, message.topic_hash(), message.topic_evictions());
        } else {
            self.on_gossip_unknown_topic(now, message.topic_hash(), message.topic_evictions(), message.topic_lage());
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

    fn periodic_interval_bounds(&self) -> (Duration, Duration) {
        let low = if self.cfg.gossip_period > self.cfg.gossip_dither {
            self.cfg.gossip_period - self.cfg.gossip_dither
        } else {
            Duration::ZERO
        };
        let high = self.cfg.gossip_period + self.cfg.gossip_dither;
        (low, high)
    }

    fn heard_interval_bounds(&self) -> (Duration, Duration) {
        let (send_low, send_high) = self.periodic_interval_bounds();
        let low = Duration::seconds_f64(send_low.as_seconds_f64() * 2.0);
        let high = Duration::seconds_f64(send_high.as_seconds_f64() * 2.0);
        (low, high)
    }

    fn startup_interval_bounds(&self) -> (Duration, Duration) {
        (Duration::ZERO, self.cfg.gossip_period)
    }

    fn cached_next_topic_update_at(&self) -> Duration {
        if self.next_topic_update_at_stale.get() {
            let next =
                self.topic_schedule_by_hash.values().map(|state| state.next_gossip_at).min().unwrap_or(Duration::MAX);
            self.next_topic_update_at.set(next);
            self.next_topic_update_at_stale.set(false);
        }
        self.next_topic_update_at.get()
    }

    fn cached_next_urgent_update_at(&self) -> Duration {
        if self.next_urgent_update_at_stale.get() {
            let next = self.pending_urgent_by_hash.values().map(|entry| entry.deadline).min().unwrap_or(Duration::MAX);
            self.next_urgent_update_at.set(next);
            self.next_urgent_update_at_stale.set(false);
        }
        self.next_urgent_update_at.get()
    }

    fn next_update_at_full_scan(&self) -> Duration {
        let next_topic =
            self.topic_schedule_by_hash.values().map(|state| state.next_gossip_at).min().unwrap_or(Duration::MAX);
        let next_urgent =
            self.pending_urgent_by_hash.values().map(|entry| entry.deadline).min().unwrap_or(Duration::MAX);
        std::cmp::min(next_topic, next_urgent)
    }

    fn reconcile_topic_deadline_change(&self, previous: Duration, updated: Duration) {
        if self.next_topic_update_at_stale.get() {
            return;
        }
        let cached = self.next_topic_update_at.get();
        if updated < cached {
            self.next_topic_update_at.set(updated);
            return;
        }
        if (previous == cached) && (updated > cached) {
            self.next_topic_update_at_stale.set(true);
        }
    }

    fn reconcile_topic_deadline_insert(&self, inserted: Duration) {
        if self.next_topic_update_at_stale.get() {
            return;
        }
        if inserted < self.next_topic_update_at.get() {
            self.next_topic_update_at.set(inserted);
        }
    }

    fn reconcile_urgent_deadline_change(&self, previous: Duration, updated: Duration) {
        if self.next_urgent_update_at_stale.get() {
            return;
        }
        let cached = self.next_urgent_update_at.get();
        if updated < cached {
            self.next_urgent_update_at.set(updated);
            return;
        }
        if (previous == cached) && (updated > cached) {
            self.next_urgent_update_at_stale.set(true);
        }
    }

    fn reconcile_urgent_deadline_insert(&self, inserted: Duration) {
        if self.next_urgent_update_at_stale.get() {
            return;
        }
        if inserted < self.next_urgent_update_at.get() {
            self.next_urgent_update_at.set(inserted);
        }
    }

    fn reconcile_urgent_deadline_removed(&self, removed: Duration) {
        if self.next_urgent_update_at_stale.get() {
            return;
        }
        if removed == self.next_urgent_update_at.get() {
            self.next_urgent_update_at_stale.set(true);
        }
    }

    fn schedule_after_send(&mut self, now: Duration, hash: u64) {
        let (low, high) = self.periodic_interval_bounds();
        let deadline = now + self.sample_duration_between(low, high);
        if let Some(state) = self.topic_schedule_by_hash.get_mut(&hash) {
            let previous = state.next_gossip_at;
            state.next_gossip_at = deadline;
            self.reconcile_topic_deadline_change(previous, deadline);
        }
    }

    fn schedule_after_heard(&mut self, now: Duration, hash: u64) {
        let (low, high) = self.heard_interval_bounds();
        let deadline = now + self.sample_duration_between(low, high);
        if let Some(state) = self.topic_schedule_by_hash.get_mut(&hash) {
            let previous = state.next_gossip_at;
            state.next_gossip_at = deadline;
            self.reconcile_topic_deadline_change(previous, deadline);
        }
    }

    fn ensure_topic_schedule_entry(&mut self, hash: u64) {
        if self.topic_schedule_by_hash.contains_key(&hash) {
            return;
        }
        let now = self.now();
        let (low, high) = self.startup_interval_bounds();
        // On topic creation, spread first-gossip opportunities over a wider window so duplicate suppression
        // can kick in before the entire network emits simultaneously.
        let next = now + self.sample_duration_between(low, high);
        self.topic_schedule_by_hash.insert(hash, TopicScheduleState::new(next));
        self.reconcile_topic_deadline_insert(next);
    }

    fn find_topic_by_subject_id(&self, subject_id: u32) -> Option<u64> {
        self.topic_hash_by_subject_id.get(&subject_id).copied()
    }

    fn shard_for_topic(&self, hash: u64) -> u32 {
        let offset = (hash % (self.shard_count as u64)) as u32;
        self.cfg.subject_id_modulus.checked_add(offset).expect("shard subject overflow")
    }

    fn should_broadcast_by_ratio(&self, periodic_emissions: u64) -> bool {
        let fraction = self.cfg.gossip_broadcast_fraction;
        if fraction <= 0.0 {
            return false;
        }
        if fraction >= 1.0 {
            return true;
        }
        let current = ((periodic_emissions as f64) * fraction).floor() as u64;
        let previous = (((periodic_emissions - 1) as f64) * fraction).floor() as u64;
        current > previous
    }

    fn choose_periodic_scope(&mut self, hash: u64) -> GossipScope {
        let (first_broadcast_pending, periodic_emissions) = {
            let state = self.topic_schedule_by_hash.get_mut(&hash).expect("missing topic schedule state");
            state.periodic_emissions = state.periodic_emissions.wrapping_add(1);
            let first = state.first_periodic_broadcast_pending;
            state.first_periodic_broadcast_pending = false;
            (first, state.periodic_emissions)
        };
        if first_broadcast_pending || self.should_broadcast_by_ratio(periodic_emissions) {
            GossipScope::Broadcast
        } else {
            GossipScope::Shard(self.shard_for_topic(hash))
        }
    }

    fn transmit_topic_gossip(&mut self, now: Duration, hash: u64, scope: GossipScope) {
        let Some(topic) = self.topics_by_hash.get(&hash) else {
            return;
        };
        let message = GossipMessage::new(self.id, scope, hash, topic.evictions(), topic.lage(now));
        self.network.borrow_mut().transmit_gossip(message);
        self.schedule_after_send(now, hash);
    }

    fn schedule_urgent(&mut self, now: Duration, hash: u64, scope: UrgentScope) {
        if !self.topics_by_hash.contains_key(&hash) {
            return;
        }
        let deadline = now + self.sample_duration_between(Duration::ZERO, self.cfg.gossip_urgent_delay);
        match self.pending_urgent_by_hash.get_mut(&hash) {
            Some(existing) => {
                let previous = existing.deadline;
                if deadline < existing.deadline {
                    existing.deadline = deadline;
                }
                if scope == UrgentScope::Broadcast {
                    existing.scope = UrgentScope::Broadcast;
                }
                let updated = existing.deadline;
                self.reconcile_urgent_deadline_change(previous, updated);
            }
            None => {
                self.pending_urgent_by_hash.insert(hash, PendingUrgentGossip { deadline, scope });
                self.reconcile_urgent_deadline_insert(deadline);
            }
        }
    }

    fn cancel_pending_urgent_if_up_to_date(&mut self, now: Duration, hash: u64, received_evictions: u16) {
        let Some(topic) = self.topics_by_hash.get(&hash) else {
            return;
        };
        if topic.evictions() != received_evictions {
            return;
        }
        let Some(pending) = self.pending_urgent_by_hash.get(&hash).copied() else {
            return;
        };
        if pending.deadline > now {
            self.pending_urgent_by_hash.remove(&hash);
            self.reconcile_urgent_deadline_removed(pending.deadline);
        }
    }

    fn emit_due_urgent(&mut self, now: Duration) {
        let due = self
            .pending_urgent_by_hash
            .iter()
            .filter(|(_, entry)| entry.deadline <= now)
            .map(|(hash, entry)| (*hash, *entry))
            .collect::<Vec<_>>();
        for (hash, entry) in due {
            self.pending_urgent_by_hash.remove(&hash);
            self.reconcile_urgent_deadline_removed(entry.deadline);
            let scope = match entry.scope {
                UrgentScope::Shard => GossipScope::Shard(self.shard_for_topic(hash)),
                UrgentScope::Broadcast => GossipScope::Broadcast,
            };
            self.transmit_topic_gossip(now, hash, scope);
        }
    }

    fn emit_periodic_gossip(&mut self, now: Duration) {
        let hash = self
            .topic_schedule_by_hash
            .iter()
            .filter(|(_, state)| state.next_gossip_at <= now)
            .min_by_key(|(hash, state)| (state.next_gossip_at, **hash))
            .map(|(hash, _)| *hash);
        let Some(hash) = hash else {
            return;
        };
        let scope = self.choose_periodic_scope(hash);
        self.transmit_topic_gossip(now, hash, scope);
    }

    fn allocate_topic(&mut self, topic_hash: u64, new_evictions: u16, now: Duration) -> u16 {
        let mut original_evictions_by_hash = BTreeMap::new();
        let mut moving = self.remove_topic_by_hash(topic_hash);
        let initial_evictions = moving.evictions();
        if initial_evictions != new_evictions {
            original_evictions_by_hash.insert(topic_hash, initial_evictions);
        }
        moving.set_evictions(new_evictions);
        loop {
            let subject_id = moving.subject_id(self.cfg.subject_id_modulus);
            let collided_hash = self.find_topic_by_subject_id(subject_id);
            match collided_hash {
                Some(hash) => {
                    let displaced = self.remove_topic_by_hash(hash);
                    if left_wins_collision(&moving, now, displaced.lage(now), displaced.hash()) {
                        self.insert_topic(moving);
                        moving = displaced;
                        original_evictions_by_hash.entry(moving.hash()).or_insert(moving.evictions());
                        moving.evict();
                    } else {
                        original_evictions_by_hash.entry(moving.hash()).or_insert(moving.evictions());
                        moving.evict();
                        self.insert_topic(displaced);
                    }
                }
                None => {
                    let final_evictions = moving.evictions();
                    self.insert_topic(moving);
                    for (changed_hash, original_evictions) in original_evictions_by_hash {
                        let updated_evictions = self.topics_by_hash.get(&changed_hash).expect("missing").evictions();
                        if updated_evictions != original_evictions {
                            // Subject-ID occupancy changed for this topic; reveal it network-wide.
                            // This will reveal collisions if any other topic is occupying the same subject-ID.
                            self.schedule_urgent(now, changed_hash, UrgentScope::Broadcast);
                        }
                    }
                    debug_assert_eq!(0, self.count_local_collisions(), "local allocation incorrect");
                    return final_evictions;
                }
            }
        }
    }

    fn on_gossip_known_topic(&mut self, now: Duration, hash: u64, evictions: u16, lage: i8) -> CrdtMergeOutcome {
        let (local_evictions, local_lage) = {
            let topic = self.topics_by_hash.get(&hash).expect("known topic missing from local state");
            (topic.evictions(), topic.lage(now))
        };
        let outcome = if local_evictions != evictions {
            if (local_lage > lage) || ((local_lage == lage) && (local_evictions > evictions)) {
                // The remote is obsolete, so we need to tell it to move. The subject-ID occupancy is not changing,
                // so there is no need to use broadcast scope, since no new collisions are expected.
                self.schedule_urgent(now, hash, UrgentScope::Shard);
                CrdtMergeOutcome::LocalWin
            } else {
                // The local replica is obsolete. If we can move exactly to the specified subject-ID (evictions),
                // then nothing needs to be gossiped because that state is already known to be occupied by this topic.
                // If that subject-ID is occupied locally and we can't displace that topic, allocation may bump one or
                // more eviction counters; allocate_topic() schedules urgent broadcast for all such changes.
                self.topics_by_hash.get_mut(&hash).expect("known topic disappeared").merge_lage(lage, now);
                self.allocate_topic(hash, evictions, now);
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

    fn on_gossip_unknown_topic(&mut self, now: Duration, hash: u64, evictions: u16, lage: i8) -> CrdtMergeOutcome {
        let subject_id = topic_subject_id(hash, evictions, self.cfg.subject_id_modulus);
        let Some(local_hash) = self.find_topic_by_subject_id(subject_id) else {
            return CrdtMergeOutcome::Consensus;
        };
        let (local_win, local_evictions) = {
            let local = self.topics_by_hash.get(&local_hash).expect("colliding local topic disappeared");
            (left_wins_collision(local, now, lage, hash), local.evictions())
        };
        if local_win {
            // The remote is occupying our subject-ID; we are not expected to be on its shard (we might be due to
            // a collision but it is unlikely), so we need to broadcast urgently to reach it and everyone else on
            // the infringing topic.
            self.schedule_urgent(now, local_hash, UrgentScope::Broadcast);
            CrdtMergeOutcome::LocalWin
        } else {
            let bumped = local_evictions.checked_add(1).expect("too many evictions");
            // We lost, so we need to move; allocate_topic() broadcasts occupancy changes.
            self.allocate_topic(local_hash, bumped, now);
            CrdtMergeOutcome::LocalLoss
        }
    }

    fn insert_topic(&mut self, topic: Topic) {
        let hash = topic.hash();
        let subject_id = topic.subject_id(self.cfg.subject_id_modulus);
        let previous_topic = self.topics_by_hash.insert(hash, topic);
        debug_assert!(previous_topic.is_none(), "insert_topic unexpectedly replaced an existing topic");
        let previous_hash = self.topic_hash_by_subject_id.insert(subject_id, hash);
        debug_assert!(previous_hash.is_none(), "insert_topic created a local subject-ID collision");
    }

    fn remove_topic_by_hash(&mut self, hash: u64) -> Topic {
        let topic = self.topics_by_hash.remove(&hash).expect("topic missing from hash index");
        let subject_id = topic.subject_id(self.cfg.subject_id_modulus);
        let removed = self.topic_hash_by_subject_id.remove(&subject_id);
        debug_assert_eq!(Some(hash), removed, "subject-ID index diverged from hash index");
        topic
    }
}

pub fn count_colliding_subjects<'a, I>(topics: I, subject_id_modulus: u32) -> usize
where
    I: IntoIterator<Item = &'a Topic>,
{
    let mut by_subject: BTreeMap<u32, BTreeSet<u64>> = BTreeMap::new();
    for topic in topics {
        by_subject.entry(topic.subject_id(subject_id_modulus)).or_default().insert(topic.hash());
    }
    by_subject.values().filter(|hashes| hashes.len() > 1).count()
}

#[cfg(test)]
mod tests;
