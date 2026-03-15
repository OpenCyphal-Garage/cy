use crate::message::{GossipMessage, GossipScope, Transmit};
use rand::{Rng, RngExt};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;
use std::rc::Rc;
use time::Duration;

const DELAY_QUANTIZATION_STEP: Duration = Duration::microseconds(10);

#[derive(Debug, Clone)]
pub(super) struct NetworkConfig {
    /// Assuming that nodes have contiguous IDs from 0 to node_count-1.
    pub node_count: usize,
    pub delay_range: RangeInclusive<Duration>,
    pub loss_probability: f64,
}

pub(super) struct Network {
    /// Messages that are currently in transit, indexed globally by delivery time.
    /// A tiebreaker is added in case we roll the same delivery time for distinct messages.
    /// Note that messages may be delivered out of order, depending on how the propagation delay is rolled.
    enroute: BTreeMap<(Duration, u64, u16), GossipMessage>,

    /// Current multicast shard subscriptions.
    node_shards: BTreeMap<u16, BTreeSet<u32>>,
    shard_subscribers: BTreeMap<u32, BTreeSet<u16>>,

    /// Shared states.
    now: Rc<dyn Fn() -> Duration + 'static>,
    rng: Rc<RefCell<dyn Rng>>,
    delivery_destinations: Vec<u16>,

    stats: NetworkStats,
    cfg: NetworkConfig,
}

impl Transmit for Network {
    fn transmit_gossip(&mut self, message: GossipMessage) {
        assert!((message.sender_id() as usize) < self.cfg.node_count);
        self.increment_sent_counter(message.sender_id(), message.scope());
        match message.scope() {
            GossipScope::Broadcast => {
                assert!(self.cfg.node_count <= u16::MAX as usize);
                for destination in 0..(self.cfg.node_count as u16) {
                    if destination != message.sender_id() {
                        self.enqueue_delivery(destination, message.clone());
                    }
                }
            }
            GossipScope::Shard(shard_id) => {
                self.delivery_destinations.clear();
                if let Some(subscribers) = self.shard_subscribers.get(&shard_id) {
                    self.delivery_destinations
                        .extend(subscribers.iter().copied().filter(|destination| *destination != message.sender_id()));
                }
                let mut destinations = std::mem::take(&mut self.delivery_destinations);
                for destination in destinations.iter().copied() {
                    if destination != message.sender_id() {
                        self.enqueue_delivery(destination, message.clone());
                    }
                }
                destinations.clear();
                self.delivery_destinations = destinations;
            }
        }
    }

    fn set_node_shards(&mut self, node_id: u16, shards: Vec<u32>) {
        assert!((node_id as usize) < self.cfg.node_count);

        if let Some(old) = self.node_shards.remove(&node_id) {
            for shard in old {
                if let Some(subscribers) = self.shard_subscribers.get_mut(&shard) {
                    subscribers.remove(&node_id);
                    if subscribers.is_empty() {
                        self.shard_subscribers.remove(&shard);
                    }
                }
            }
        }

        let set = shards.into_iter().collect::<BTreeSet<_>>();
        for shard in &set {
            self.shard_subscribers.entry(*shard).or_default().insert(node_id);
        }
        self.node_shards.insert(node_id, set);
    }
}

impl Network {
    pub(super) fn new(cfg: &NetworkConfig, now: Rc<dyn Fn() -> Duration + 'static>, rng: Rc<RefCell<dyn Rng>>) -> Self {
        Self {
            enroute: BTreeMap::new(),
            node_shards: BTreeMap::new(),
            shard_subscribers: BTreeMap::new(),
            now,
            rng,
            delivery_destinations: Vec::new(),
            stats: NetworkStats::default(),
            cfg: cfg.clone(),
        }
    }

    fn enqueue_delivery(&mut self, destination: u16, message: GossipMessage) {
        if self.rng.borrow_mut().random_bool(self.cfg.loss_probability) {
            self.stats.lost += 1;
            return;
        }
        let delay_start = *self.cfg.delay_range.start();
        let delay_end = *self.cfg.delay_range.end();
        let delay = if delay_start == delay_end {
            delay_start
        } else {
            let sampled_seconds =
                self.rng.borrow_mut().random_range(delay_start.as_seconds_f64()..=delay_end.as_seconds_f64());
            let sampled = Duration::seconds_f64(sampled_seconds);
            quantize_delay(sampled, DELAY_QUANTIZATION_STEP).clamp(delay_start, delay_end)
        };
        let delivery_time = (self.now)() + delay;
        let tiebreaker = self.rng.borrow_mut().next_u64();
        self.enroute.insert((delivery_time, tiebreaker, destination), message);
    }

    fn increment_sent_counter(&mut self, sender_id: u16, scope: GossipScope) {
        match scope {
            GossipScope::Broadcast => {
                self.stats.broadcast_sent_per_node.entry(sender_id).and_modify(|c| *c += 1).or_insert(1);
            }
            GossipScope::Shard(_) => {
                self.stats.shard_sent_per_node.entry(sender_id).and_modify(|c| *c += 1).or_insert(1);
            }
        }
    }

    fn increment_received_counter(&mut self, destination: u16, scope: GossipScope) {
        match scope {
            GossipScope::Broadcast => {
                self.stats.broadcast_received_per_node.entry(destination).and_modify(|c| *c += 1).or_insert(1);
            }
            GossipScope::Shard(_) => {
                self.stats.shard_received_per_node.entry(destination).and_modify(|c| *c += 1).or_insert(1);
            }
        }
    }

    /// Drains all messages that are due by the specified time, grouped by destination.
    pub fn drain_due(&mut self, now: Duration) -> Vec<(u16, Vec<GossipMessage>)> {
        let mut by_destination: BTreeMap<u16, Vec<GossipMessage>> = BTreeMap::new();
        while let Some((&(delivery_time, tie, destination), _)) = self.enroute.iter().next() {
            if delivery_time > now {
                break;
            }
            let message = self
                .enroute
                .remove(&(delivery_time, tie, destination))
                .expect("enroute message disappeared while draining arrivals");
            self.increment_received_counter(destination, message.scope());
            by_destination.entry(destination).or_default().push(message);
        }
        by_destination.into_iter().collect()
    }

    pub fn soonest_arrival_at(&self) -> Option<Duration> {
        self.enroute.keys().next().map(|&(time, _, _)| time)
    }

    pub fn config(&self) -> &NetworkConfig {
        &self.cfg
    }

    pub fn stats(&self) -> NetworkStats {
        self.stats.clone()
    }
}

/// Propagation statistics for debugging and analysis.
#[derive(Debug, Clone, Default)]
pub(super) struct NetworkStats {
    // Transmit counters are per gossip emission (one multicast send), not per destination.
    pub broadcast_sent_per_node: BTreeMap<u16, u64>,
    pub shard_sent_per_node: BTreeMap<u16, u64>,
    // Receive and loss counters are per destination delivery copy.
    pub broadcast_received_per_node: BTreeMap<u16, u64>,
    pub shard_received_per_node: BTreeMap<u16, u64>,
    pub lost: u64,
}

impl NetworkStats {
    pub fn broadcast_sent_total(&self) -> u64 {
        self.broadcast_sent_per_node.values().sum()
    }

    pub fn shard_sent_total(&self) -> u64 {
        self.shard_sent_per_node.values().sum()
    }

    pub fn sent_total(&self) -> u64 {
        self.broadcast_sent_total() + self.shard_sent_total()
    }

    pub fn broadcast_received_total(&self) -> u64 {
        self.broadcast_received_per_node.values().sum()
    }

    pub fn shard_received_total(&self) -> u64 {
        self.shard_received_per_node.values().sum()
    }

    pub fn received_total(&self) -> u64 {
        self.broadcast_received_total() + self.shard_received_total()
    }
}

fn quantize_delay(delay: Duration, quantum: Duration) -> Duration {
    let q_us = quantum.whole_microseconds();
    if q_us <= 0 {
        return delay;
    }
    let delay_us = delay.whole_microseconds();
    let rounded_us = ((delay_us + (q_us / 2)) / q_us) * q_us;
    Duration::microseconds(i64::try_from(rounded_us).unwrap_or(i64::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    fn make_test_network(now: Rc<RefCell<Duration>>, node_count: usize) -> Network {
        let config = NetworkConfig { node_count, delay_range: Duration::ZERO..=Duration::ZERO, loss_probability: 0.0 };
        let now_provider: Rc<dyn Fn() -> Duration + 'static> = Rc::new(move || *now.borrow());
        Network::new(&config, now_provider, Rc::new(RefCell::new(SmallRng::seed_from_u64(0xBAD5_EED))))
    }

    fn make_test_gossip(sender_id: u16, scope: GossipScope) -> GossipMessage {
        GossipMessage::new(sender_id, scope, 0x1234_5678_9ABC_DEF0, 0, -1)
    }

    #[test]
    fn network_broadcast_rejects_node_count_above_u16_max() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, (u16::MAX as usize) + 1);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.transmit_gossip(make_test_gossip(0, GossipScope::Broadcast));
        }));

        assert!(result.is_err());
    }

    #[test]
    fn network_transmit_rejects_sender_id_out_of_range() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 3);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.transmit_gossip(make_test_gossip(3, GossipScope::Broadcast));
        }));

        assert!(result.is_err());
    }

    #[test]
    fn network_drain_due_drains_all_due_messages() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 3);
        network.transmit_gossip(make_test_gossip(0, GossipScope::Broadcast));

        let drained = network.drain_due(Duration::ZERO);
        assert_eq!(2, drained.len());
        assert_eq!(1, drained[0].1.len());
        assert_eq!(1, drained[1].1.len());
        assert_eq!(None, network.soonest_arrival_at());
    }

    #[test]
    fn network_time_provider_controls_delivery_time_base() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now.clone(), 2);
        *now.borrow_mut() = Duration::seconds(5);
        network.set_node_shards(1, vec![42]);
        network.transmit_gossip(make_test_gossip(0, GossipScope::Shard(42)));
        assert_eq!(Some(Duration::seconds(5)), network.soonest_arrival_at());
    }

    #[test]
    fn network_quantizes_delay_to_50us_grid() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let config = NetworkConfig {
            node_count: 2,
            delay_range: Duration::ZERO..=Duration::microseconds(200),
            loss_probability: 0.0,
        };
        let now_provider: Rc<dyn Fn() -> Duration + 'static> = Rc::new(move || *now.borrow());
        let mut network = Network::new(&config, now_provider, Rc::new(RefCell::new(SmallRng::seed_from_u64(1234))));

        network.set_node_shards(1, vec![42]);
        for _ in 0..64 {
            network.transmit_gossip(make_test_gossip(0, GossipScope::Shard(42)));
        }
        assert!(!network.enroute.is_empty());
        for &(delivery_time, _, _) in network.enroute.keys() {
            assert_eq!(0, delivery_time.whole_microseconds() % DELAY_QUANTIZATION_STEP.whole_microseconds());
        }
    }

    #[test]
    fn network_quantized_delay_stays_in_requested_range() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let config = NetworkConfig {
            node_count: 2,
            delay_range: Duration::microseconds(1)..=Duration::microseconds(49),
            loss_probability: 0.0,
        };
        let now_provider: Rc<dyn Fn() -> Duration + 'static> = Rc::new(move || *now.borrow());
        let mut network = Network::new(&config, now_provider, Rc::new(RefCell::new(SmallRng::seed_from_u64(5678))));

        network.set_node_shards(1, vec![42]);
        for _ in 0..64 {
            network.transmit_gossip(make_test_gossip(0, GossipScope::Shard(42)));
        }
        assert!(!network.enroute.is_empty());
        for &(delivery_time, _, _) in network.enroute.keys() {
            assert!(delivery_time >= Duration::microseconds(1));
            assert!(delivery_time <= Duration::microseconds(49));
        }
    }

    #[test]
    fn shard_delivery_reaches_only_subscribers() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 4);
        network.set_node_shards(1, vec![500]);
        network.set_node_shards(2, vec![500]);
        network.set_node_shards(3, vec![700]);

        network.transmit_gossip(make_test_gossip(0, GossipScope::Shard(500)));
        let drained = network.drain_due(Duration::ZERO);
        let destinations = drained.into_iter().map(|(destination, _)| destination).collect::<BTreeSet<_>>();
        assert_eq!(BTreeSet::from([1_u16, 2_u16]), destinations);
    }

    #[test]
    fn stats_count_transmit_once_per_emission_but_receive_per_delivery_copy() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 4);
        network.set_node_shards(1, vec![500]);
        network.set_node_shards(2, vec![500]);
        network.set_node_shards(3, vec![700]);

        network.transmit_gossip(make_test_gossip(0, GossipScope::Broadcast)); // 1 emit, 3 deliveries
        network.transmit_gossip(make_test_gossip(0, GossipScope::Shard(500))); // 1 emit, 2 deliveries
        let _ = network.drain_due(Duration::ZERO);

        let stats = network.stats();
        assert_eq!(1, stats.broadcast_sent_total());
        assert_eq!(1, stats.shard_sent_total());
        assert_eq!(2, stats.sent_total());
        assert_eq!(3, stats.broadcast_received_total());
        assert_eq!(2, stats.shard_received_total());
        assert_eq!(5, stats.received_total());
    }

    #[test]
    fn stats_lost_counts_dropped_delivery_copies() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let config =
            NetworkConfig { node_count: 4, delay_range: Duration::ZERO..=Duration::ZERO, loss_probability: 1.0 };
        let now_provider: Rc<dyn Fn() -> Duration + 'static> = Rc::new(move || *now.borrow());
        let mut network = Network::new(&config, now_provider, Rc::new(RefCell::new(SmallRng::seed_from_u64(42))));

        network.transmit_gossip(make_test_gossip(0, GossipScope::Broadcast)); // 3 destination copies dropped
        let _ = network.drain_due(Duration::ZERO);

        let stats = network.stats();
        assert_eq!(1, stats.broadcast_sent_total());
        assert_eq!(0, stats.received_total());
        assert_eq!(3, stats.lost);
    }
}
