use crate::message::{GossipMessage, Transmit};
use rand::{Rng, RngExt};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::RangeInclusive;
use std::rc::Rc;
use time::Duration;

#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// Assuming that nodes have contiguous IDs from 0 to node_count-1; used for broadcasting.
    pub node_count: usize,
    pub delay_range: RangeInclusive<Duration>,
    pub loss_probability: f64,
}

pub struct Network {
    /// Messages that are currently in transit, indexed by the destination node, then by delivery time.
    /// A tiebreaker is added in case we roll the same delivery time for distinct messages.
    /// Note that messages may be delivered out of order, depending on how the propagation delay is rolled.
    enroute: BTreeMap<u16, BTreeMap<(Duration, u64), GossipMessage>>,

    /// Propagation statistics for debugging and analysis.
    count_sent_per_node: BTreeMap<u16, u64>,
    count_received_per_node: BTreeMap<u16, u64>,
    count_lost: u64,

    /// Shared states.
    now: Rc<dyn Fn() -> Duration + 'static>,
    rng: Rc<RefCell<dyn Rng>>,

    cfg: NetworkConfig,
}

impl Transmit for Network {
    fn unicast_gossip(&mut self, destination: u16, message: GossipMessage) {
        assert!((destination as usize) < self.cfg.node_count);
        self.count_sent_per_node.entry(message.sender_id()).and_modify(|c| *c += 1).or_insert(1);
        if self.rng.borrow_mut().random_bool(self.cfg.loss_probability) {
            self.count_lost += 1;
            return;
        }
        let delay_start = *self.cfg.delay_range.start();
        let delay_end = *self.cfg.delay_range.end();
        let delay = if delay_start == delay_end {
            delay_start
        } else {
            let sampled_seconds =
                self.rng.borrow_mut().random_range(delay_start.as_seconds_f64()..=delay_end.as_seconds_f64());
            Duration::seconds_f64(sampled_seconds)
        };
        let delivery_time = (self.now)() + delay;
        let tiebreaker = self.rng.borrow_mut().next_u64();
        // This is where we may introduce reordering, which is good.
        self.enroute.entry(destination).or_default().insert((delivery_time, tiebreaker), message);
    }

    fn broadcast_gossip(&mut self, message: GossipMessage) {
        assert!(self.cfg.node_count <= u16::MAX as usize);
        assert!((message.sender_id() as usize) < self.cfg.node_count);
        for destination in 0..(self.cfg.node_count as u16) {
            if destination != message.sender_id() {
                self.unicast_gossip(destination, message.clone());
            }
        }
    }
}

impl Network {
    pub fn new(cfg: &NetworkConfig, now: Rc<dyn Fn() -> Duration + 'static>, rng: Rc<RefCell<dyn Rng>>) -> Self {
        Self {
            enroute: BTreeMap::new(),
            count_sent_per_node: BTreeMap::new(),
            count_received_per_node: BTreeMap::new(),
            count_lost: 0,
            now,
            rng,
            cfg: cfg.clone(),
        }
    }

    pub fn pull(&mut self, now: Duration, destination: u16) -> Vec<GossipMessage> {
        let mut out = Vec::new();
        if let Some(dest_queue) = self.enroute.get_mut(&destination) {
            while let Some((&(delivery_time, tie), _)) = dest_queue.iter().next() {
                if delivery_time > now {
                    break;
                }
                self.count_received_per_node.entry(destination).and_modify(|c| *c += 1).or_insert(1);
                let msg = dest_queue.remove(&(delivery_time, tie));
                out.push(msg.expect("enroute message disappeared while draining arrivals"));
            }
        }
        out
    }

    pub fn soonest_arrival_at(&self) -> Option<Duration> {
        // TODO optimize by keeping a separate priority queue of soonest arrivals.
        self.enroute.values().filter_map(|dest_queue| dest_queue.keys().next().map(|&(time, _)| time)).min()
    }

    pub fn config(&self) -> &NetworkConfig {
        &self.cfg
    }
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

    fn make_test_gossip(sender_id: u16) -> GossipMessage {
        GossipMessage::new(sender_id, 0, 0, 0x1234_5678_9ABC_DEF0, 0, -1)
    }

    #[test]
    fn network_broadcast_rejects_node_count_above_u16_max() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, (u16::MAX as usize) + 1);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.broadcast_gossip(make_test_gossip(0));
        }));

        assert!(result.is_err());
    }

    #[test]
    fn network_broadcast_rejects_sender_id_out_of_range() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 3);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.broadcast_gossip(make_test_gossip(3));
        }));

        assert!(result.is_err());
    }

    #[test]
    fn network_pull_drains_all_due_messages() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now, 2);
        network.unicast_gossip(1, make_test_gossip(0));
        network.unicast_gossip(1, make_test_gossip(0));

        let pulled = network.pull(Duration::ZERO, 1);
        assert_eq!(2, pulled.len());
        assert_eq!(None, network.soonest_arrival_at());
    }

    #[test]
    fn network_time_provider_controls_delivery_time_base() {
        let now = Rc::new(RefCell::new(Duration::ZERO));
        let mut network = make_test_network(now.clone(), 2);
        *now.borrow_mut() = Duration::seconds(5);
        network.unicast_gossip(1, make_test_gossip(0));
        assert_eq!(Some(Duration::seconds(5)), network.soonest_arrival_at());
    }
}
