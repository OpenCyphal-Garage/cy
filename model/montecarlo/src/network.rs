use crate::message::GossipMessage;
use rand::prelude::SmallRng;
use rand::{Rng, RngExt, SeedableRng};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::RangeInclusive;
use std::rc::Rc;
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// Assuming that nodes have contiguous IDs from 0 to node_count-1; used for broadcasting.
    pub node_count: usize,
    pub delay_range: RangeInclusive<Duration>,
    pub loss_probability: f64,
}

#[derive(Debug, Clone)]
pub struct Network<'a> {
    /// Messages that are currently in transit, indexed by the destination node, then by delivery time.
    /// A tiebreaker is added in case we roll the same delivery time for distinct messages.
    /// Note that messages may be delivered out of order, depending on how the propagation delay is rolled.
    enroute: BTreeMap<u16, BTreeMap<(Duration, u64), GossipMessage>>,

    /// Propagation statistics for debugging and analysis.
    count_sent_per_node: BTreeMap<u16, u64>,
    count_received_per_node: BTreeMap<u16, u64>,
    count_lost: u64,

    /// Shared states.
    now: &'a Duration,
    rng: Rc<RefCell<SmallRng>>,

    cfg: NetworkConfig,
}

impl<'a> Network<'a> {
    pub fn new(cfg: NetworkConfig, now: &'a Duration, rng: Rc<RefCell<SmallRng>>) -> Self {
        Self {
            enroute: BTreeMap::new(),
            count_sent_per_node: BTreeMap::new(),
            count_received_per_node: BTreeMap::new(),
            count_lost: 0,
            now,
            rng,
            cfg,
        }
    }

    pub fn unicast_gossip(&mut self, destination: u16, message: GossipMessage) {
        assert!((destination as usize) < self.cfg.node_count);
        self.count_sent_per_node.entry(message.sender_id()).and_modify(|c| *c += 1).or_insert(1);
        if self.rng.borrow_mut().random_bool(self.cfg.loss_probability) {
            self.count_lost += 1;
            return;
        }
        let delay = self.rng.borrow_mut().random_range(self.cfg.delay_range.clone());
        let delivery_time = *self.now + delay;
        let tiebreaker = self.rng.borrow_mut().next_u64();
        // This is where we may introduce reordering, which is good.
        self.enroute.entry(destination).or_default().insert((delivery_time, tiebreaker), message);
    }

    pub fn broadcast_gossip(&mut self, message: GossipMessage) {
        assert!(self.cfg.node_count <= u16::MAX as usize);
        assert!((message.sender_id() as usize) < self.cfg.node_count);
        for destination in 0..(self.cfg.node_count as u16) {
            if destination != message.sender_id() {
                self.unicast_gossip(destination, message.clone());
            }
        }
    }

    pub fn pull(&mut self, now: Duration, destination: u16) -> Option<GossipMessage> {
        if let Some(dest_queue) = self.enroute.get_mut(&destination) {
            if let Some((&(delivery_time, tie), message)) = dest_queue.iter().next() {
                if delivery_time <= now {
                    self.count_received_per_node.entry(destination).and_modify(|c| *c += 1).or_insert(1);
                    return dest_queue.remove(&(delivery_time, tie));
                }
            }
        }
        None
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
    use std::panic::{AssertUnwindSafe, catch_unwind};

    fn make_test_network(now: &Duration, node_count: usize) -> Network<'_> {
        let config = NetworkConfig { node_count, delay_range: Duration::ZERO..=Duration::ZERO, loss_probability: 0.0 };
        Network::new(config, now, Rc::new(RefCell::new(SmallRng::seed_from_u64(0xBAD5_EED))))
    }

    fn make_test_gossip(sender_id: u16) -> GossipMessage {
        GossipMessage::new(sender_id, 0, 0, 0x1234_5678_9ABC_DEF0, 0, -1)
    }

    #[test]
    fn network_broadcast_rejects_node_count_above_u16_max() {
        let now = Duration::ZERO;
        let mut network = make_test_network(&now, (u16::MAX as usize) + 1);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.broadcast_gossip(make_test_gossip(0));
        }));

        assert!(result.is_err());
    }

    #[test]
    fn network_broadcast_rejects_sender_id_out_of_range() {
        let now = Duration::ZERO;
        let mut network = make_test_network(&now, 3);

        let result = catch_unwind(AssertUnwindSafe(|| {
            network.broadcast_gossip(make_test_gossip(3));
        }));

        assert!(result.is_err());
    }
}
