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
    let now: Rc<dyn Fn() -> Duration + 'static> = Rc::new(|| Duration::ZERO);
    Node::new(0, network, rng, now, &cfg).unwrap()
}

fn snapshot(node: &Node<'_>, modulus: u16) -> Vec<(u64, u16, u16)> {
    node.topics_by_hash.values().map(|topic| (topic.hash(), topic.subject_id(modulus), topic.evictions())).collect()
}

fn make_recording_node(cfg: NodeConfig) -> (Node<'static>, Rc<RefCell<TxLog>>, Rc<RefCell<Duration>>) {
    let log = Rc::new(RefCell::new(TxLog::default()));
    let network: Rc<RefCell<dyn Transmit>> = Rc::new(RefCell::new(RecordingNetwork { log: log.clone() }));
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0xBAD5_EED0)));
    let now = Rc::new(RefCell::new(Duration::ZERO));
    let now_provider: Rc<dyn Fn() -> Duration + 'static> = {
        let now = now.clone();
        Rc::new(move || *now.borrow())
    };
    (Node::new(0, network, rng, now_provider, &cfg).unwrap(), log, now)
}

fn make_message(sender: u16, ttl: u8, outdegree: u8, hash: u64, evictions: u16, lage: i8) -> GossipMessage {
    GossipMessage::new(sender, ttl, outdegree, hash, evictions, lage)
}

#[test]
fn new_rejects_non_prime_modulus() {
    let cfg = NodeConfig { subject_id_modulus: 12, ..NodeConfig::default() };
    let network = Rc::new(RefCell::new(StubNetwork));
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0)));
    let now: Rc<dyn Fn() -> Duration + 'static> = Rc::new(|| Duration::ZERO);
    assert!(Node::new(0, network, rng, now, &cfg).is_err());
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
    let (mut node, log, now) = make_recording_node(cfg);
    node.add_topic(1);
    node.gossip_at = Duration::MAX;

    *now.borrow_mut() = Duration::seconds(8);
    node.step(vec![make_message(42, 3, 2, 1, 1, 2)]);

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
    let (mut node, log, now) = make_recording_node(cfg);
    node.add_topic(1);
    node.gossip_at = Duration::MAX;

    *now.borrow_mut() = Duration::seconds(2);
    node.step(vec![make_message(7, 2, 1, 1, 4, 3)]);

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
    let (mut node, log, now) = make_recording_node(cfg);
    node.add_topic(2);
    node.gossip_at = Duration::MAX;
    node.set_peers_for_test(vec![(5, Duration::seconds(1)), (7, Duration::seconds(1))]);

    *now.borrow_mut() = Duration::seconds(1);
    node.step(vec![make_message(5, 3, 1, 1, 1, 3)]);

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
    let (mut node, log, now) = make_recording_node(cfg);
    node.gossip_at = Duration::MAX;
    node.set_peers_for_test(vec![(5, Duration::ZERO), (7, Duration::ZERO)]);
    let message = make_message(5, 3, 1, 42, 0, -1);

    *now.borrow_mut() = Duration::seconds(0);
    node.step(vec![message.clone()]);
    *now.borrow_mut() = Duration::seconds(1);
    node.step(vec![message.clone()]);
    *now.borrow_mut() = Duration::seconds(7);
    node.step(vec![message]);

    let log = log.borrow();
    assert_eq!(2, log.unicasts.len());
    assert!(log.unicasts.iter().all(|(destination, _)| *destination == 7));
}

#[test]
fn forwarding_respects_message_outdegree_and_excludes_sender() {
    let cfg = NodeConfig { subject_id_modulus: 11, gossip_outdegree_urgent: 0, ..NodeConfig::default() };
    let (mut node, log, now) = make_recording_node(cfg);
    node.gossip_at = Duration::MAX;
    node.set_peers_for_test(vec![(1, Duration::ZERO), (2, Duration::ZERO), (3, Duration::ZERO)]);

    *now.borrow_mut() = Duration::seconds(1);
    node.step(vec![make_message(1, 4, 2, 99, 0, -1)]);

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
    let (mut node, _, now) = make_recording_node(cfg);
    node.gossip_at = Duration::MAX;
    node.set_peers_for_test(vec![(1, Duration::ZERO)]);
    node.set_peer_moratorium_until_for_test(Duration::seconds(1000));

    *now.borrow_mut() = Duration::seconds(10);
    node.step(vec![make_message(2, 0, 0, 12, 0, -1)]);
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
    let (mut node, _, now) = make_recording_node(cfg);
    node.gossip_at = Duration::MAX;
    node.set_peers_for_test(vec![(1, Duration::ZERO)]);
    node.set_peer_moratorium_until_for_test(Duration::seconds(5));

    *now.borrow_mut() = Duration::seconds(1);
    node.step(vec![make_message(2, 0, 0, 12, 0, -1)]);
    assert_eq!(vec![1], node.peer_ids());
    *now.borrow_mut() = Duration::seconds(6);
    node.step(vec![make_message(2, 0, 0, 13, 0, -1)]);
    assert_eq!(vec![2], node.peer_ids());
    assert_eq!(Duration::seconds(16), node.peer_moratorium_until_for_test());
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
    let (mut node, log, now) = make_recording_node(cfg);
    node.add_topic(1);
    node.gossip_at = Duration::ZERO;

    *now.borrow_mut() = Duration::ZERO;
    node.step(Vec::new());

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
    let (mut node, log, now) = make_recording_node(cfg);
    node.add_topic(1);
    node.set_peers_for_test(vec![(9, Duration::ZERO)]);
    node.gossip_at = Duration::ZERO;

    *now.borrow_mut() = Duration::ZERO;
    node.step(Vec::new());

    let log = log.borrow();
    assert!(log.broadcasts.is_empty());
    assert_eq!(1, log.unicasts.len());
    assert_eq!(9, log.unicasts[0].0);
    assert_eq!(2, log.unicasts[0].1.ttl());
    assert_eq!(1, log.unicasts[0].1.outdegree());
}
