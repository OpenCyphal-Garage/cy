use super::*;
use rand::SeedableRng;
use rand::rngs::SmallRng;

#[derive(Default)]
struct TxLog {
    messages: Vec<GossipMessage>,
}

struct RecordingNetwork {
    log: Rc<RefCell<TxLog>>,
}

impl Transmit for RecordingNetwork {
    fn transmit_gossip(&mut self, message: GossipMessage) {
        self.log.borrow_mut().messages.push(message);
    }

    fn set_node_shards(&mut self, _node_id: u16, _shards: Vec<u32>) {}
}

fn make_recording_node(
    cfg: NodeConfig,
    shard_count: u32,
) -> (Node<'static>, Rc<RefCell<TxLog>>, Rc<RefCell<Duration>>) {
    let log = Rc::new(RefCell::new(TxLog::default()));
    let network: Rc<RefCell<dyn Transmit>> = Rc::new(RefCell::new(RecordingNetwork { log: log.clone() }));
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0xBAD5_EED0)));
    let now = Rc::new(RefCell::new(Duration::ZERO));
    let now_provider: Rc<dyn Fn() -> Duration + 'static> = {
        let now = now.clone();
        Rc::new(move || *now.borrow())
    };
    (Node::new(0, shard_count, network, rng, now_provider, &cfg).unwrap(), log, now)
}

fn make_message(sender: u16, scope: GossipScope, hash: u64, evictions: u16, lage: i8) -> GossipMessage {
    GossipMessage::new(sender, scope, hash, evictions, lage)
}

fn take_messages(log: &Rc<RefCell<TxLog>>) -> Vec<GossipMessage> {
    std::mem::take(&mut log.borrow_mut().messages)
}

fn defer_periodic(node: &mut Node<'_>) {
    for state in node.topic_schedule_by_hash.values_mut() {
        state.next_gossip_at = Duration::MAX;
    }
    node.next_topic_update_at_stale.set(true);
}

fn set_topic_next_gossip_at(node: &mut Node<'_>, hash: u64, at: Duration) {
    node.topic_schedule_by_hash.get_mut(&hash).expect("missing schedule state").next_gossip_at = at;
    node.next_topic_update_at_stale.set(true);
}

fn insert_pending_urgent(node: &mut Node<'_>, hash: u64, deadline: Duration, scope: UrgentScope) {
    node.pending_urgent_by_hash.insert(hash, PendingUrgentGossip { deadline, scope });
    node.next_urgent_update_at_stale.set(true);
}

#[test]
fn new_rejects_non_prime_modulus() {
    let cfg = NodeConfig { subject_id_modulus: 12, ..NodeConfig::default() };
    let log = Rc::new(RefCell::new(TxLog::default()));
    let network: Rc<RefCell<dyn Transmit>> = Rc::new(RefCell::new(RecordingNetwork { log }));
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0)));
    let now: Rc<dyn Fn() -> Duration + 'static> = Rc::new(|| Duration::ZERO);
    assert!(Node::new(0, 1, network, rng, now, &cfg).is_err());
}

#[test]
fn new_rejects_zero_shard_count() {
    let cfg = NodeConfig::default();
    let log = Rc::new(RefCell::new(TxLog::default()));
    let network: Rc<RefCell<dyn Transmit>> = Rc::new(RefCell::new(RecordingNetwork { log }));
    let rng = Rc::new(RefCell::new(SmallRng::seed_from_u64(0)));
    let now: Rc<dyn Fn() -> Duration + 'static> = Rc::new(|| Duration::ZERO);
    assert!(Node::new(0, 0, network, rng, now, &cfg).is_err());
}

#[test]
fn first_periodic_gossip_is_forced_broadcast_and_rescheduled_by_send_window() {
    let cfg = NodeConfig {
        gossip_period: Duration::seconds(5),
        gossip_dither: Duration::seconds(1),
        gossip_broadcast_fraction: 0.1,
        ..NodeConfig::default()
    };
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(42);
    set_topic_next_gossip_at(&mut node, 42, Duration::ZERO);

    *now.borrow_mut() = Duration::ZERO;
    node.step(Vec::new());

    let messages = take_messages(&log);
    assert_eq!(1, messages.len());
    assert_eq!(GossipScope::Broadcast, messages[0].scope());

    let state = node.topic_schedule_by_hash.get(&42).expect("missing schedule state");
    assert_eq!(1, state.periodic_emissions);
    assert!(!state.first_periodic_broadcast_pending);
    assert!(state.next_gossip_at >= Duration::seconds(4));
    assert!(state.next_gossip_at <= Duration::seconds(6));
}

#[test]
fn topic_creation_applies_startup_jitter_before_first_periodic_gossip() {
    let cfg = NodeConfig {
        gossip_period: Duration::seconds(5),
        gossip_dither: Duration::seconds(1),
        ..NodeConfig::default()
    };
    let (mut node, _log, now) = make_recording_node(cfg, 100);
    *now.borrow_mut() = Duration::seconds(10);
    node.add_topic(123);

    let state = node.topic_schedule_by_hash.get(&123).expect("missing schedule state");
    assert!(state.next_gossip_at >= Duration::seconds(10));
    assert!(state.next_gossip_at <= Duration::seconds(22)); // startup window: [0, 2*(5+1)] seconds from now
}

#[test]
fn periodic_scheduler_emits_one_oldest_due_topic() {
    let cfg =
        NodeConfig { gossip_period: Duration::seconds(5), gossip_dither: Duration::ZERO, ..NodeConfig::default() };
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    node.add_topic(2);

    set_topic_next_gossip_at(&mut node, 1, Duration::seconds(5));
    set_topic_next_gossip_at(&mut node, 2, Duration::seconds(3));

    *now.borrow_mut() = Duration::seconds(5);
    node.step(Vec::new());

    let messages = take_messages(&log);
    assert_eq!(1, messages.len());
    assert_eq!(2, messages[0].topic_hash());
    assert_eq!(Duration::seconds(5), node.topic_schedule_by_hash.get(&1).unwrap().next_gossip_at);
    assert_eq!(Duration::seconds(10), node.topic_schedule_by_hash.get(&2).unwrap().next_gossip_at);
}

#[test]
fn known_gossip_reschedules_topic_to_duplicate_suppression_window() {
    let cfg = NodeConfig {
        gossip_period: Duration::seconds(5),
        gossip_dither: Duration::seconds(1),
        ..NodeConfig::default()
    };
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    defer_periodic(&mut node);

    *now.borrow_mut() = Duration::seconds(10);
    node.step(vec![make_message(7, GossipScope::Shard(2000), 1, 0, -1)]);

    assert!(take_messages(&log).is_empty());
    let state = node.topic_schedule_by_hash.get(&1).expect("missing schedule state");
    assert!(state.next_gossip_at >= Duration::seconds(18));
    assert!(state.next_gossip_at <= Duration::seconds(22));
}

#[test]
fn periodic_scope_uses_per_topic_ratio_after_first_broadcast() {
    let cfg = NodeConfig {
        gossip_period: Duration::seconds(5),
        gossip_dither: Duration::ZERO,
        gossip_broadcast_fraction: 0.1,
        ..NodeConfig::default()
    };
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(42);
    let shard = node.subject_id_modulus() + ((42 % 100) as u32);

    for emission in 1_i64..=20 {
        *now.borrow_mut() = Duration::seconds(emission);
        set_topic_next_gossip_at(&mut node, 42, Duration::seconds(emission));
        node.step(Vec::new());

        let messages = take_messages(&log);
        assert_eq!(1, messages.len());
        let expected_scope = if (emission == 1) || (emission == 10) || (emission == 20) {
            GossipScope::Broadcast
        } else {
            GossipScope::Shard(shard)
        };
        assert_eq!(expected_scope, messages[0].scope(), "unexpected scope at emission {emission}");
    }
}

#[test]
fn next_update_at_uses_earliest_periodic_or_urgent_deadline() {
    let cfg = NodeConfig::default();
    let (mut node, _log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    node.add_topic(2);
    set_topic_next_gossip_at(&mut node, 1, Duration::seconds(10));
    set_topic_next_gossip_at(&mut node, 2, Duration::seconds(7));
    assert_eq!(Duration::seconds(7), node.next_update_at());

    insert_pending_urgent(&mut node, 1, Duration::seconds(3), UrgentScope::Shard);
    assert_eq!(Duration::seconds(3), node.next_update_at());

    *now.borrow_mut() = Duration::seconds(9);
    node.pending_urgent_by_hash.clear();
    node.next_urgent_update_at_stale.set(true);
    set_topic_next_gossip_at(&mut node, 1, Duration::seconds(4));
    set_topic_next_gossip_at(&mut node, 2, Duration::seconds(6));
    assert_eq!(Duration::seconds(4), node.next_update_at());
}

#[test]
fn known_topic_local_win_divergence_schedules_delayed_urgent_shard() {
    let cfg = NodeConfig { gossip_urgent_delay: Duration::milliseconds(50), ..NodeConfig::default() };
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    defer_periodic(&mut node);

    *now.borrow_mut() = Duration::seconds(8);
    node.step(vec![make_message(7, GossipScope::Shard(2000), 1, 1, 2)]);

    assert!(log.borrow().messages.is_empty());
    let pending = node.pending_urgent_by_hash.get(&1).copied().expect("urgent gossip must be pending");
    assert_eq!(UrgentScope::Shard, pending.scope);
    assert!(pending.deadline >= Duration::seconds(8));
    assert!(pending.deadline <= Duration::seconds(8) + Duration::milliseconds(50));
}

#[test]
fn unknown_topic_local_win_collision_schedules_delayed_urgent_broadcast() {
    let cfg =
        NodeConfig { subject_id_modulus: 11, gossip_urgent_delay: Duration::milliseconds(50), ..NodeConfig::default() };
    let (mut node, log, now) = make_recording_node(cfg, 16);
    node.add_topic(2);
    defer_periodic(&mut node);

    *now.borrow_mut() = Duration::seconds(8);
    node.step(vec![make_message(7, GossipScope::Shard(11), 1, 1, 2)]); // subject_id=2 collides with topic 2

    assert!(log.borrow().messages.is_empty());
    let pending = node.pending_urgent_by_hash.get(&2).copied().expect("urgent gossip must be pending");
    assert_eq!(UrgentScope::Broadcast, pending.scope);
}

#[test]
fn delayed_urgent_is_canceled_by_up_to_date_gossip_before_deadline() {
    let cfg = NodeConfig::default();
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    defer_periodic(&mut node);

    *now.borrow_mut() = Duration::seconds(1);
    insert_pending_urgent(&mut node, 1, Duration::seconds(1) + Duration::milliseconds(10), UrgentScope::Shard);

    *now.borrow_mut() = Duration::seconds(1) + Duration::milliseconds(5);
    node.step(vec![make_message(9, GossipScope::Shard(2000), 1, 0, -1)]);
    assert!(!node.pending_urgent_by_hash.contains_key(&1));

    *now.borrow_mut() = Duration::seconds(1) + Duration::milliseconds(20);
    node.step(Vec::new());
    assert!(take_messages(&log).is_empty());
}

#[test]
fn shard_selection_is_invariant_across_evictions_for_same_hash() {
    let cfg = NodeConfig::default();
    let (mut node, _log, _now) = make_recording_node(cfg, 100);
    node.add_topic(0xDEAD_BEEF);
    let shard_before = node.shard_for_topic(0xDEAD_BEEF);

    node.topics_by_hash.get_mut(&0xDEAD_BEEF).unwrap().set_evictions(123);
    let shard_after = node.shard_for_topic(0xDEAD_BEEF);

    assert_eq!(shard_before, shard_after);
}

#[test]
fn urgent_requests_coalesce_and_upgrade_to_broadcast() {
    let cfg = NodeConfig { gossip_urgent_delay: Duration::milliseconds(50), ..NodeConfig::default() };
    let (mut node, _log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);

    insert_pending_urgent(&mut node, 1, Duration::seconds(1), UrgentScope::Shard);

    *now.borrow_mut() = Duration::seconds(2);
    node.schedule_urgent(Duration::seconds(2), 1, UrgentScope::Broadcast);
    let second = node.pending_urgent_by_hash.get(&1).copied().unwrap();

    assert_eq!(UrgentScope::Broadcast, second.scope);
    assert_eq!(Duration::seconds(1), second.deadline);
}

#[test]
fn urgent_send_uses_current_local_topic_state_and_send_reschedule_window() {
    let cfg = NodeConfig::default();
    let (mut node, log, now) = make_recording_node(cfg, 100);
    node.add_topic(1);
    defer_periodic(&mut node);

    insert_pending_urgent(&mut node, 1, Duration::seconds(2), UrgentScope::Shard);
    node.topics_by_hash.get_mut(&1).unwrap().set_evictions(7);

    *now.borrow_mut() = Duration::seconds(2);
    node.step(Vec::new());

    let messages = take_messages(&log);
    assert_eq!(1, messages.len());
    assert_eq!(7, messages[0].topic_evictions());
    let state = node.topic_schedule_by_hash.get(&1).expect("missing schedule state");
    assert!(state.next_gossip_at >= Duration::seconds(6));
    assert!(state.next_gossip_at <= Duration::seconds(8));
}
