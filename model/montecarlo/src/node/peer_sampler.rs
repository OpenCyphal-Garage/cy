use rand::{Rng, RngExt};
use time::Duration;

#[derive(Debug, Clone)]
pub(super) struct PeerSamplerConfig {
    pub self_id: u16,
    pub peer_count: usize,
    pub peer_age_reachable: Duration,
    pub peer_age_replaceable: Duration,
}

#[derive(Debug, Clone)]
struct PeerEntry {
    remote_id: u16,
    ticket: u64,
    last_seen: Duration,
}

pub(super) struct PeerSampler {
    peers: Vec<PeerEntry>,
    cfg: PeerSamplerConfig,
}

impl PeerSampler {
    pub(super) fn new(cfg: PeerSamplerConfig) -> Self {
        Self { peers: Vec::new(), cfg }
    }

    pub fn peer_ids(&self) -> Vec<u16> {
        self.peers.iter().map(|peer| peer.remote_id).collect()
    }

    pub fn observe(&mut self, now: Duration, remote_id: u16) {
        if (remote_id == self.cfg.self_id) || (self.cfg.peer_count == 0) {
            return;
        }
        if let Some(peer) = self.peers.iter_mut().find(|peer| peer.remote_id == remote_id) {
            peer.last_seen = now;
            return;
        }
        let new_ticket = ticket(self.cfg.self_id, remote_id);
        if self.peers.len() < self.cfg.peer_count {
            self.peers.push(PeerEntry { remote_id, ticket: new_ticket, last_seen: now });
            return;
        }
        let expired_index = self
            .peers
            .iter()
            .enumerate()
            .filter(|(_, peer)| (now - peer.last_seen) > self.cfg.peer_age_replaceable)
            .min_by_key(|(_, peer)| peer.last_seen)
            .map(|(index, _)| index);
        if let Some(index) = expired_index {
            self.peers[index] = PeerEntry { remote_id, ticket: new_ticket, last_seen: now };
            return;
        }
        let worst_index = self
            .peers
            .iter()
            .enumerate()
            .max_by_key(|(_, peer)| (peer.ticket, peer.remote_id))
            .map(|(index, _)| index)
            .expect("peer set cannot be empty when selecting the worst live ticket");
        if new_ticket < self.peers[worst_index].ticket {
            self.peers[worst_index] = PeerEntry { remote_id, ticket: new_ticket, last_seen: now };
        }
    }

    pub fn sample_targets(&self, now: Duration, outdegree: u8, blacklist: &[u16], rng: &mut dyn Rng) -> Vec<u16> {
        if outdegree == 0 {
            return Vec::new();
        }
        let mut eligible = self
            .peers
            .iter()
            .filter_map(|peer| {
                let blocked = blacklist.iter().any(|peer_id| *peer_id == peer.remote_id);
                if !blocked && self.is_reachable(now, peer) { Some(peer.remote_id) } else { None }
            })
            .collect::<Vec<_>>();
        let mut targets = Vec::new();
        while (targets.len() < outdegree as usize) && !eligible.is_empty() {
            let index = rng.random_range(0..eligible.len());
            targets.push(eligible.swap_remove(index));
        }
        targets
    }

    pub fn needs_broadcast_bootstrap(&self, now: Duration) -> bool {
        if self.peers.len() < self.cfg.peer_count {
            return true;
        }
        self.peers.iter().any(|peer| !self.is_reachable(now, peer))
    }

    fn is_reachable(&self, now: Duration, peer: &PeerEntry) -> bool {
        (now - peer.last_seen) <= self.cfg.peer_age_reachable
    }

    #[cfg(test)]
    pub(crate) fn set_peers_for_test(&mut self, peers: Vec<(u16, Duration)>) {
        self.peers = peers
            .into_iter()
            .map(|(remote_id, last_seen)| PeerEntry {
                remote_id,
                ticket: ticket(self.cfg.self_id, remote_id),
                last_seen,
            })
            .collect();
    }
}

pub(super) fn ticket(local_id: u16, remote_id: u16) -> u64 {
    let mut x = (((local_id as u64) << 16) | (remote_id as u64)).wrapping_add(0x9E37_79B9_7F4A_7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use std::collections::BTreeSet;

    fn cfg(self_id: u16) -> PeerSamplerConfig {
        PeerSamplerConfig {
            self_id,
            peer_count: 3,
            peer_age_reachable: Duration::seconds(10),
            peer_age_replaceable: Duration::seconds(5),
        }
    }

    #[test]
    fn observe_ignores_self_and_refreshes_existing_without_membership_change() {
        let mut local_cfg = cfg(7);
        local_cfg.peer_count = 1;
        let mut sampler = PeerSampler::new(local_cfg);
        sampler.observe(Duration::seconds(1), 7);
        assert!(sampler.peer_ids().is_empty());

        sampler.observe(Duration::seconds(1), 10);
        sampler.observe(Duration::seconds(4), 10);
        assert_eq!(vec![10], sampler.peer_ids());
        assert!(!sampler.needs_broadcast_bootstrap(Duration::seconds(6)));
    }

    #[test]
    fn observe_retains_smallest_tickets_among_live_peers() {
        let mut sampler = PeerSampler::new(cfg(0));
        for remote_id in [1_u16, 2, 3, 4, 5, 6] {
            sampler.observe(Duration::seconds(1), remote_id);
        }
        let kept = sampler.peer_ids().into_iter().collect::<BTreeSet<_>>();
        let expected = (1_u16..=6).map(|remote_id| (remote_id, ticket(0, remote_id))).collect::<Vec<_>>();
        let expected = expected
            .iter()
            .cloned()
            .fold(Vec::<(u16, u64)>::new(), |mut smallest, entry| {
                smallest.push(entry);
                smallest.sort_by_key(|(_, t)| *t);
                smallest.truncate(3);
                smallest
            })
            .into_iter()
            .map(|(remote_id, _)| remote_id)
            .collect::<BTreeSet<_>>();
        assert_eq!(expected, kept);
    }

    #[test]
    fn observe_replaces_expired_peer_even_if_expired_ticket_is_better() {
        let mut local_cfg = cfg(0);
        local_cfg.peer_count = 2;
        let mut sampler = PeerSampler::new(local_cfg);
        sampler.set_peers_for_test(vec![(1, Duration::ZERO)]);
        sampler.observe(Duration::seconds(1), 2);
        let new_peer = (3_u16..=64)
            .find(|remote_id| ticket(0, *remote_id) > ticket(0, 1))
            .expect("test setup requires a worse-ticket replacement candidate");
        assert!(ticket(0, new_peer) > ticket(0, 1));

        sampler.observe(Duration::seconds(10), new_peer);

        let ids = sampler.peer_ids().into_iter().collect::<BTreeSet<_>>();
        assert!(ids.contains(&2));
        assert!(ids.contains(&new_peer));
        assert!(!ids.contains(&1));
    }

    #[test]
    fn observe_allows_immediate_consecutive_replacements_without_moratorium() {
        let mut local_cfg = cfg(0);
        local_cfg.peer_count = 1;
        local_cfg.peer_age_replaceable = Duration::seconds(100);
        let mut sampler = PeerSampler::new(local_cfg);
        let all = (1_u16..=32).map(|remote_id| (remote_id, ticket(0, remote_id))).collect::<Vec<_>>();
        let worst = all.iter().max_by_key(|(_, t)| *t).map(|(remote_id, _)| *remote_id).expect("non-empty setup");
        let mut best_two = all.clone();
        best_two.sort_by_key(|(_, t)| *t);
        let first = best_two[1].0;
        let second = best_two[0].0;
        sampler.set_peers_for_test(vec![(worst, Duration::ZERO)]);

        sampler.observe(Duration::seconds(1), first);
        sampler.observe(Duration::seconds(1), second);

        assert_eq!(vec![second], sampler.peer_ids());
    }

    #[test]
    fn observe_does_not_replace_live_peer_with_worse_ticket() {
        let mut local_cfg = cfg(0);
        local_cfg.peer_count = 1;
        local_cfg.peer_age_replaceable = Duration::seconds(100);
        let mut sampler = PeerSampler::new(local_cfg);
        let all = (1_u16..=64).map(|remote_id| (remote_id, ticket(0, remote_id))).collect::<Vec<_>>();
        let best = all.iter().min_by_key(|(_, t)| *t).map(|(remote_id, _)| *remote_id).expect("non-empty setup");
        let worse = all
            .iter()
            .find(|(remote_id, t)| (*remote_id != best) && (*t > ticket(0, best)))
            .map(|(remote_id, _)| *remote_id)
            .expect("test setup requires a worse ticket candidate");
        sampler.set_peers_for_test(vec![(best, Duration::ZERO)]);

        for now in [Duration::seconds(1), Duration::seconds(2), Duration::seconds(3)] {
            sampler.observe(now, worse);
        }

        assert_eq!(vec![best], sampler.peer_ids());
    }

    #[test]
    fn sample_targets_respects_blacklist_outdegree_and_reachability() {
        let mut sampler = PeerSampler::new(cfg(0));
        sampler.set_peers_for_test(vec![(1, Duration::ZERO), (2, Duration::seconds(100)), (3, Duration::seconds(100))]);
        let mut rng = rand::rngs::SmallRng::seed_from_u64(1);

        let targets = sampler.sample_targets(Duration::seconds(105), 3, &[2], &mut rng);

        assert_eq!(1, targets.len());
        assert_eq!(3, targets[0]);
    }

    #[test]
    fn needs_broadcast_bootstrap_is_true_for_incomplete_or_stale_sets() {
        let mut local_cfg = cfg(0);
        local_cfg.peer_count = 2;
        let mut sampler = PeerSampler::new(local_cfg);
        assert!(sampler.needs_broadcast_bootstrap(Duration::ZERO));

        sampler.set_peers_for_test(vec![(1, Duration::seconds(10)), (2, Duration::seconds(10))]);
        assert!(!sampler.needs_broadcast_bootstrap(Duration::seconds(12)));
        assert!(sampler.needs_broadcast_bootstrap(Duration::seconds(30)));
    }
}
