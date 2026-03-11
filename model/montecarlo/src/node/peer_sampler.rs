use rand::{Rng, RngExt};
use std::ops::RangeInclusive;
use time::Duration;

#[derive(Debug, Clone)]
pub(super) struct PeerSamplerConfig {
    pub self_id: u16,
    pub peer_count: usize,
    pub peer_age_reachable: Duration,
    pub peer_age_replaceable: Duration,
    pub peer_replacement_probability: f64,
    pub peer_moratorium_range: RangeInclusive<Duration>,
}

#[derive(Debug, Clone)]
struct PeerEntry {
    remote_id: u16,
    last_seen: Duration,
}

pub(super) struct PeerSampler {
    peers: Vec<PeerEntry>,
    peer_moratorium_until: Duration,
    cfg: PeerSamplerConfig,
}

impl PeerSampler {
    pub(super) fn new(cfg: PeerSamplerConfig) -> Self {
        Self { peers: Vec::new(), peer_moratorium_until: Duration::ZERO, cfg }
    }

    pub fn peer_ids(&self) -> Vec<u16> {
        self.peers.iter().map(|peer| peer.remote_id).collect()
    }

    pub fn observe(&mut self, now: Duration, remote_id: u16, rng: &mut dyn Rng) {
        if (remote_id == self.cfg.self_id) || (self.cfg.peer_count == 0) {
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
        } else if (now >= self.peer_moratorium_until) && rng.random_bool(self.cfg.peer_replacement_probability) {
            Some(rng.random_range(0..self.peers.len()))
        } else {
            None
        };
        if let Some(index) = replacement_index {
            self.peers[index] = PeerEntry { remote_id, last_seen: now };
            self.peer_moratorium_until = now + self.sample_peer_moratorium(rng);
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

    fn sample_duration_between(&self, low: Duration, high: Duration, rng: &mut dyn Rng) -> Duration {
        if low >= high {
            return low;
        }
        let sampled_seconds = rng.random_range(low.as_seconds_f64()..=high.as_seconds_f64());
        Duration::seconds_f64(sampled_seconds)
    }

    fn sample_peer_moratorium(&self, rng: &mut dyn Rng) -> Duration {
        self.sample_duration_between(
            *self.cfg.peer_moratorium_range.start(),
            *self.cfg.peer_moratorium_range.end(),
            rng,
        )
    }

    fn is_reachable(&self, now: Duration, peer: &PeerEntry) -> bool {
        (now - peer.last_seen) <= self.cfg.peer_age_reachable
    }

    #[cfg(test)]
    pub(crate) fn set_peers_for_test(&mut self, peers: Vec<(u16, Duration)>) {
        self.peers = peers.into_iter().map(|(remote_id, last_seen)| PeerEntry { remote_id, last_seen }).collect();
    }

    #[cfg(test)]
    pub(crate) fn set_moratorium_until_for_test(&mut self, until: Duration) {
        self.peer_moratorium_until = until;
    }

    #[cfg(test)]
    pub(crate) fn moratorium_until_for_test(&self) -> Duration {
        self.peer_moratorium_until
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    fn cfg(self_id: u16) -> PeerSamplerConfig {
        PeerSamplerConfig {
            self_id,
            peer_count: 2,
            peer_age_reachable: Duration::seconds(10),
            peer_age_replaceable: Duration::seconds(5),
            peer_replacement_probability: 0.5,
            peer_moratorium_range: Duration::seconds(1)..=Duration::seconds(1),
        }
    }

    #[test]
    fn observe_ignores_self_and_updates_existing_peer() {
        let mut local_cfg = cfg(7);
        local_cfg.peer_count = 1;
        let mut sampler = PeerSampler::new(local_cfg);
        let mut rng = SmallRng::seed_from_u64(0);
        sampler.observe(Duration::seconds(1), 7, &mut rng);
        assert!(sampler.peer_ids().is_empty());

        sampler.observe(Duration::seconds(1), 10, &mut rng);
        sampler.observe(Duration::seconds(4), 10, &mut rng);
        assert_eq!(vec![10], sampler.peer_ids());
        assert!(!sampler.needs_broadcast_bootstrap(Duration::seconds(6)));
    }

    #[test]
    fn observe_replaces_stale_peer_even_during_moratorium() {
        let mut sampler = PeerSampler::new(cfg(0));
        sampler.set_peers_for_test(vec![(1, Duration::ZERO), (2, Duration::seconds(9))]);
        sampler.set_moratorium_until_for_test(Duration::seconds(1000));
        let mut rng = SmallRng::seed_from_u64(0);

        sampler.observe(Duration::seconds(10), 3, &mut rng);

        let ids = sampler.peer_ids();
        assert!(ids.contains(&3));
        assert_eq!(2, ids.len());
    }

    #[test]
    fn observe_probabilistic_replacement_obeys_moratorium() {
        let mut local_cfg = cfg(0);
        local_cfg.peer_count = 1;
        local_cfg.peer_age_replaceable = Duration::seconds(100);
        local_cfg.peer_replacement_probability = 1.0;
        local_cfg.peer_moratorium_range = Duration::seconds(10)..=Duration::seconds(10);

        let mut sampler = PeerSampler::new(local_cfg);
        sampler.set_peers_for_test(vec![(1, Duration::ZERO)]);
        sampler.set_moratorium_until_for_test(Duration::seconds(5));
        let mut rng = SmallRng::seed_from_u64(0xBAD5_EED0);

        sampler.observe(Duration::seconds(1), 2, &mut rng);
        assert_eq!(vec![1], sampler.peer_ids());

        sampler.observe(Duration::seconds(6), 2, &mut rng);
        assert_eq!(vec![2], sampler.peer_ids());
        assert_eq!(Duration::seconds(16), sampler.moratorium_until_for_test());
    }

    #[test]
    fn sample_targets_respects_blacklist_outdegree_and_reachability() {
        let mut sampler = PeerSampler::new(cfg(0));
        sampler.set_peers_for_test(vec![(1, Duration::ZERO), (2, Duration::seconds(100)), (3, Duration::seconds(100))]);
        let mut rng = SmallRng::seed_from_u64(1);

        let targets = sampler.sample_targets(Duration::seconds(105), 3, &[2], &mut rng);

        assert_eq!(1, targets.len());
        assert_eq!(3, targets[0]);
    }

    #[test]
    fn needs_broadcast_bootstrap_is_true_for_incomplete_or_stale_sets() {
        let mut sampler = PeerSampler::new(cfg(0));
        assert!(sampler.needs_broadcast_bootstrap(Duration::ZERO));

        sampler.set_peers_for_test(vec![(1, Duration::seconds(10)), (2, Duration::seconds(10))]);
        assert!(!sampler.needs_broadcast_bootstrap(Duration::seconds(12)));
        assert!(sampler.needs_broadcast_bootstrap(Duration::seconds(30)));
    }
}
