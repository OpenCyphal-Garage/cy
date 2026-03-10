use crate::message::gossip_dedup_hash;
use time::Duration;

#[derive(Debug, Clone)]
pub struct GossipDedupConfig {
    pub capacity: usize,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
struct GossipDedupEntry {
    hash: u64,
    last_seen: Duration,
}

pub struct GossipDedup {
    entries: Vec<GossipDedupEntry>,
    cfg: GossipDedupConfig,
}

impl GossipDedup {
    pub fn new(cfg: GossipDedupConfig) -> Self {
        Self { entries: Vec::new(), cfg }
    }

    pub fn should_forward_hash(&mut self, now: Duration, hash: u64, ttl: u8) -> bool {
        if self.cfg.capacity == 0 {
            return ttl > 0;
        }
        let stale_before = now - self.cfg.timeout;
        if let Some(entry) = self.entries.iter_mut().find(|entry| entry.hash == hash) {
            let fresh = entry.last_seen < stale_before;
            entry.last_seen = now;
            return fresh && (ttl > 0);
        }
        self.touch_hash(now, hash);
        ttl > 0
    }

    pub fn touch_hash(&mut self, now: Duration, hash: u64) {
        if self.cfg.capacity == 0 {
            return;
        }
        if let Some(entry) = self.entries.iter_mut().find(|entry| entry.hash == hash) {
            entry.last_seen = now;
            return;
        }
        if self.entries.len() < self.cfg.capacity {
            self.entries.push(GossipDedupEntry { hash, last_seen: now });
            return;
        }
        let oldest_index = self
            .entries
            .iter()
            .enumerate()
            .min_by_key(|(_, entry)| entry.last_seen)
            .map(|(index, _)| index)
            .expect("dedup cache cannot be empty when replacing LRU entry");
        self.entries[oldest_index] = GossipDedupEntry { hash, last_seen: now };
    }

    pub fn touch_gossip(&mut self, now: Duration, topic_hash: u64, topic_evictions: u16, topic_lage: i8) {
        self.touch_hash(now, gossip_dedup_hash(topic_hash, topic_evictions, topic_lage));
    }

    #[cfg(test)]
    pub(crate) fn hashes_for_test(&self) -> Vec<u64> {
        self.entries.iter().map(|entry| entry.hash).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_dedup(capacity: usize, timeout: Duration) -> GossipDedup {
        GossipDedup::new(GossipDedupConfig { capacity, timeout })
    }

    #[test]
    fn should_forward_first_seen_and_suppress_recent_duplicates() {
        let mut dedup = make_dedup(4, Duration::seconds(5));

        assert!(dedup.should_forward_hash(Duration::seconds(1), 10, 3));
        assert!(!dedup.should_forward_hash(Duration::seconds(2), 10, 3));
        assert!(!dedup.should_forward_hash(Duration::seconds(2), 10, 0));
    }

    #[test]
    fn should_forward_again_after_timeout() {
        let mut dedup = make_dedup(4, Duration::seconds(5));

        assert!(dedup.should_forward_hash(Duration::seconds(1), 10, 3));
        assert!(!dedup.should_forward_hash(Duration::seconds(4), 10, 3));
        assert!(dedup.should_forward_hash(Duration::seconds(10), 10, 3));
    }

    #[test]
    fn ttl_zero_never_forwards_but_still_updates_cache() {
        let mut dedup = make_dedup(4, Duration::seconds(5));

        assert!(!dedup.should_forward_hash(Duration::seconds(1), 10, 0));
        assert_eq!(vec![10], dedup.hashes_for_test());
        assert!(!dedup.should_forward_hash(Duration::seconds(2), 10, 3));
    }

    #[test]
    fn capacity_zero_disables_caching() {
        let mut dedup = make_dedup(0, Duration::seconds(5));

        assert!(dedup.should_forward_hash(Duration::seconds(1), 10, 1));
        assert!(dedup.should_forward_hash(Duration::seconds(2), 10, 1));
        assert!(dedup.hashes_for_test().is_empty());
    }

    #[test]
    fn touch_hash_replaces_oldest_entry_when_full() {
        let mut dedup = make_dedup(2, Duration::seconds(10));

        dedup.touch_hash(Duration::seconds(1), 1);
        dedup.touch_hash(Duration::seconds(2), 2);
        dedup.touch_hash(Duration::seconds(3), 3);

        let hashes = dedup.hashes_for_test();
        assert_eq!(2, hashes.len());
        assert!(hashes.contains(&2));
        assert!(hashes.contains(&3));
    }

    #[test]
    fn touch_gossip_uses_consistent_key_derivation() {
        let mut dedup = make_dedup(4, Duration::seconds(5));

        dedup.touch_gossip(Duration::seconds(1), 0xDEAD_BEEF, 3, 4);

        let expected = gossip_dedup_hash(0xDEAD_BEEF, 3, 4);
        assert_eq!(vec![expected], dedup.hashes_for_test());
    }
}
