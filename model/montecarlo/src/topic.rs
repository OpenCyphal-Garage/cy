use std::cmp::min;
use time::Duration;

#[derive(Debug, Clone)]
pub struct Topic {
    hash: u64,
    evictions: u16, // Large values imply convergence issues.
    origin: Duration,
}

impl Topic {
    pub fn new(hash: u64, origin: Duration) -> Self {
        Self { hash, evictions: 0, origin }
    }

    pub fn age(&self, now: Duration) -> Duration {
        now - self.origin
    }

    pub fn lage(&self, now: Duration) -> i8 {
        lage_from_duration(self.age(now))
    }

    /// Adjusts the local topic age estimate based on a received gossip. This implements lage propagation.
    pub fn merge_lage(&mut self, lage: i8, now: Duration) {
        let merged_origin = if lage >= 63 { Duration::MIN } else { now - lage_to_duration(lage) };
        self.origin = min(self.origin, merged_origin);
    }

    pub fn subject_id(&self, modulus: u32) -> u32 {
        topic_subject_id(self.hash, self.evictions, modulus)
    }

    pub fn evictions(&self) -> u16 {
        self.evictions
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn set_evictions(&mut self, evictions: u16) {
        self.evictions = evictions;
    }

    pub fn evict(&mut self) {
        self.evictions = self.evictions.checked_add(1).expect("too many evictions");
    }
}

pub fn topic_subject_id(hash: u64, evictions: u16, modulus: u32) -> u32 {
    ((hash + (evictions as u64).pow(2)) % (modulus as u64)) as u32
}

pub fn left_wins_collision(local: &Topic, now: Duration, remote_lage: i8, remote_hash: u64) -> bool {
    let local_lage = local.lage(now);
    if local_lage != remote_lage { local_lage > remote_lage } else { local.hash < remote_hash }
}

/// lage is ⌊log₂(age in seconds)⌋, or -1 for age=0; range from -1 to about ~35.
pub fn lage_from_duration(duration: Duration) -> i8 {
    match duration.whole_seconds() {
        ..=0 => -1,
        s => (s as u64).ilog2() as i8,
    }
}

pub fn lage_to_duration(lage: i8) -> Duration {
    match lage {
        ..0 => Duration::ZERO,
        63.. => Duration::MAX,
        v => Duration::seconds(1_i64 << (v as u32)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn topic_new_exposes_basic_properties() {
        let topic = Topic::new(0xDEAD_BEEF, Duration::seconds(5));
        assert_eq!(0xDEAD_BEEF, topic.hash());
        assert_eq!(0, topic.evictions());
    }

    #[test]
    fn topic_age_and_lage_follow_origin() {
        let topic = Topic::new(7, Duration::seconds(10));
        assert_eq!(Duration::seconds(5), topic.age(Duration::seconds(15)));
        assert_eq!(2, topic.lage(Duration::seconds(15))); // floor(log2(5))
    }

    #[test]
    fn merge_lage_prefers_older_origin() {
        let mut topic = Topic::new(1, Duration::seconds(10));
        topic.merge_lage(3, Duration::seconds(20)); // implies origin at 12s, newer than current
        assert_eq!(Duration::seconds(10), topic.age(Duration::seconds(20)));

        topic.merge_lage(4, Duration::seconds(20)); // implies origin at 4s, older than current
        assert_eq!(Duration::seconds(16), topic.age(Duration::seconds(20)));
    }

    #[test]
    fn merge_lage_handles_old_remote_without_underflow() {
        let mut topic = Topic::new(1, Duration::ZERO);
        topic.merge_lage(62, Duration::seconds(1));
        assert!(topic.age(Duration::seconds(1)) > Duration::ZERO);
    }

    #[test]
    fn evict_increments_counter_and_changes_subject() {
        let mut topic = Topic::new(3, Duration::ZERO);
        assert_eq!(0, topic.evictions());
        assert_eq!(3, topic.subject_id(11));
        topic.evict();
        assert_eq!(1, topic.evictions());
        assert_eq!(4, topic.subject_id(11));
    }

    #[test]
    fn set_evictions_overrides_counter() {
        let mut topic = Topic::new(3, Duration::ZERO);
        topic.evict();
        assert_eq!(1, topic.evictions());
        topic.set_evictions(7);
        assert_eq!(7, topic.evictions());
        assert_eq!(8, topic.subject_id(11));
    }

    #[test]
    fn left_wins_collision_prefers_higher_lage() {
        let local = Topic::new(10, Duration::seconds(2)); // age at t=10 is 8s => lage=3
        assert!(left_wins_collision(&local, Duration::seconds(10), 2, 1));
        assert!(!left_wins_collision(&local, Duration::seconds(10), 4, 1));
    }

    #[test]
    fn left_wins_collision_tiebreaks_on_hash() {
        let local_low = Topic::new(1, Duration::ZERO);
        let local_high = Topic::new(3, Duration::ZERO);
        assert!(left_wins_collision(&local_low, Duration::ZERO, -1, 2));
        assert!(!left_wins_collision(&local_high, Duration::ZERO, -1, 2));
    }

    #[test]
    fn lage_conversion_matches_model_examples() {
        assert_eq!(-1, lage_from_duration(Duration::ZERO));
        assert_eq!(-1, lage_from_duration(Duration::seconds(-1)));
        assert_eq!(0, lage_from_duration(Duration::seconds(1)));
        assert_eq!(1, lage_from_duration(Duration::seconds(2)));
        assert_eq!(1, lage_from_duration(Duration::seconds(3)));
        assert_eq!(Duration::ZERO, lage_to_duration(-1));
        assert_eq!(Duration::seconds(1), lage_to_duration(0));
        assert_eq!(Duration::seconds(2), lage_to_duration(1));
        assert_eq!(Duration::seconds(8), lage_to_duration(3));
        assert_eq!(Duration::MAX, lage_to_duration(63));
    }

    #[test]
    fn topic_subject_id_uses_quadratic_probing() {
        assert_eq!(4, topic_subject_id(3, 1, 11));
        assert_eq!(4, topic_subject_id(4, 0, 11));
        assert_eq!(5, topic_subject_id(12, 2, 11));
    }
}
