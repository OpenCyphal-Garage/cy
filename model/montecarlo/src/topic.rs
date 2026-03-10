use std::cmp::min;
use std::time::Duration;

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
        self.origin = min(self.origin, now - lage_to_duration(lage));
    }

    pub fn subject_id(&self, modulus: u16) -> u16 {
        topic_subject_id(self.hash, self.evictions, modulus)
    }

    pub fn evictions(&self) -> u16 {
        self.evictions
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn evict(&mut self) {
        self.evictions = self.evictions.checked_add(1).expect("too many evictions");
    }
}

pub fn topic_subject_id(hash: u64, evictions: u16, modulus: u16) -> u16 {
    ((hash + (evictions as u64).pow(2)) % (modulus as u64)) as u16
}

pub fn left_wins_collision(local: &Topic, now: Duration, remote_lage: i8, remote_hash: u64) -> bool {
    let local_lage = local.lage(now);
    if local_lage != remote_lage { local_lage > remote_lage } else { local.hash < remote_hash }
}

/// lage is ⌊log₂(age in seconds)⌋, or -1 for age=0; range from -1 to about ~35.
pub fn lage_from_duration(duration: Duration) -> i8 {
    match duration.as_secs() {
        0 => -1,
        s => s.ilog2() as i8,
    }
}

pub fn lage_to_duration(lage: i8) -> Duration {
    match lage {
        ..0 => Duration::ZERO,
        63.. => Duration::MAX,
        v => Duration::from_secs(1_u64 << (v as u32)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lage_conversion_matches_model_examples() {
        assert_eq!(-1, lage_from_duration(Duration::ZERO));
        assert_eq!(0, lage_from_duration(Duration::from_secs(1)));
        assert_eq!(1, lage_from_duration(Duration::from_secs(2)));
        assert_eq!(1, lage_from_duration(Duration::from_secs(3)));
        assert_eq!(Duration::ZERO, lage_to_duration(-1));
        assert_eq!(Duration::from_secs(1), lage_to_duration(0));
        assert_eq!(Duration::from_secs(2), lage_to_duration(1));
        assert_eq!(Duration::from_secs(8), lage_to_duration(3));
    }

    #[test]
    fn topic_subject_id_uses_quadratic_probing() {
        assert_eq!(4, topic_subject_id(3, 1, 11));
        assert_eq!(4, topic_subject_id(4, 0, 11));
        assert_eq!(5, topic_subject_id(12, 2, 11));
    }
}
