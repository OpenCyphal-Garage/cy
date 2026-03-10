#[derive(Debug, Clone)]
pub struct GossipMessage {
    sender_id: u16,

    /// Message propagation parameters for forwarding.
    ttl: u8,
    outdegree: u8,

    /// Gossiped topic details.
    topic_hash: u64,
    topic_evictions: u16,
    topic_lage: i8,
}

impl GossipMessage {
    pub fn new(sender_id: u16, ttl: u8, outdegree: u8, topic_hash: u64, topic_evictions: u16, topic_lage: i8) -> Self {
        Self { sender_id, ttl, outdegree, topic_hash, topic_evictions, topic_lage }
    }

    pub fn sender_id(&self) -> u16 {
        self.sender_id
    }

    pub fn ttl(&self) -> u8 {
        self.ttl
    }

    pub fn outdegree(&self) -> u8 {
        self.outdegree
    }

    pub fn topic_hash(&self) -> u64 {
        self.topic_hash
    }

    pub fn topic_evictions(&self) -> u16 {
        self.topic_evictions
    }

    pub fn topic_lage(&self) -> i8 {
        self.topic_lage
    }

    pub fn dedup_hash(&self) -> u64 {
        gossip_dedup_hash(self.topic_hash, self.topic_evictions, self.topic_lage)
    }
}

/// The connectivity fabric of the simulator that implements message delivery with optional latency and loss.
pub trait Transmit {
    fn unicast_gossip(&mut self, destination: u16, message: GossipMessage);
    fn broadcast_gossip(&mut self, message: GossipMessage);
}

pub fn gossip_dedup_hash(hash: u64, evictions: u16, lage: i8) -> u64 {
    let other = ((evictions as u64) << 16) | (((lage + 1) as u64) << 56);
    hash ^ other
}
