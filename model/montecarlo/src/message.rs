#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GossipScope {
    Broadcast,
    Shard(u32),
}

#[derive(Debug, Clone)]
pub struct GossipMessage {
    sender_id: u16,
    scope: GossipScope,
    topic_hash: u64,
    topic_evictions: u16,
    topic_lage: i8,
}

impl GossipMessage {
    pub fn new(sender_id: u16, scope: GossipScope, topic_hash: u64, topic_evictions: u16, topic_lage: i8) -> Self {
        Self { sender_id, scope, topic_hash, topic_evictions, topic_lage }
    }

    pub fn sender_id(&self) -> u16 {
        self.sender_id
    }

    pub fn scope(&self) -> GossipScope {
        self.scope
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
}

/// The connectivity fabric of the simulator that implements message delivery with optional latency and loss.
pub trait Transmit {
    fn transmit_gossip(&mut self, message: GossipMessage);
    fn set_node_shards(&mut self, node_id: u16, shards: Vec<u32>);
}
