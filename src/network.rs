// exec
use std::collections::HashSet;

pub type NodeId = u64;

#[derive(Clone, Debug)]
pub struct Message<S: Clone> {
    pub from: NodeId,
    pub to: NodeId,
    pub payload: Payload<S>,
}

#[derive(Clone, Debug)]
pub enum Payload<S: Clone> {
    Prepare { ballot: (u64, u64) },
    Promise { ballot: (u64, u64), accepted: Option<((u64, u64), (u64, u128, S))> },
    Accept  { ballot: (u64, u64), value: (u64, u128, S) },
    Accepted { ballot: (u64, u64) },
    Nack    { ballot: (u64, u64) },
}

pub struct SimNetwork<S: Clone> {
    pub queue: Vec<Message<S>>,
    pub drop_rate: f64,
    pub failed_nodes: HashSet<NodeId>,
    rng_seed: u64,
}

impl<S: Clone> SimNetwork<S> {
    pub fn new(drop_rate: f64, failed_nodes: HashSet<NodeId>, seed: u64) -> Self {
        SimNetwork { queue: Vec::new(), drop_rate, failed_nodes, rng_seed: seed }
    }

    pub fn send(&mut self, msg: Message<S>) {
        if self.failed_nodes.contains(&msg.to) || self.failed_nodes.contains(&msg.from) {
            return;
        }
        if self.should_drop() {
            return;
        }
        self.queue.push(msg);
    }

    pub fn deliver_one(&mut self) -> Option<Message<S>> {
        if self.queue.is_empty() { return None; }
        Some(self.queue.remove(0))
    }

    fn should_drop(&mut self) -> bool {
        self.rng_seed = self.rng_seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = (self.rng_seed >> 33) as f64 / (u32::MAX as f64);
        r < self.drop_rate
    }
}
