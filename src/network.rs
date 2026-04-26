// exec
#[allow(unused_imports)]
use vstd::prelude::*;
use std::collections::HashSet;
#[allow(unused_imports)]
use crate::primitives::{Ballot, Versioned};

pub use crate::primitives::NodeId;

verus! {

#[derive(Clone, Debug)]
pub struct Message<S: Clone> {
    pub from: NodeId,
    pub to: NodeId,
    pub payload: Payload<S>,
}

#[derive(Clone, Debug)]
pub enum Payload<S: Clone> {
    Prepare { ballot: Ballot },
    Promise { ballot: Ballot, accepted: Option<(Ballot, Versioned<S>)> },
    Accept  { ballot: Ballot, value: Versioned<S> },
    Accepted { ballot: Ballot },
    Nack    { ballot: Ballot },
}

pub struct SimNetwork<S: Clone> {
    pub queue: Vec<Message<S>>,
    pub drop_rate: f64,
    pub failed_nodes: HashSet<NodeId>,
    rng_seed: u64,
}

impl<S: Clone> SimNetwork<S> {
    #[verifier::external_body]
    pub fn new(drop_rate: f64, failed_nodes: HashSet<NodeId>, seed: u64) -> Self {
        SimNetwork { queue: Vec::new(), drop_rate, failed_nodes, rng_seed: seed }
    }

    #[verifier::external_body]
    pub fn send(&mut self, msg: Message<S>) {
        if self.failed_nodes.contains(&msg.to) || self.failed_nodes.contains(&msg.from) {
            return;
        }
        if self.should_drop() {
            return;
        }
        self.queue.push(msg);
    }

    #[verifier::external_body]
    pub fn is_failed(&self, id: NodeId) -> bool {
        self.failed_nodes.contains(&id)
    }

    #[verifier::external_body]
    pub fn deliver_one(&mut self) -> Option<Message<S>> {
        if self.queue.is_empty() { return None; }
        Some(self.queue.remove(0))
    }

    #[verifier::external_body]
    fn should_drop(&mut self) -> bool {
        self.rng_seed = self.rng_seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = (self.rng_seed >> 33) as f64 / (u32::MAX as f64);
        r < self.drop_rate
    }
}

} // verus!
