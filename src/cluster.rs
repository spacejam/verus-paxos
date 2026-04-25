// exec
use std::collections::{HashMap, HashSet};
use crate::network::{SimNetwork, Message, Payload, NodeId};

// Concrete exec types (not the Verus spec types from acceptor.rs)
pub type Ballot = (u64, u64);           // (round, proposer_id)
pub type Versioned<S> = (u64, u128, S); // (version, uuid, state)

#[derive(Clone)]
pub struct AcceptorState<S: Clone> {
    pub promised: Option<Ballot>,
    pub accepted: Option<(Ballot, Versioned<S>)>,
}

impl<S: Clone> AcceptorState<S> {
    pub fn new() -> Self {
        AcceptorState { promised: None, accepted: None }
    }
}

pub struct CASPaxosCluster<S: Clone> {
    pub acceptors: HashMap<NodeId, AcceptorState<S>>,
    pub network: SimNetwork<S>,
    pub cluster_size: usize,
}

#[derive(Debug)]
pub enum ProposalError {
    Contention,
}

impl<S: Clone + std::fmt::Debug> CASPaxosCluster<S> {
    pub fn new(
        node_ids: Vec<NodeId>,
        drop_rate: f64,
        failed_nodes: HashSet<NodeId>,
        seed: u64,
    ) -> Self {
        let cluster_size = node_ids.len();
        let acceptors = node_ids.iter().map(|&id| (id, AcceptorState::new())).collect();
        CASPaxosCluster { acceptors, network: SimNetwork::new(drop_rate, failed_nodes, seed), cluster_size }
    }

    pub fn run_proposal(
        &mut self,
        proposer_id: NodeId,
        round: u64,
        f: impl Fn(S) -> S,
        init_value: Versioned<S>,
        new_uuid: u128,
    ) -> Result<Versioned<S>, ProposalError> {
        let ballot: Ballot = (round, proposer_id);
        let quorum_size = self.cluster_size / 2 + 1;
        let node_ids: Vec<NodeId> = self.acceptors.keys().cloned().collect();

        // Phase 1: send Prepare to all acceptors
        for &id in &node_ids {
            self.network.send(Message {
                from: proposer_id, to: id,
                payload: Payload::Prepare { ballot },
            });
        }

        // Process Phase 1 messages: acceptors handle Prepare, proposer collects Promises
        let mut phase1_msgs: Vec<Message<S>> = Vec::new();
        while let Some(m) = self.network.deliver_one() { phase1_msgs.push(m); }

        // Acceptors handle Prepare, send responses back into network
        for msg in &phase1_msgs {
            if let Payload::Prepare { ballot: b } = msg.payload {
                if let Some(state) = self.acceptors.get_mut(&msg.to) {
                    let promise = match state.promised {
                        None => { state.promised = Some(b); true }
                        Some(p) if p < b => { state.promised = Some(b); true }
                        _ => false,
                    };
                    let payload = if promise {
                        Payload::Promise { ballot: b, accepted: state.accepted.clone() }
                    } else {
                        Payload::Nack { ballot: b }
                    };
                    self.network.send(Message { from: msg.to, to: proposer_id, payload });
                }
            }
        }

        // Proposer collects Phase 1 responses
        let mut phase1_responses: Vec<Message<S>> = Vec::new();
        while let Some(m) = self.network.deliver_one() { phase1_responses.push(m); }

        let mut promises: Vec<Option<(Ballot, Versioned<S>)>> = Vec::new();
        for msg in &phase1_responses {
            if msg.to == proposer_id {
                if let Payload::Promise { accepted, .. } = &msg.payload {
                    promises.push(accepted.clone());
                }
            }
        }

        if promises.len() < quorum_size {
            return Err(ProposalError::Contention);
        }

        // select_value: pick highest-version accepted value, fallback to init_value
        let selected = promises.iter()
            .filter_map(|acc| acc.as_ref())
            .max_by_key(|(_, v)| v.0)
            .map(|(_, v)| v.clone())
            .unwrap_or(init_value);

        let new_value: Versioned<S> = (selected.0 + 1, new_uuid, f(selected.2.clone()));

        // Phase 2: send Accept to all acceptors
        for &id in &node_ids {
            self.network.send(Message {
                from: proposer_id, to: id,
                payload: Payload::Accept { ballot, value: new_value.clone() },
            });
        }

        // Acceptors handle Accept, send Accepted back
        let mut phase2_msgs: Vec<Message<S>> = Vec::new();
        while let Some(m) = self.network.deliver_one() { phase2_msgs.push(m); }

        for msg in &phase2_msgs {
            if let Payload::Accept { ballot: b, value: ref v } = msg.payload {
                if let Some(state) = self.acceptors.get_mut(&msg.to) {
                    let accept = match state.promised {
                        None => false,
                        Some(p) => p <= b,
                    };
                    if accept {
                        state.promised = Some(b);
                        state.accepted = Some((b, v.clone()));
                        self.network.send(Message {
                            from: msg.to, to: proposer_id,
                            payload: Payload::Accepted { ballot: b },
                        });
                    }
                }
            }
        }

        // Count Accepted responses
        let mut accepted_count = 0usize;
        while let Some(m) = self.network.deliver_one() {
            if m.to == proposer_id {
                if let Payload::Accepted { .. } = m.payload {
                    accepted_count += 1;
                }
            }
        }

        if accepted_count < quorum_size {
            return Err(ProposalError::Contention);
        }

        Ok(new_value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn single_proposal_commits() {
        let mut cluster = CASPaxosCluster::new(
            vec![1, 2, 3, 4, 5], 0.0, HashSet::new(), 42,
        );
        let init: Versioned<u64> = (0, 0, 0u64);
        let result = cluster.run_proposal(99, 1, |x| x + 1, init, 1234u128);
        assert!(result.is_ok());
        let v = result.unwrap();
        assert_eq!(v.0, 1);  // version incremented to 1
        assert_eq!(v.2, 1);  // state = 0 + 1
    }
}
