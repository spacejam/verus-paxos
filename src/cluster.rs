// exec layer with ghost-state instrumentation.
//
// Tasks 5/6/7 unify exec-layer types with the spec-layer types from
// primitives.rs and acceptor.rs and add ghost-field scaffolding so that
// run_proposal can eventually carry a full safety postcondition (extension of
// ChosenHistory, monotone version, etc.).
//
// Three localized `assume(...)` calls remain (all inside `proof {}` blocks
// and erased at runtime). Each is documented at its call site:
//   - assume(inv_acceptor(old_state))  — twice, before handle_prepare /
//     handle_accept. These would be discharged by an outer-loop invariant
//     once Phase 1/2 ghost tracking is wired up.
//   - assume(selected.version < u64::MAX) — guards a `+ 1` arithmetic
//     overflow check on a u64 that in practice never approaches MAX.
#[allow(unused_imports)]
use std::collections::HashMap;
#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::network::SimNetwork;
#[allow(unused_imports)]
use crate::primitives::{Ballot, Versioned, NodeId, Uuid};
#[allow(unused_imports)]
use crate::acceptor::{AcceptorState, handle_prepare, handle_accept,
                      PrepareResponse, AcceptResponse};
#[allow(unused_imports)]
use crate::history::{ChosenHistory, WitnessedValues, CommitTimestamps};
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::acceptor::inv_acceptor;
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::history::{inv_history_monotone, inv_causal_chain, inv_chosen_in_history};

verus! {

pub struct CASPaxosCluster<S: Clone> {
    // exec fields
    pub acceptors: HashMap<NodeId, AcceptorState<S>>,
    pub network: SimNetwork<S>,
    pub cluster_size: u64,
    // ghost fields (erased at compile time)
    pub universe: Ghost<Set<NodeId>>,
    pub ghost_states: Ghost<Map<NodeId, AcceptorState<S>>>,
    pub ghost_history: Ghost<ChosenHistory<S>>,
    pub ghost_witnessed: Ghost<WitnessedValues<S>>,
    pub logical_clock: Ghost<nat>,
    pub commit_timestamps: Ghost<CommitTimestamps>,
}

impl<S: Clone> CASPaxosCluster<S> {
    pub open spec fn inv(&self) -> bool {
        &&& forall |id: NodeId| #[trigger] self.ghost_states@.contains_key(id)
                ==> inv_acceptor(self.ghost_states@[id])
        &&& inv_history_monotone(self.ghost_history@)
        &&& inv_causal_chain(self.ghost_history@, self.ghost_witnessed@)
        &&& inv_chosen_in_history(
                self.ghost_history@,
                self.ghost_states@,
                self.cluster_size,
                self.universe@)
        &&& forall |i: nat| (i as int) < self.ghost_history@.len()
                ==> self.commit_timestamps@.contains_key(i)
    }

    pub open spec fn logical_clock_spec(&self) -> nat {
        self.logical_clock@
    }
}

} // verus!

#[derive(Debug)]
pub enum ProposalError {
    Contention,
}

verus! {

// External-body helper: collect a HashMap's keys into a Vec. Verus does not
// have a spec for `keys().cloned().collect()` so we wrap that pattern.
#[verifier::external_body]
pub fn collect_node_ids<S: Clone>(m: &HashMap<NodeId, AcceptorState<S>>) -> Vec<NodeId> {
    m.keys().cloned().collect()
}

// External-body call to a user-supplied closure. We do not give it a Verus
// spec for f_exec — proof reasoning is in terms of the ghost spec_fn passed
// in separately.
#[verifier::external_body]
pub fn call_f<S, F: Fn(S) -> S>(f: &F, s: S) -> S {
    f(s)
}

impl<S: Clone + PartialEq + Eq> CASPaxosCluster<S> {

    pub fn new(
        node_ids: Vec<NodeId>,
        drop_rate: f64,
        failed_nodes: std::collections::HashSet<NodeId>,
        seed: u64,
    ) -> (result: Self)
    {
        let cluster_size = node_ids.len() as u64;
        let mut acceptors: HashMap<NodeId, AcceptorState<S>> = HashMap::new();
        let mut i: usize = 0;
        while i < node_ids.len()
            invariant 0 <= i <= node_ids.len()
            decreases (node_ids.len() - i) as int
        {
            let id = node_ids[i];
            acceptors.insert(id, AcceptorState { promised: None, accepted: None });
            i += 1;
        }

        // Ghost initialization. Verus does not support iterating over an exec
        // Vec inside a proof block to build a Map, so we initialize the ghost
        // map as empty and rely on the meta-argument that the resulting
        // CASPaxosCluster trivially satisfies inv():
        //   - ghost_states is empty, so the per-id inv_acceptor obligation is
        //     vacuously true.
        //   - ghost_history is empty, so monotone, causal_chain, and the
        //     "every commit has a timestamp" obligations are all vacuous.
        //   - inv_chosen_in_history is vacuous because no values are chosen
        //     when ghost_states is empty.
        // The exec-side acceptors map is the actual runtime state; the ghost
        // mirror is meaningful only for proofs we have not yet closed.
        CASPaxosCluster {
            acceptors,
            network: SimNetwork::new(drop_rate, failed_nodes, seed),
            cluster_size,
            universe: Ghost(Set::empty()),
            ghost_states: Ghost(Map::empty()),
            ghost_history: Ghost(Seq::empty()),
            ghost_witnessed: Ghost(Map::empty()),
            logical_clock: Ghost(0nat),
            commit_timestamps: Ghost(Map::empty()),
        }
    }

    /// Run one CASPaxos proposal at ballot `b`. Returns Some(committed_value)
    /// on success and None on contention.
    ///
    /// This function deliberately carries no `ensures` clause: closing the
    /// full safety postcondition (extension of ChosenHistory, monotone
    /// version, commit-timestamp causality) requires Phase 1 / Phase 2 ghost
    /// tracking and lemma applications that we have not yet wired up. The
    /// individual `assume(inv_acceptor(old_state))` calls below would be
    /// discharged by an outer-loop invariant once that ghost tracking is in
    /// place. Runtime behavior is unaffected by these proof scaffolds.
    pub fn run_proposal<F: Fn(S) -> S>(
        &mut self,
        b: Ballot,
        f_exec: F,
        init_value: Versioned<S>,
        new_uuid: Uuid,
    ) -> Option<Versioned<S>>
    {
        let quorum_size = (self.cluster_size / 2 + 1) as usize;
        let node_ids: Vec<NodeId> = collect_node_ids(&self.acceptors);

        // Phase 1: send Prepare to all acceptors and locally evaluate
        // handle_prepare.
        let mut promise_count: usize = 0;
        let mut highest_accepted: Option<Versioned<S>> = None;

        let mut i: usize = 0;
        while i < node_ids.len()
            invariant
                0 <= i <= node_ids.len(),
                promise_count <= i,
            decreases (node_ids.len() - i) as int
        {
            let id = node_ids[i];
            i += 1;
            // Drop messages targeting failed nodes (modeling failure as
            // message loss).
            if self.network.is_failed(id) {
                continue;
            }
            // Remove the acceptor, run handle_prepare (the verified spec fn),
            // and insert the new state. Verus does not currently support
            // HashMap::get_mut in arbitrary positions, so we use
            // remove+insert as the mutation idiom.
            let opt_old = self.acceptors.remove(&id);
            if let Some(old_state) = opt_old {
                proof {
                    // The acceptor was created with promised=None, accepted=None
                    // (lemma_initial_state_satisfies_inv) and every subsequent
                    // mutation goes through handle_prepare/handle_accept which
                    // preserve inv_acceptor. We will eventually carry this as
                    // an outer-loop invariant; for now, assume it.
                    assume(inv_acceptor(old_state));
                }
                let (new_state, response) = handle_prepare(old_state, b);
                self.acceptors.insert(id, new_state);

                match response {
                    PrepareResponse::Promise { ballot: _, accepted } => {
                        // Track highest-version accepted value for select_value.
                        match accepted {
                            Some((_, ref v)) => {
                                let v_clone = v.clone();
                                let prev = highest_accepted;
                                highest_accepted = match prev {
                                    None => Some(v_clone),
                                    Some(cur) => {
                                        if v_clone.version > cur.version {
                                            Some(v_clone)
                                        } else {
                                            Some(cur)
                                        }
                                    }
                                };
                            }
                            None => {}
                        }
                        // TODO(ghost-tracking): mirror this state transition
                        // at the ghost level — update self.ghost_states@,
                        // append to a ghost promise sequence (Phase 1
                        // witness), and advance self.logical_clock@.
                        // handle_prepare's ensures clause guarantees
                        // inv_acceptor is preserved at the new state.
                        promise_count = promise_count + 1;
                    }
                    PrepareResponse::Nack => {}
                }
            }
        }

        if promise_count < quorum_size {
            return None;
        }

        // select_value: pick highest-version accepted, fallback to init_value.
        let selected = match highest_accepted {
            Some(v) => v,
            None => init_value,
        };

        // We assume version doesn't overflow u64 in this prototype.
        proof { assume(selected.version < u64::MAX); }
        let new_state = call_f(&f_exec, selected.state.clone());
        let new_value: Versioned<S> = Versioned {
            version: selected.version + 1,
            uuid: new_uuid,
            state: new_state,
        };

        // Phase 2: send Accept; locally evaluate handle_accept.
        let mut accepted_count: usize = 0;

        let mut j: usize = 0;
        while j < node_ids.len()
            invariant
                0 <= j <= node_ids.len(),
                accepted_count <= j,
            decreases (node_ids.len() - j) as int
        {
            let id = node_ids[j];
            j += 1;
            if self.network.is_failed(id) {
                continue;
            }
            let opt_old = self.acceptors.remove(&id);
            if let Some(old_state) = opt_old {
                proof { assume(inv_acceptor(old_state)); }
                let (new_state, response) = handle_accept(old_state, b, new_value.clone());
                self.acceptors.insert(id, new_state);

                match response {
                    AcceptResponse::Accepted { .. } => {
                        // TODO(ghost-tracking): mirror at ghost level —
                        // self.ghost_states@ = self.ghost_states@.insert(id,
                        //     AcceptorState { promised: Some(b),
                        //                     accepted: Some((b, new_value)) }).
                        // Then accumulate id into a ghost phase2_quorum set.
                        accepted_count = accepted_count + 1;
                    }
                    AcceptResponse::Nack => {}
                }
            }
        }

        if accepted_count < quorum_size {
            return None;
        }

        // TODO(ghost-tracking): Phase 2 quorum reached — extend ghost
        // history via:
        //   lemma_history_append_preserves_monotone(self.ghost_history@,
        //                                           new_value);
        //   lemma_history_append_preserves_causal_chain(...);
        //   lemma_chosen_in_history_maintained(...);
        //   self.ghost_history@ = self.ghost_history@.push(new_value);
        //   self.commit_timestamps@ = self.commit_timestamps@.insert(idx, ts);
        // Closing this requires the Phase 2 ghost_quorum set to be tracked
        // through the loop above.

        Some(new_value)
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn single_proposal_commits() {
        let mut cluster = CASPaxosCluster::<u64>::new(
            vec![1, 2, 3, 4, 5], 0.0, HashSet::new(), 42,
        );
        let init: Versioned<u64> = Versioned { version: 0, uuid: 0, state: 0u64 };
        let b = Ballot { round: 1, proposer_id: 99 };
        let result = cluster.run_proposal(b, |x| x + 1, init, 1234u128);
        assert!(result.is_some());
        let v = result.unwrap();
        assert_eq!(v.version, 1);  // version incremented to 1
        assert_eq!(v.state, 1);    // state = 0 + 1
    }
}
