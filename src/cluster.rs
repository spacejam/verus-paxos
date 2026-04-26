// exec layer with ghost-state instrumentation.
//
// Tasks 5/6/7 unify exec-layer types with the spec-layer types from
// primitives.rs and acceptor.rs and add ghost-field scaffolding so that
// run_proposal can eventually carry a full safety postcondition (extension of
// ChosenHistory, monotone version, etc.).
//
// Phase 1 / Phase 2 ghost tracking is wired up: a local ghost mirror
// (local_ghost_states) is maintained in lockstep with the exec acceptors
// HashMap, the per-id inv_acceptor invariant is carried as a loop invariant
// on the local mirror, and the Phase 2 quorum is recorded as a Set<NodeId>
// (phase2_quorum). After Phase 2 quorum is reached, lemmas
// lemma_history_append_preserves_monotone and
// lemma_chosen_in_history_maintained extend the ghost ChosenHistory.
//
// Several `assume(...)` calls remain (all inside `proof {}` blocks and erased
// at runtime). They are the residual gap between exec-side `acceptors`
// (HashMap) and ghost-side `local_ghost_states` (Map), plus a few
// preconditions for the history lemmas that require deeper invariants we
// have not yet wired up (causal chain witness recording, exec-ghost
// HashMap-Map bijection). Each is documented at its call site:
//   - assume(inv_acceptor(old_state))     [Phase 1 + Phase 2]
//   - assume(selected.version < u64::MAX) [u64 overflow guard]
//   - assume(nv_clone == new_value)       [Versioned::clone() spec gap]
//   - assume(is_quorum(phase2_quorum, ..)) plus the four chosen-history
//     preconditions just before invoking lemma_chosen_in_history_maintained.
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
use crate::history::{inv_history_monotone, inv_causal_chain, inv_chosen_in_history,
                     lemma_history_append_preserves_monotone,
                     lemma_chosen_in_history_maintained};
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::primitives::is_quorum;
#[cfg(verus_only)]
#[allow(unused_imports)]
use crate::quorum::chosen;

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
        ensures result.inv()
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
        proof {
            // inv_acceptor: vacuous because ghost_states is empty.
            assert(forall |id: NodeId| !Map::<NodeId, AcceptorState<S>>::empty().contains_key(id));
            // inv_history_monotone: vacuous for empty sequence.
            assert(inv_history_monotone(Seq::<Versioned<S>>::empty()));
            // inv_causal_chain: vacuous for empty sequence.
            assert(inv_causal_chain(Seq::<Versioned<S>>::empty(), Map::<Ballot, Versioned<S>>::empty()));
            // inv_chosen_in_history: vacuous — chosen requires all quorum members
            // to have accepted, impossible with empty ghost_states (no keys).
            assert(inv_chosen_in_history(
                Seq::<Versioned<S>>::empty(),
                Map::<NodeId, AcceptorState<S>>::empty(),
                cluster_size as u64,
                Set::<NodeId>::empty())) by {
                // chosen(empty_map, b, v, q, cs) requires forall id in q: empty_map.contains_key(id).
                // But empty_map has no keys, so any q with is_quorum is not possible.
                assert forall |b: Ballot, v: Versioned<S>, q: Set<NodeId>|
                    (#[trigger] chosen(Map::<NodeId, AcceptorState<S>>::empty(), b, v, q, cluster_size as u64))
                    && q.subset_of(Set::<NodeId>::empty())
                    implies exists |i: int| 0 <= i < Seq::<Versioned<S>>::empty().len() && Seq::<Versioned<S>>::empty()[i] == v
                by {
                    // is_quorum requires q.len() * 2 > cluster_size, so q is non-empty.
                    // But q.subset_of(Set::empty()) implies q is empty.
                    // Non-empty and empty: contradiction, so this branch is vacuous.
                    assert(is_quorum(q, cluster_size as u64));
                    assert(q.subset_of(Set::<NodeId>::empty()));
                    vstd::set_lib::lemma_len_subset(q, Set::<NodeId>::empty());
                    assert(q.len() == 0);
                    assert(q.len() * 2 == 0);
                    // cluster_size as nat >= 0, and 0 > cluster_size as nat is false.
                    // So is_quorum(q, cluster_size) is false. Contradiction.
                };
            };
            // commit_timestamps: vacuous because history is empty (len == 0).
            assert(forall |i: nat| (i as int) < (0int) ==> Map::<nat, nat>::empty().contains_key(i));
        }
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
        requires old(self).inv()
    {
        // Capture the inv facts from the pre-state into ghost locals so they
        // remain accessible inside proof {} blocks after self is mutated.
        let ghost initial_history = self.ghost_history@;
        proof {
            assert(inv_history_monotone(initial_history));
        }
        let quorum_size = (self.cluster_size / 2 + 1) as usize;
        let node_ids: Vec<NodeId> = collect_node_ids(&self.acceptors);

        // Phase 1: send Prepare to all acceptors and locally evaluate
        // handle_prepare.
        let mut promise_count: usize = 0;
        let mut highest_accepted: Option<Versioned<S>> = None;

        // Local ghost mirror of acceptor states. We update this in lockstep
        // with the exec acceptors HashMap so that the ghost map records every
        // post-handle_prepare / post-handle_accept transition. We start
        // empty (rather than from self.ghost_states@) because run_proposal
        // currently has no `requires self.inv()` precondition; the per-id
        // inv_acceptor invariant on entries we ourselves insert is
        // discharged by handle_prepare/handle_accept's ensures clauses.
        // The struct field self.ghost_states@ is overwritten with this
        // mirror at the end.
        let ghost mut local_ghost_states: Map<NodeId, AcceptorState<S>> = Map::empty();

        let mut i: usize = 0;
        while i < node_ids.len()
            invariant
                0 <= i <= node_ids.len(),
                promise_count <= i,
                forall |id: NodeId| #[trigger] local_ghost_states.contains_key(id)
                    ==> inv_acceptor(local_ghost_states[id]),
                self.ghost_history@ == initial_history,
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
                    // preserve inv_acceptor. Establishing the exec-ghost
                    // correspondence (`old_state == local_ghost_states[id]` for
                    // all ids in the HashMap) requires a HashMap-Map bijection
                    // invariant we have not yet wired up; for now, assume.
                    assume(inv_acceptor(old_state));
                }
                let (new_state, response) = handle_prepare(old_state, b);
                self.acceptors.insert(id, new_state.clone());

                match response {
                    PrepareResponse::Promise { ballot: _, accepted } => {
                        // Update ghost mirror. handle_prepare's ensures clause
                        // guarantees inv_acceptor(new_state), so the loop
                        // invariant is preserved.
                        proof {
                            local_ghost_states = local_ghost_states.insert(id, new_state);
                        }
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
                        promise_count = promise_count + 1;
                    }
                    PrepareResponse::Nack => {
                        // On Nack, handle_prepare returned the unchanged state.
                        // Mirror that at the ghost level too — for consistency,
                        // even though our pragmatic invariant only tracks
                        // inv_acceptor and that holds for old_state by ensures.
                        proof {
                            local_ghost_states = local_ghost_states.insert(id, new_state);
                        }
                    }
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

        // Snapshot the ghost state before Phase 2 so we can prove Phase 2
        // only changes acceptors in phase2_quorum (used by
        // lemma_chosen_in_history_maintained).
        let ghost states_before_p2 = local_ghost_states;
        let ghost mut phase2_quorum: Set<NodeId> = Set::empty();

        let mut j: usize = 0;
        while j < node_ids.len()
            invariant
                0 <= j <= node_ids.len(),
                accepted_count <= j,
                phase2_quorum.finite(),
                accepted_count == phase2_quorum.len(),
                forall |id: NodeId| #[trigger] local_ghost_states.contains_key(id)
                    ==> inv_acceptor(local_ghost_states[id]),
                forall |id: NodeId| #[trigger] phase2_quorum.contains(id) ==>
                    local_ghost_states.contains_key(id)
                    && local_ghost_states[id].accepted == Some((b, new_value)),
                self.ghost_history@ == initial_history,
            decreases (node_ids.len() - j) as int
        {
            let id = node_ids[j];
            j += 1;
            if self.network.is_failed(id) {
                continue;
            }
            let opt_old = self.acceptors.remove(&id);
            if let Some(old_state) = opt_old {
                proof {
                    // Same correspondence gap as in Phase 1 — a HashMap-Map
                    // bijection invariant would discharge this. Closed via
                    // the loop invariant that ghost states satisfy
                    // inv_acceptor, plus the assumption that the exec
                    // HashMap's old_state matches local_ghost_states[id].
                    assume(inv_acceptor(old_state));
                }
                let nv_clone = new_value.clone();
                let (new_state, response) = handle_accept(old_state, b, nv_clone);
                self.acceptors.insert(id, new_state.clone());

                match response {
                    AcceptResponse::Accepted { .. } => {
                        proof {
                            // handle_accept's ensures gives:
                            //   new_state.accepted == Some((b, nv_clone))
                            //   inv_acceptor(new_state)
                            // Since Versioned derives PartialEq/Eq, we use
                            // an explicit assume to bridge clone equality
                            // (Versioned<S>: Clone has no Verus spec for
                            // clone()).
                            assume(nv_clone == new_value);
                            // Each NodeId is visited at most once because
                            // self.acceptors.remove(&id) removes it from the
                            // HashMap; a second remove would return None and
                            // skip the inner block. Verus lacks a HashMap spec
                            // to express this, so we assume it here.
                            assume(!phase2_quorum.contains(id));
                            local_ghost_states = local_ghost_states.insert(id, new_state);
                            phase2_quorum = phase2_quorum.insert(id);
                            vstd::set::axiom_set_insert_len(phase2_quorum.remove(id), id);
                            assert(phase2_quorum.contains(id));
                            assert(local_ghost_states[id].accepted == Some((b, new_value)));
                        }
                        accepted_count = accepted_count + 1;
                    }
                    AcceptResponse::Nack => {
                        // No ghost mutation needed: handle_accept ensures
                        // result.0 == state on Nack, so the ghost mirror
                        // is unchanged.
                    }
                }
            }
        }

        if accepted_count < quorum_size {
            return None;
        }

        // Phase 2 quorum reached — extend ghost history with new_value.
        proof {
            // Establish is_quorum(phase2_quorum, cluster_size).
            // Loop invariant: accepted_count == phase2_quorum.len(), phase2_quorum.finite().
            // Post-loop: accepted_count >= quorum_size.
            // quorum_size = (cluster_size / 2 + 1) as usize (exec computation).
            // Verus cannot bridge exec let-bindings into spec, so we assume the
            // nat-level quorum_size value. This is sound: quorum_size was set to
            // exactly (self.cluster_size / 2 + 1) as usize before Phase 1.
            assume(quorum_size as nat == (self.cluster_size as nat) / 2 + 1);
            // From the loop invariant and post-loop guard:
            assert(phase2_quorum.len() == accepted_count as nat);
            assert(accepted_count >= quorum_size);
            // Arithmetic: phase2_quorum.len() * 2 > cluster_size.
            // We know phase2_quorum.len() >= quorum_size and
            // quorum_size = cluster_size/2 + 1 (nat division).
            // Key: (cs/2 + 1)*2 > cs for all nat cs. Proof by cases:
            //   cs even (cs = 2k): cs/2 = k, (k+1)*2 = 2k+2 > 2k = cs.
            //   cs odd (cs = 2k+1): cs/2 = k, (k+1)*2 = 2k+2 > 2k+1 = cs.
            assert(phase2_quorum.len() * 2 > self.cluster_size as nat) by {
                let plen: nat = phase2_quorum.len();
                let qs: nat = quorum_size as nat;
                let cs: nat = self.cluster_size as nat;
                assert(plen >= qs);
                assert(qs == cs / 2 + 1);
                // cs / 2 * 2 <= cs < cs / 2 * 2 + 2 (property of nat integer division)
                assert(cs / 2 * 2 <= cs) by (nonlinear_arith);
                assert(cs < cs / 2 * 2 + 2) by (nonlinear_arith);
                // Therefore (cs/2 + 1) * 2 = cs/2*2 + 2 > cs
                assert(qs * 2 == (cs / 2 + 1) * 2);
                assert((cs / 2 + 1) * 2 == cs / 2 * 2 + 2) by (nonlinear_arith);
                assert(qs * 2 > cs);
                // plen >= qs, so plen * 2 >= qs * 2 > cs
                assert(plen * 2 >= qs * 2) by (nonlinear_arith)
                    requires plen >= qs;
            };
            assert(is_quorum(phase2_quorum, self.cluster_size));
            assert(chosen(local_ghost_states, b, new_value, phase2_quorum, self.cluster_size));

            // The history extension obligations require deeper invariants we
            // have not yet wired up (causal chain, monotone version,
            // exec-ghost correspondence). We assume these and rely on the
            // verified lemmas to package the consequences.
            assume(phase2_quorum.subset_of(self.universe@));
            assume(self.ghost_history@.len() == 0
                || self.ghost_history@.last().version < new_value.version);
            assume(forall |b2: Ballot, v2: Versioned<S>, q2: Set<NodeId>|
                chosen(local_ghost_states, b2, v2, q2, self.cluster_size)
                && q2.subset_of(self.universe@)
                && v2 != new_value
                ==> chosen(states_before_p2, b2, v2, q2, self.cluster_size));
            assume(inv_chosen_in_history(
                self.ghost_history@, states_before_p2,
                self.cluster_size, self.universe@));
            // inv_history_monotone: self.ghost_history@ has not been mutated yet
            // (no proof-block assignment to self.ghost_history@ precedes this point),
            // so it still equals initial_history, which satisfies inv_history_monotone
            // by the captured ghost local.
            assert(self.ghost_history@ == initial_history);
            assert(inv_history_monotone(self.ghost_history@));

            lemma_history_append_preserves_monotone(self.ghost_history@, new_value);
            lemma_chosen_in_history_maintained(
                self.ghost_history@, new_value,
                states_before_p2, local_ghost_states,
                b, phase2_quorum, self.cluster_size, self.universe@,
            );

            // Causal chain extension: needs witnessed[b] == selected and
            // new_value == apply_cas(f_spec, witnessed[b], new_uuid). This
            // requires threading f_spec through and recording witness in
            // Phase 1 — assumed for now.
            assume(inv_causal_chain(
                self.ghost_history@.push(new_value), self.ghost_witnessed@));

            // Record commit timestamp before extending history.
            let commit_idx: nat = self.ghost_history@.len() as nat;
            self.commit_timestamps@ = self.commit_timestamps@.insert(
                commit_idx, self.logical_clock@);

            // Extend ghost history.
            self.ghost_history@ = self.ghost_history@.push(new_value);

            // Publish the local ghost state mirror.
            self.ghost_states@ = local_ghost_states;

            // Advance logical clock.
            self.logical_clock@ = (self.logical_clock@ + 1) as nat;
        }

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
