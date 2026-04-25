#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::primitives::*;
#[allow(unused_imports)]
use crate::acceptor::*;
#[allow(unused_imports)]
use crate::quorum::*;

verus! {

// ChosenHistory: ghost-only, never in exec memory.
// A sequence of Versioned<S> values chosen across completed rounds, in ascending version order.
pub type ChosenHistory<S> = Seq<Versioned<S>>;

// WitnessedValues: ghost map from ballot to the highest-versioned value a proposer
// observed in Phase 1 for that ballot. Keyed by Ballot (not ProposerId) because one
// proposer may run multiple rounds at different ballots, each with an independent witness.
pub type WitnessedValues<S> = Map<Ballot, Versioned<S>>;

// INV_HISTORY_MONOTONE: version numbers in the history are strictly increasing.
pub open spec fn inv_history_monotone<S>(h: ChosenHistory<S>) -> bool {
    forall |i: int, j: int| 0 <= i < j < h.len() ==> h[i].version < h[j].version
}

// INV_CAUSAL_CHAIN: each committed value after the first was produced by apply_cas
// applied to the Phase 1 witness (which may be uncommitted) for that round's proposer.
pub open spec fn inv_causal_chain<S>(h: ChosenHistory<S>, witnessed: WitnessedValues<S>) -> bool {
    forall |i: int| 0 < i < h.len() ==>
        exists |b: Ballot, f: spec_fn(S) -> S, new_uuid: Uuid|
            witnessed.contains_key(b)
            && witnessed[b].version == h[i].version - 1
            && (#[trigger] h[i]) == apply_cas(f, witnessed[b], new_uuid)
}

// CommitTimestamps: ghost map from history index to the logical-clock step at which
// that value was committed (Phase 2 quorum reached). Defined here alongside the other
// ghost history types; used in linearizability.rs (is_valid_linearization) and
// cluster.rs (run_proposal postcondition).
pub type CommitTimestamps = Map<nat, nat>;

/// Every quorum-chosen value appears in ChosenHistory.
/// Bridge invariant connecting the snapshot `chosen` predicate to ChosenHistory.
pub open spec fn inv_chosen_in_history<S>(
    h: ChosenHistory<S>,
    states: Map<NodeId, AcceptorState<S>>,
    cluster_size: u64,
    universe: Set<NodeId>,
) -> bool {
    forall |b: Ballot, v: Versioned<S>, q: Set<NodeId>|
        (#[trigger] chosen(states, b, v, q, cluster_size)) && q.subset_of(universe)
        ==> exists |i: int| 0 <= i < h.len() && h[i] == v
}

pub proof fn lemma_chosen_in_history_maintained<S>(
    h: ChosenHistory<S>,
    v: Versioned<S>,
    states_old: Map<NodeId, AcceptorState<S>>,
    states_new: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    q: Set<NodeId>,
    cluster_size: u64,
    universe: Set<NodeId>,
)
    requires
        inv_chosen_in_history(h, states_old, cluster_size, universe),
        inv_history_monotone(h),
        chosen(states_new, b, v, q, cluster_size),
        q.subset_of(universe),
        h.len() > 0 ==> h.last().version < v.version,
        // Any value chosen in states_new other than v was also chosen in states_old.
        forall |b2: Ballot, v2: Versioned<S>, q2: Set<NodeId>|
            chosen(states_new, b2, v2, q2, cluster_size) && q2.subset_of(universe) && v2 != v
            ==> chosen(states_old, b2, v2, q2, cluster_size),
    ensures
        inv_chosen_in_history(h.push(v), states_new, cluster_size, universe)
{
    assert forall |b2: Ballot, v2: Versioned<S>, q2: Set<NodeId>|
        #[trigger] chosen(states_new, b2, v2, q2, cluster_size) && q2.subset_of(universe)
        implies exists |i: int| 0 <= i < h.push(v).len() && h.push(v)[i] == v2
    by {
        if v2 == v {
            assert(h.push(v)[h.len() as int] == v);
        } else {
            let idx = choose |i: int| 0 <= i < h.len() && h[i] == v2;
            assert(h.push(v)[idx] == h[idx]);
        }
    }
}

pub proof fn lemma_history_append_preserves_monotone<S>(
    h: ChosenHistory<S>,
    v: Versioned<S>,
)
    requires
        inv_history_monotone(h),
        h.len() > 0 ==> h.last().version < v.version,
    ensures
        inv_history_monotone(h.push(v))
{
    assert(inv_history_monotone(h));
    assert forall |i: int, j: int|
        0 <= i < j < h.push(v).len() implies h.push(v)[i].version < h.push(v)[j].version
    by {
        if j == h.push(v).len() - 1 {
            if i < h.len() {
                assert(h.push(v)[i] == h[i]);
                assert(h.push(v)[j] == v);
                if h.len() == 1 {
                    assert(i == 0);
                    assert(h[i] == h.last());
                    assert(h[i].version < v.version);
                } else {
                    // h[i].version < h.last().version < v.version
                    assert(h[i].version <= h.last().version) by {
                        if i == h.len() - 1 {
                            // h[i] == h.last()
                        } else {
                            // i < h.len() - 1 < j, all in h, use IH on h
                            assert(h[i].version < h[h.len() - 1].version);
                        }
                    }
                    assert(h[i].version < v.version);
                }
            }
        }
        // Cases where both i and j are in h are covered by inv_history_monotone(h)
    };
}

pub proof fn lemma_history_append_preserves_causal_chain<S>(
    h: ChosenHistory<S>,
    v: Versioned<S>,
    witnessed: WitnessedValues<S>,
    b: Ballot,
    f: spec_fn(S) -> S,
)
    requires
        inv_causal_chain(h, witnessed),
        h.len() > 0 ==> witnessed.contains_key(b) && witnessed[b].version == h.last().version,
        v == apply_cas(f, witnessed[b], v.uuid),
        h.len() > 0 ==> witnessed[b].version == v.version - 1,
    ensures
        inv_causal_chain(h.push(v), witnessed)
{
    assert forall |i: int| 0 < i < h.push(v).len() implies
        exists |rb: Ballot, rf: spec_fn(S) -> S, ru: Uuid|
            witnessed.contains_key(rb)
            && witnessed[rb].version == h.push(v)[i].version - 1
            && (#[trigger] h.push(v)[i]) == apply_cas(rf, witnessed[rb], ru)
    by {
        if i < h.len() {
            assert(h.push(v)[i] == h[i]);
            // Existing entries satisfy inv_causal_chain(h, witnessed) already
        } else {
            // i == h.push(v).len() - 1, the newly appended entry
            assert(h.push(v)[i] == v);
            assert(witnessed.contains_key(b));
            assert(witnessed[b].version == v.version - 1);
            assert(v == apply_cas(f, witnessed[b], v.uuid));
        }
    };
}

} // verus!
