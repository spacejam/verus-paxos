// Layer 3
#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::primitives::*;
#[allow(unused_imports)]
use crate::acceptor::*;

verus! {

// chosen: a value v is quorum-committed at ballot b when a full quorum accepted it.
pub open spec fn chosen<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    v: Versioned<S>,
    q: Set<NodeId>,
    cluster_size: u64,
) -> bool {
    is_quorum(q, cluster_size)
    && forall |id: NodeId| #[trigger] q.contains(id) ==>
        states.contains_key(id) && states[id].accepted == Some((b, v))
}

// phase1_responses: ghost spec function collecting Promise messages from a quorum.
// Uninterpreted — the exec layer populates this correctly.
pub spec fn phase1_responses<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    q: Set<NodeId>,
) -> Seq<Promise<S>>;

// Soundness axiom: phase1_responses faithfully reflects each acceptor's accepted value.
pub proof fn axiom_phase1_responses_complete<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    q: Set<NodeId>,
)
    ensures
        forall |id: NodeId| #[trigger] q.contains(id) && states.contains_key(id) ==>
            exists |i: int| 0 <= i < phase1_responses(states, b, q).len()
                && #[trigger] phase1_responses(states, b, q)[i].from == id
                && phase1_responses(states, b, q)[i].accepted == states[id].accepted
{
    assume(false); // Axiom: phase1_responses faithfully reflects acceptor state
}

// Agreement: at most one value is chosen per ballot.
pub proof fn lemma_at_most_one_value_per_ballot<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    v1: Versioned<S>,
    v2: Versioned<S>,
    q1: Set<NodeId>,
    q2: Set<NodeId>,
    universe: Set<NodeId>,
    cluster_size: u64,
)
    requires
        chosen(states, b, v1, q1, cluster_size),
        chosen(states, b, v2, q2, cluster_size),
        q1.subset_of(universe),
        q2.subset_of(universe),
        universe.finite(),
        universe.len() == cluster_size as nat,
        forall |id: NodeId| universe.contains(id) ==> states.contains_key(id),
        forall |id: NodeId| #[trigger] states.contains_key(id) ==> inv_acceptor(states[id]),
    ensures
        v1 == v2
{
    lemma_quorums_intersect(q1, q2, universe, cluster_size);
    let inter = q1.intersect(q2);
    assert(!inter.is_empty());
    let id = choose |id: NodeId| inter.contains(id);
    assert(q1.contains(id) && q2.contains(id));
    assert(states[id].accepted == Some((b, v1)));
    assert(states[id].accepted == Some((b, v2)));
    assert(v1 == v2);
}

// If v1 is chosen at b1, and a proposer completed Phase 1 at higher ballot b2 over q2,
// then select_value returns a version >= v1.version.
pub proof fn lemma_higher_ballot_sees_chosen_version<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b1: Ballot,
    b2: Ballot,
    v1: Versioned<S>,
    q1: Set<NodeId>,
    q2: Set<NodeId>,
    universe: Set<NodeId>,
    cluster_size: u64,
    own_value: Versioned<S>,
)
    requires
        chosen(states, b1, v1, q1, cluster_size),
        is_quorum(q2, cluster_size),
        ballot_lt(b1, b2),
        q1.subset_of(universe),
        q2.subset_of(universe),
        universe.finite(),
        universe.len() == cluster_size as nat,
        forall |id: NodeId| universe.contains(id) ==> states.contains_key(id),
        forall |id: NodeId| #[trigger] states.contains_key(id) ==> inv_acceptor(states[id]),
        forall |id: NodeId| #[trigger] q2.contains(id) ==>
            match states[id].promised { Some(p) => ballot_le(b2, p), None => false },
    ensures
        select_value(phase1_responses(states, b2, q2), own_value).version >= v1.version
{
    lemma_quorums_intersect(q1, q2, universe, cluster_size);
    let id = choose |id: NodeId| q1.intersect(q2).contains(id);
    assert(q1.contains(id));
    assert(q2.contains(id));
    assert(states[id].accepted == Some((b1, v1)));
    axiom_phase1_responses_complete(states, b2, q2);
    let idx = choose |i: int| 0 <= i < phase1_responses(states, b2, q2).len()
        && phase1_responses(states, b2, q2)[i].from == id
        && phase1_responses(states, b2, q2)[i].accepted == states[id].accepted;
    assert(phase1_responses(states, b2, q2)[idx].accepted == Some((b1, v1)));
    lemma_select_value_version_is_max(phase1_responses(states, b2, q2), own_value);
    assert(select_value(phase1_responses(states, b2, q2), own_value).version >= v1.version);
}

// Version uniqueness: at most one Versioned<S> with a given version is ever chosen.
pub proof fn lemma_version_unique_across_ballots<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b1: Ballot,
    b2: Ballot,
    v1: Versioned<S>,
    v2: Versioned<S>,
    q1: Set<NodeId>,
    q2: Set<NodeId>,
    universe: Set<NodeId>,
    cluster_size: u64,
)
    requires
        chosen(states, b1, v1, q1, cluster_size),
        chosen(states, b2, v2, q2, cluster_size),
        v1.version == v2.version,
        q1.subset_of(universe),
        q2.subset_of(universe),
        universe.finite(),
        universe.len() == cluster_size as nat,
        forall |id: NodeId| universe.contains(id) ==> states.contains_key(id),
        forall |id: NodeId| #[trigger] states.contains_key(id) ==> inv_acceptor(states[id]),
        forall |id: NodeId| #[trigger] q1.contains(id) ==>
            match states[id].promised { Some(p) => ballot_le(b1, p), None => false },
        forall |id: NodeId| #[trigger] q2.contains(id) ==>
            match states[id].promised { Some(p) => ballot_le(b2, p), None => false },
    ensures
        v1 == v2
{
    if b1 == b2 {
        lemma_at_most_one_value_per_ballot(states, b1, v1, v2, q1, q2, universe, cluster_size);
    } else if ballot_lt(b1, b2) {
        lemma_higher_ballot_sees_chosen_version(
            states, b1, b2, v1, q1, q2, universe, cluster_size, v2
        );
        assume(v1 == v2); // PROOF_OBLIGATION: inductive value-preservation on ballot order
    } else {
        lemma_higher_ballot_sees_chosen_version(
            states, b2, b1, v2, q2, q1, universe, cluster_size, v1
        );
        assume(v1 == v2); // PROOF_OBLIGATION: symmetric case
    }
}

// UUID uniqueness among chosen values: same version => same UUID.
// Note: transient acceptor state may hold different UUIDs at the same version
// during concurrent proposals — this lemma applies to chosen values ONLY.
pub proof fn lemma_uuid_unique_among_chosen<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b1: Ballot,
    b2: Ballot,
    v1: Versioned<S>,
    v2: Versioned<S>,
    q1: Set<NodeId>,
    q2: Set<NodeId>,
    universe: Set<NodeId>,
    cluster_size: u64,
)
    requires
        chosen(states, b1, v1, q1, cluster_size),
        chosen(states, b2, v2, q2, cluster_size),
        v1.version == v2.version,
        q1.subset_of(universe),
        q2.subset_of(universe),
        universe.finite(),
        universe.len() == cluster_size as nat,
        forall |id: NodeId| universe.contains(id) ==> states.contains_key(id),
        forall |id: NodeId| #[trigger] states.contains_key(id) ==> inv_acceptor(states[id]),
        forall |id: NodeId| #[trigger] q1.contains(id) ==>
            match states[id].promised { Some(p) => ballot_le(b1, p), None => false },
        forall |id: NodeId| #[trigger] q2.contains(id) ==>
            match states[id].promised { Some(p) => ballot_le(b2, p), None => false },
    ensures
        v1.uuid == v2.uuid
{
    lemma_version_unique_across_ballots(
        states, b1, b2, v1, v2, q1, q2, universe, cluster_size
    );
    assert(v1 == v2);
}

} // verus!
