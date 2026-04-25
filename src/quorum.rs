// Layer 3
#[allow(unused_imports)]
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::primitives::*;
#[allow(unused_imports)]
use crate::acceptor::*;
#[allow(unused_imports)]
use crate::history::*;

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
// then select_value on the concrete Phase 1 promises returns a version >= v1.version.
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
    promises: Seq<Promise<S>>,
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
        // Completeness: promises faithfully reflects q2 acceptors' accepted values.
        // Caller (cluster.rs) proves this from ghost tracking; was previously the axiom.
        forall |id: NodeId|
            #[trigger] q2.contains(id)
            && states.contains_key(id)
            ==> exists |i: int| 0 <= i < promises.len()
                && promises[i].from == id
                && promises[i].accepted == states[id].accepted,
    ensures
        select_value(promises, own_value).version >= v1.version
{
    lemma_quorums_intersect(q1, q2, universe, cluster_size);
    let id = choose |id: NodeId| q1.intersect(q2).contains(id);
    assert(q1.contains(id));
    assert(q2.contains(id));
    assert(states[id].accepted == Some((b1, v1)));
    let idx = choose |i: int| 0 <= i < promises.len()
        && promises[i].from == id
        && promises[i].accepted == states[id].accepted;
    assert(promises[idx].accepted == Some((b1, v1)));
    lemma_select_value_version_is_max(promises, own_value);
    assert(select_value(promises, own_value).version >= v1.version);
}

// Version uniqueness: at most one Versioned<S> with a given version is ever chosen.
// Proof: both values appear in ChosenHistory (by inv_chosen_in_history).
// Since history versions are strictly increasing (inv_history_monotone), same version
// implies same index implies same value.
pub proof fn lemma_version_unique_across_ballots<S>(
    h: ChosenHistory<S>,
    v1: Versioned<S>,
    v2: Versioned<S>,
)
    requires
        v1.version == v2.version,
        inv_history_monotone(h),
        exists |i: int| 0 <= i < h.len() && h[i] == v1,
        exists |i: int| 0 <= i < h.len() && h[i] == v2,
    ensures
        v1 == v2
{
    let i1 = choose |i: int| 0 <= i < h.len() && h[i] == v1;
    let i2 = choose |i: int| 0 <= i < h.len() && h[i] == v2;
    // h[i1].version == v1.version == v2.version == h[i2].version
    if i1 < i2 {
        assert(0 <= i1 < i2 < h.len());
        assert(h[i1].version < h[i2].version); // inv_history_monotone
        assert(false);
    } else if i2 < i1 {
        assert(0 <= i2 < i1 < h.len());
        assert(h[i2].version < h[i1].version); // inv_history_monotone
        assert(false);
    }
    // i1 == i2 => h[i1] == h[i2] => v1 == v2
    assert(i1 == i2);
    assert(v1 == h[i1]);
    assert(v2 == h[i2]);
}

// UUID uniqueness among chosen values: same version => same UUID.
// Note: transient acceptor state may hold different UUIDs at the same version
// during concurrent proposals — this lemma applies to chosen values ONLY.
pub proof fn lemma_uuid_unique_among_chosen<S>(
    h: ChosenHistory<S>,
    v1: Versioned<S>,
    v2: Versioned<S>,
)
    requires
        v1.version == v2.version,
        inv_history_monotone(h),
        exists |i: int| 0 <= i < h.len() && h[i] == v1,
        exists |i: int| 0 <= i < h.len() && h[i] == v2,
    ensures
        v1.uuid == v2.uuid
{
    lemma_version_unique_across_ballots(h, v1, v2);
    assert(v1 == v2);
}

} // verus!
