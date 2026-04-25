use vstd::prelude::*;

verus! {

pub type NodeId = u64;
pub type ProposerId = u64;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Ballot {
    pub round: u64,
    pub proposer_id: ProposerId,
}

pub open spec fn ballot_lt(a: Ballot, b: Ballot) -> bool {
    a.round < b.round || (a.round == b.round && a.proposer_id < b.proposer_id)
}

pub open spec fn ballot_le(a: Ballot, b: Ballot) -> bool {
    ballot_lt(a, b) || a == b
}

proof fn lemma_ballot_lt_irrefl(a: Ballot)
    ensures !ballot_lt(a, a)
{}

proof fn lemma_ballot_lt_asymm(a: Ballot, b: Ballot)
    requires ballot_lt(a, b)
    ensures !ballot_lt(b, a)
{}

proof fn lemma_ballot_lt_trans(a: Ballot, b: Ballot, c: Ballot)
    requires ballot_lt(a, b), ballot_lt(b, c)
    ensures ballot_lt(a, c)
{}

proof fn lemma_ballot_lt_total(a: Ballot, b: Ballot)
    requires a != b
    ensures ballot_lt(a, b) || ballot_lt(b, a)
{}

// Uuid is u128 in spec mode (no rand dependency needed for proofs).
// In exec mode, the caller generates a u128 and passes it in.
pub type Uuid = u128;

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Versioned<S> {
    pub version: u64,
    pub uuid: Uuid,
    pub state: S,
}

// apply_cas is the only spec function that touches .state.
// new_uuid is supplied by the proposer at the exec layer and passed through as a spec argument.
pub open spec fn apply_cas<S>(
    f: spec_fn(S) -> S,
    v: Versioned<S>,
    new_uuid: Uuid,
) -> Versioned<S>
    recommends v.version < u64::MAX
{
    Versioned {
        version: (v.version + 1) as u64,
        uuid: new_uuid,
        state: f(v.state),
    }
}

pub proof fn lemma_apply_cas_increments_version<S>(
    f: spec_fn(S) -> S,
    v: Versioned<S>,
    new_uuid: Uuid,
)
    requires v.version < u64::MAX
    ensures apply_cas(f, v, new_uuid).version == v.version + 1
{}

// cluster_size is threaded as a parameter everywhere — never a global.
pub open spec fn is_quorum(q: Set<NodeId>, cluster_size: u64) -> bool {
    q.finite() && q.len() * 2 > cluster_size as nat
}

// RoundId is the ballot that uniquely identifies a round.
pub type RoundId = Ballot;

pub proof fn lemma_quorums_intersect(
    q1: Set<NodeId>,
    q2: Set<NodeId>,
    universe: Set<NodeId>,
    cluster_size: u64,
)
    requires
        is_quorum(q1, cluster_size),
        is_quorum(q2, cluster_size),
        q1.subset_of(universe),
        q2.subset_of(universe),
        universe.finite(),
        universe.len() == cluster_size as nat,
    ensures
        !(q1.intersect(q2)).is_empty(),
{
    // q1 and q2 are both finite (from is_quorum).
    // q1 ∪ q2 ⊆ universe, so (q1 ∪ q2).len() ≤ universe.len() = cluster_size.
    // By lemma_set_intersect_union_lens:
    //   (q1 + q2).len() + (q1 ∩ q2).len() == q1.len() + q2.len()
    // q1.len() + q2.len() > cluster_size (each > cluster_size/2).
    // So (q1 ∩ q2).len() > (q1 + q2).len() - cluster_size ≥ 0, in fact > 0.
    let inter = q1.intersect(q2);
    let union = q1.union(q2);
    // union is finite since both q1, q2 are finite
    vstd::set_lib::lemma_set_union_finite_iff(q1, q2);
    // union ⊆ universe, so union.len() ≤ universe.len() = cluster_size
    vstd::set_lib::lemma_len_subset(union, universe);
    // (q1 + q2).len() + inter.len() == q1.len() + q2.len()
    vstd::set_lib::lemma_set_intersect_union_lens(q1, q2);
    // Now derive: inter.len() > 0
    assert(inter.len() > 0) by {
        // union.len() ≤ cluster_size, and inter.len() = q1.len() + q2.len() - union.len()
        // q1.len() > cluster_size/2 and q2.len() > cluster_size/2
        // so q1.len() + q2.len() > cluster_size ≥ union.len()
        // hence inter.len() > 0
    };
    // inter.len() > 0 implies inter is not empty
    vstd::set_lib::axiom_is_empty_len0(inter);
}

// participating_quorum records which acceptors actually responded in each round.
// Safety invariants are properties of completed rounds only.
// Whether a round completes is a liveness question and is not modeled here.
pub spec fn participating_quorum(round: RoundId, universe: Set<NodeId>) -> Set<NodeId>;

// round_completed holds when the participating quorum is a valid quorum.
pub open spec fn round_completed(round: RoundId, cluster_size: u64, universe: Set<NodeId>) -> bool {
    is_quorum(participating_quorum(round, universe), cluster_size)
}

} // verus!
