use vstd::prelude::*;

verus! {

pub type NodeId = u64;
pub type ProposerId = u64;

#[derive(PartialEq, Eq, Clone, Copy)]
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

#[derive(PartialEq, Eq, Clone)]
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

} // verus!
