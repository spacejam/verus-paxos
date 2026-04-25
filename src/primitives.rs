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

} // verus!
