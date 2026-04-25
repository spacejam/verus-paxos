use vstd::prelude::*;
use crate::primitives::*;

verus! {

#[derive(PartialEq, Eq, Clone)]
pub struct AcceptorState<S> {
    pub promised: Option<Ballot>,
    pub accepted: Option<(Ballot, Versioned<S>)>,
}

// INV_ACCEPTOR: accepted ballot never exceeds promised ballot.
pub open spec fn inv_acceptor<S>(state: AcceptorState<S>) -> bool {
    match state.accepted {
        None => true,
        Some((b, _v)) => match state.promised {
            None => false,
            Some(p) => ballot_le(b, p),
        }
    }
}

pub proof fn lemma_initial_state_satisfies_inv<S>()
    ensures inv_acceptor(AcceptorState::<S> { promised: None, accepted: None })
{}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_state_has_no_accepted() {
        let s: AcceptorState<u64> = AcceptorState {
            promised: None,
            accepted: None,
        };
        assert!(s.promised.is_none());
        assert!(s.accepted.is_none());
    }
}
