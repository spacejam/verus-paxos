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

pub enum PrepareResponse<S> {
    Promise { ballot: Ballot, accepted: Option<(Ballot, Versioned<S>)> },
    Nack,
}

// handle_prepare: acceptor responds to Phase 1 prepare.
// Invariant-preserving: inv_acceptor holds before and after.
pub fn handle_prepare<S: Clone>(
    state: AcceptorState<S>,
    b: Ballot,
) -> (result: (AcceptorState<S>, PrepareResponse<S>))
    requires inv_acceptor(state)
    ensures
        inv_acceptor(result.0),
        match result.1 {
            PrepareResponse::Promise { ballot, accepted: _ } => {
                ballot == b
                && result.0.promised == Some(b)
            },
            PrepareResponse::Nack => result.0 == state,
        }
{
    match state.promised {
        None => {
            let accepted = state.accepted.clone();
            let new_state = AcceptorState { promised: Some(b), accepted: state.accepted };
            (new_state, PrepareResponse::Promise { ballot: b, accepted })
        }
        Some(p) => {
            if p.round < b.round || (p.round == b.round && p.proposer_id < b.proposer_id) {
                let accepted = state.accepted.clone();
                let new_state = AcceptorState { promised: Some(b), accepted: state.accepted };
                (new_state, PrepareResponse::Promise { ballot: b, accepted })
            } else {
                (state, PrepareResponse::Nack)
            }
        }
    }
}

pub enum AcceptResponse {
    Accepted { ballot: Ballot },
    Nack,
}

pub fn handle_accept<S: Clone>(
    state: AcceptorState<S>,
    b: Ballot,
    v: Versioned<S>,
) -> (result: (AcceptorState<S>, AcceptResponse))
    requires inv_acceptor(state)
    ensures
        inv_acceptor(result.0),
        match result.1 {
            AcceptResponse::Accepted { ballot } => {
                ballot == b
                && result.0.accepted == Some((b, v))
                && ballot_le(b, result.0.promised.unwrap())
            },
            AcceptResponse::Nack => result.0 == state,
        }
{
    match state.promised {
        None => (state, AcceptResponse::Nack),
        Some(p) => {
            let accept = p.round < b.round
                || (p.round == b.round && p.proposer_id <= b.proposer_id);
            if accept {
                let new_state = AcceptorState {
                    promised: Some(b),
                    accepted: Some((b, v)),
                };
                assert(ballot_le(b, b)) by {
                    assert(b == b);
                }
                (new_state, AcceptResponse::Accepted { ballot: b })
            } else {
                (state, AcceptResponse::Nack)
            }
        }
    }
}

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

    #[test]
    fn prepare_on_fresh_state_returns_promise() {
        let state: AcceptorState<u64> = AcceptorState { promised: None, accepted: None };
        let b = Ballot { round: 1, proposer_id: 42 };
        let (new_state, resp) = handle_prepare(state, b);
        assert!(matches!(resp, PrepareResponse::Promise { .. }));
        assert_eq!(new_state.promised, Some(b));
    }

    #[test]
    fn prepare_with_lower_ballot_returns_nack() {
        let high = Ballot { round: 5, proposer_id: 1 };
        let low  = Ballot { round: 3, proposer_id: 1 };
        let state: AcceptorState<u64> = AcceptorState { promised: Some(high), accepted: None };
        let (_new_state, resp) = handle_prepare(state, low);
        assert!(matches!(resp, PrepareResponse::Nack));
    }

    #[test]
    fn accept_after_matching_promise_succeeds() {
        let b = Ballot { round: 2, proposer_id: 7 };
        let v = Versioned { version: 0, uuid: 0, state: 42u64 };
        let state = AcceptorState { promised: Some(b), accepted: None };
        let (new_state, resp) = handle_accept(state, b, v.clone());
        assert!(matches!(resp, AcceptResponse::Accepted { .. }));
        assert_eq!(new_state.accepted, Some((b, v)));
    }

    #[test]
    fn accept_with_lower_ballot_than_promise_nacks() {
        let promised = Ballot { round: 5, proposer_id: 1 };
        let lower    = Ballot { round: 2, proposer_id: 1 };
        let v = Versioned { version: 0, uuid: 0, state: 0u64 };
        let state = AcceptorState { promised: Some(promised), accepted: None };
        let (_new_state, resp) = handle_accept(state, lower, v);
        assert!(matches!(resp, AcceptResponse::Nack));
    }
}
