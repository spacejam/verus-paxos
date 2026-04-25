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

#[derive(Clone, Debug)]
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
            PrepareResponse::Promise { ballot, accepted } => {
                ballot == b
                && result.0.promised == Some(b)
                && accepted == state.accepted
            },
            PrepareResponse::Nack => result.0 == state,
        }
{
    match state.promised {
        None => {
            // inv_acceptor(state) + promised==None implies accepted==None
            assert(state.accepted.is_none());
            // Build new_state without clone: accepted must be None here
            let new_state = AcceptorState::<S> { promised: Some(b), accepted: None };
            let response = PrepareResponse::Promise { ballot: b, accepted: state.accepted };
            (new_state, response)
        }
        Some(p) => {
            if p.round < b.round || (p.round == b.round && p.proposer_id < b.proposer_id) {
                // Explicitly match state.accepted to preserve inv_acceptor through the clone:
                // Ballot is Copy, so ballot field is preserved exactly; only Versioned<S>.state
                // goes through clone. inv_acceptor only checks the ballot, not the value.
                let new_accepted: Option<(Ballot, Versioned<S>)> = match state.accepted {
                    None => None,
                    Some((ab, ref v)) => Some((ab, v.clone())),
                };
                proof {
                    // Show new_accepted has same ballot structure as state.accepted
                    match state.accepted {
                        None => { assert(new_accepted.is_none()); },
                        Some((ab, _)) => {
                            assert(new_accepted.is_some());
                            assert(new_accepted.unwrap().0 == ab);
                            assert(ballot_le(ab, p));
                            // p < b, and ballot_le(ab, p), so ballot_le(ab, b)
                            assert(ballot_le(ab, b)) by {
                                if ab.round < p.round {
                                    assert(ab.round < b.round || ab.round == b.round);
                                    assert(ab.round <= p.round);
                                    assert(ab.round < b.round || (ab.round == b.round && ab.proposer_id <= b.proposer_id));
                                } else {
                                    // ab.round == p.round (since ballot_le holds)
                                    assert(ab.round == p.round);
                                    assert(ab.proposer_id <= p.proposer_id);
                                }
                            }
                        }
                    }
                }
                let new_state = AcceptorState { promised: Some(b), accepted: new_accepted };
                let response = PrepareResponse::Promise { ballot: b, accepted: state.accepted };
                (new_state, response)
            } else {
                (state, PrepareResponse::Nack)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug)]
pub struct Promise<S> {
    pub from: NodeId,
    pub ballot: Ballot,
    pub accepted: Option<(Ballot, Versioned<S>)>,
}

// select_value picks the Versioned<S> with the highest accepted version
// from Phase 1 responses, falling back to own_value if none had accepted.
pub open spec fn select_value<S>(
    responses: Seq<Promise<S>>,
    own_value: Versioned<S>,
) -> Versioned<S>
    decreases responses.len()
{
    if responses.len() == 0 {
        own_value
    } else {
        let rest = select_value(responses.drop_last(), own_value);
        let last = responses.last();
        match last.accepted {
            None => rest,
            Some((_b, v)) => if v.version > rest.version { v } else { rest }
        }
    }
}

pub proof fn lemma_select_value_version_is_max<S>(
    responses: Seq<Promise<S>>,
    own_value: Versioned<S>,
)
    ensures
        select_value(responses, own_value).version >= own_value.version,
        forall |i: int| 0 <= i < responses.len() ==>
            match #[trigger] responses[i].accepted {
                None => true,
                Some((_b, v)) => select_value(responses, own_value).version >= v.version,
            }
    decreases responses.len()
{
    if responses.len() == 0 {
        // vacuously true
    } else {
        let prefix = responses.drop_last();
        lemma_select_value_version_is_max(prefix, own_value);
        let prefix_result = select_value(prefix, own_value);
        let last = responses.last();
        // select_value(responses, ...) is defined in terms of prefix_result and last.accepted
        match last.accepted {
            None => {
                // select_value(responses, own_value) == prefix_result
                assert(select_value(responses, own_value) == prefix_result);
                // for all i in prefix, IH gives: prefix_result.version >= v.version
                // so select_value(responses, own_value).version >= v.version for those i too
                assert forall |i: int| 0 <= i < responses.len() implies
                    match #[trigger] responses[i].accepted {
                        None => true,
                        Some((_b, v)) => select_value(responses, own_value).version >= v.version,
                    }
                by {
                    if i < prefix.len() {
                        // IH covers i in prefix
                        assert(responses[i] == prefix[i]);
                    }
                    // i == responses.len() - 1 is last, with None accepted, trivially true
                }
            },
            Some((_blast, vlast)) => {
                // select_value(responses, own_value) is either vlast or prefix_result
                assert(select_value(responses, own_value) ==
                    if vlast.version > prefix_result.version { vlast } else { prefix_result });
                assert forall |i: int| 0 <= i < responses.len() implies
                    match #[trigger] responses[i].accepted {
                        None => true,
                        Some((_b, v)) => select_value(responses, own_value).version >= v.version,
                    }
                by {
                    if i < prefix.len() {
                        // IH gives prefix_result.version >= v.version for prefix elements
                        assert(responses[i] == prefix[i]);
                        // select_value(responses, own_value).version >= prefix_result.version
                    }
                    // i == last index: select_value >= vlast.version by construction
                }
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
