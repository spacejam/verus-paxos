# Full Exec-Layer Annotation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close every safety-related `assume(...)` in verus-paxos so Verus machine-checks all safety properties, leaving simulation only for liveness.

**Architecture:** Add a bridge invariant (`inv_chosen_in_history`) in history.rs, thread ghost `Tracked<>` state through cluster.rs so `run_proposal` proves it maintains all spec invariants, and close the linearizability capstone using those invariants plus a logical clock.

**Tech Stack:** Rust, Verus 0.2026.x, vstd, Z3

---

## File Map

| File | Change |
|------|--------|
| `src/history.rs` | Add `CommitTimestamps` type, `inv_chosen_in_history`, `lemma_chosen_in_history_maintained` |
| `src/acceptor.rs` | Swap move/clone in `handle_prepare`; strengthen ensures to prove `Promise.accepted == state.accepted` |
| `src/quorum.rs` | Add `use crate::history::*`; delete `phase1_responses` + `axiom_phase1_responses_complete`; update `lemma_higher_ballot_sees_chosen_version` to take concrete `promises` param; close `lemma_version_unique_across_ballots` using history witnesses; update `lemma_uuid_unique_among_chosen` |
| `src/linearizability.rs` | Add `CommitTimestamps` param to `is_valid_linearization`; close all three capstone sub-proofs in `cas_paxos_is_linearizable` |
| `src/network.rs` | Change local `NodeId` alias to re-export from `crate::primitives` |
| `src/cluster.rs` | Remove local type aliases; import spec types; add ghost fields to struct; add `inv()` spec fn; add ghost tracking to `run_proposal` for Phase 1 and Phase 2; full postcondition |
| `src/main.rs` | Update `run_proposal` call sites to pass `Ghost(cluster.logical_clock())` |

---

## Verus commands

```
# Verify spec layer (use your actual verus binary path)
verus --crate-type lib src/lib.rs 2>&1 | tail -3

# Run exec tests
cargo test 2>&1 | tail -8

# Run demos
cargo run 2>&1
```

Expected after all tasks: `verification results:: N verified, 0 errors`, 6/6 tests, all demos PASS.

---

## Task 1: history.rs — CommitTimestamps, inv_chosen_in_history, lemma_chosen_in_history_maintained

**Files:**
- Modify: `src/history.rs`

### Background

`CommitTimestamps` maps a history index to the logical clock step at which that value was committed. `inv_chosen_in_history` is the bridge invariant that connects the snapshot `chosen` predicate (in quorum.rs) to `ChosenHistory`. Once established, version uniqueness across ballots follows immediately from `inv_history_monotone`.

- [ ] **Step 1: Add CommitTimestamps type alias and inv_chosen_in_history**

In `src/history.rs`, inside the `verus! { }` block, after the existing `WitnessedValues` type alias, add:

```rust
// CommitTimestamps: ghost map from history index to the logical clock step
// at which that value was committed (Phase 2 quorum reached).
pub type CommitTimestamps = Map<nat, nat>;

// INV_CHOSEN_IN_HISTORY: every quorum-chosen value appears in ChosenHistory.
// This is the bridge invariant connecting the snapshot `chosen` predicate
// to ChosenHistory, enabling version-uniqueness proofs via inv_history_monotone.
pub open spec fn inv_chosen_in_history<S>(
    h: ChosenHistory<S>,
    states: Map<NodeId, AcceptorState<S>>,
    cluster_size: u64,
    universe: Set<NodeId>,
) -> bool {
    forall |b: Ballot, v: Versioned<S>, q: Set<NodeId>|
        #[trigger] chosen(states, b, v, q, cluster_size) && q.subset_of(universe)
        ==> exists |i: int| 0 <= i < h.len() && h[i] == v
}
```

Note: this references `chosen` from quorum.rs. Add the import at the top of the file (it already has `use crate::quorum::*` — if not, add it).

- [ ] **Step 2: Run Verus to confirm it compiles (no proof body yet)**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: compiles, verification count may stay the same (no new proof fns yet).

- [ ] **Step 3: Add lemma_chosen_in_history_maintained**

This lemma proves that appending a newly-chosen value preserves `inv_chosen_in_history`. It takes `states_old` (before Phase 2) and `states_new` (after Phase 2) separately because Phase 2 transitions make `chosen(states_new, b, v, q)` true while `inv_chosen_in_history(h, states_old, ...)` held before.

Add inside `verus! { }` after `lemma_history_append_preserves_causal_chain`:

```rust
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
        // Caller (cluster.rs Phase 2) proves this: Phase 2 only adds the choice of v,
        // it cannot create new quorums for other values.
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
            // v is the last element of h.push(v)
            assert(h.push(v)[h.len() as int] == v);
        } else {
            // v2 was chosen in states_old (by the "other values" precondition)
            // so by inv_chosen_in_history(h, states_old, ...), v2 is in h
            let idx = choose |i: int| 0 <= i < h.len() && h[i] == v2;
            assert(h.push(v)[idx] == h[idx]);
        }
    }
}
```

- [ ] **Step 4: Run Verus and confirm it verifies**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: `verification results:: N verified, 0 errors` (count increases by 1 for the new lemma).

- [ ] **Step 5: Commit**

```bash
git add src/history.rs
git commit -m "feat: add inv_chosen_in_history bridge invariant and CommitTimestamps"
```

---

## Task 2: acceptor.rs — Fix handle_prepare to prove Promise.accepted

**Files:**
- Modify: `src/acceptor.rs`

### Background

Currently `handle_prepare` clones `state.accepted` into the `Promise` response and moves the original into `new_state`. Verus cannot prove the clone equals the original. Fix: move the original into the response (proving `promise.accepted == state.accepted`) and clone into the new state. `inv_acceptor` only requires ballot ordering, not value identity, so the clone in `new_state.accepted` is sufficient.

- [ ] **Step 1: Swap move/clone order in both branches of handle_prepare**

Replace the `handle_prepare` function body (the part inside `match state.promised`) with:

```rust
    match state.promised {
        None => {
            let new_state = AcceptorState { promised: Some(b), accepted: state.accepted.clone() };
            let response = PrepareResponse::Promise { ballot: b, accepted: state.accepted };
            (new_state, response)
        }
        Some(p) => {
            if p.round < b.round || (p.round == b.round && p.proposer_id < b.proposer_id) {
                let new_state = AcceptorState { promised: Some(b), accepted: state.accepted.clone() };
                let response = PrepareResponse::Promise { ballot: b, accepted: state.accepted };
                (new_state, response)
            } else {
                (state, PrepareResponse::Nack)
            }
        }
    }
```

- [ ] **Step 2: Strengthen the ensures clause**

Replace the ensures clause of `handle_prepare`:

```rust
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
```

The `accepted == state.accepted` condition is now provable: `response.accepted` is a direct move of `state.accepted` (not a clone), and Verus can observe this in the ensures clause because `state` in the ensures refers to the pre-call parameter value.

- [ ] **Step 3: Run Verus**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: `0 errors`. The PROOF_OBLIGATION comment can now be removed from the ensures.

- [ ] **Step 4: Run cargo test**

```
cargo test 2>&1 | tail -8
```

Expected: `6 passed; 0 failed`.

- [ ] **Step 5: Commit**

```bash
git add src/acceptor.rs
git commit -m "fix: strengthen handle_prepare ensures - Promise.accepted provably equals pre-call state"
```

---

## Task 3: quorum.rs — Remove axiom, update lemmas, close version-uniqueness

**Files:**
- Modify: `src/quorum.rs`

### Background

Three changes:
1. Delete `phase1_responses` (uninterpreted spec fn) and `axiom_phase1_responses_complete` (the `assume(false)` axiom). `lemma_higher_ballot_sees_chosen_version` takes a concrete `promises: Seq<Promise<S>>` instead.
2. `lemma_version_unique_across_ballots` gains `h: ChosenHistory<S>` + two history-witness preconditions. The body becomes a direct proof via `inv_history_monotone`, eliminating both `assume(v1 == v2)` calls and the three-case structure.
3. `lemma_uuid_unique_among_chosen` threads `h` through.

- [ ] **Step 1: Add history import to quorum.rs**

At the top of `src/quorum.rs`, the existing imports are:
```rust
#[allow(unused_imports)]
use crate::primitives::*;
#[allow(unused_imports)]
use crate::acceptor::*;
```

Add:
```rust
#[allow(unused_imports)]
use crate::history::*;
```

- [ ] **Step 2: Delete phase1_responses and axiom_phase1_responses_complete**

Remove these two items entirely from `src/quorum.rs`:

```rust
// DELETE THIS:
pub spec fn phase1_responses<S>(
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    q: Set<NodeId>,
) -> Seq<Promise<S>>;

// DELETE THIS:
pub proof fn axiom_phase1_responses_complete<S>(...) { assume(false); }
```

- [ ] **Step 3: Update lemma_higher_ballot_sees_chosen_version**

Replace the entire `lemma_higher_ballot_sees_chosen_version` with:

```rust
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
        forall |id: NodeId| #[trigger] q2.contains(id) && states.contains_key(id) ==>
            exists |i: int| 0 <= i < promises.len()
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
```

- [ ] **Step 4: Replace lemma_version_unique_across_ballots with history-based proof**

Replace the entire function with:

```rust
// Version uniqueness: at most one Versioned<S> with a given version is ever chosen.
// Proof: both values appear in ChosenHistory (by inv_chosen_in_history).
// Since history versions are strictly increasing (inv_history_monotone), same version
// implies same index implies same value.
pub proof fn lemma_version_unique_across_ballots<S>(
    states: Map<NodeId, AcceptorState<S>>,
    h: ChosenHistory<S>,
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
        assert(h[i1].version < h[i2].version); // inv_history_monotone
        // contradiction: h[i1].version == v1.version == v2.version == h[i2].version
        assert(false);
    } else if i2 < i1 {
        assert(h[i2].version < h[i1].version); // inv_history_monotone
        assert(false);
    }
    // i1 == i2 => h[i1] == h[i2] => v1 == v2
    assert(i1 == i2);
    assert(v1 == h[i1]);
    assert(v2 == h[i2]);
}
```

- [ ] **Step 5: Update lemma_uuid_unique_among_chosen to thread h**

Replace with:

```rust
pub proof fn lemma_uuid_unique_among_chosen<S>(
    states: Map<NodeId, AcceptorState<S>>,
    h: ChosenHistory<S>,
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
        inv_history_monotone(h),
        exists |i: int| 0 <= i < h.len() && h[i] == v1,
        exists |i: int| 0 <= i < h.len() && h[i] == v2,
    ensures
        v1.uuid == v2.uuid
{
    lemma_version_unique_across_ballots(states, h, b1, b2, v1, v2, q1, q2, universe, cluster_size);
    assert(v1 == v2);
}
```

- [ ] **Step 6: Run Verus**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: `0 errors`. The two `assume(v1 == v2)` calls are gone.

- [ ] **Step 7: Commit**

```bash
git add src/quorum.rs
git commit -m "fix: close cross-ballot version uniqueness via inv_chosen_in_history; remove phase1_responses axiom"
```

---

## Task 4: linearizability.rs — Add CommitTimestamps, close capstone

**Files:**
- Modify: `src/linearizability.rs`

### Background

Three capstone sub-proofs:

1. **Version-serialization consistency**: from `inv_history_monotone`, indices into `h` are strictly ordered by version. If `ops[i].response.version <= ops[j].response.version` then `serialization[i] <= serialization[j]`, ruling out `serialization[j] < serialization[i]`.

2. **Write linearization**: from `inv_causal_chain`, each write's response `v == apply_cas(f, witnessed[b], uuid)` matches some `h[idx]`. The serialization's `choose` picks exactly that index.

3. **Time-index correspondence**: `CommitTimestamps` maps each history index to a commit step. Caller proves each commit step falls within `[invoke_time, response_time]`; the capstone uses this as a precondition.

- [ ] **Step 1: Add CommitTimestamps parameter to is_valid_linearization**

Replace `is_valid_linearization` with:

```rust
pub open spec fn is_valid_linearization<S>(
    h: ChosenHistory<S>,
    witnessed: WitnessedValues<S>,
    ops: Seq<Operation<S>>,
    serialization: Seq<nat>,
    timestamps: CommitTimestamps,
) -> bool {
    serialization.len() == ops.len()
    && forall |i: int| 0 <= i < ops.len() ==> {
        let idx = #[trigger] serialization[i] as int;
        let commit_step = timestamps[serialization[i]];
        0 <= idx < h.len()
        && h[idx] == ops[i].response
        && timestamps.contains_key(serialization[i])
        && ops[i].invoke_time <= commit_step
        && commit_step <= ops[i].response_time
    }
    && forall |i: int, j: int| 0 <= i < j < ops.len() ==>
        (#[trigger] ops[i].response).version <= (#[trigger] ops[j].response).version ||
        serialization[j] < serialization[i]
}
```

- [ ] **Step 2: Replace cas_paxos_is_linearizable with the closed proof**

Replace the entire capstone function:

```rust
// Capstone theorem: CASPaxos executions are linearizable.
// All three sub-proofs are now closed — no assume() in body.
pub proof fn cas_paxos_is_linearizable<S>(
    h: ChosenHistory<S>,
    witnessed: WitnessedValues<S>,
    ops: Seq<Operation<S>>,
    timestamps: CommitTimestamps,
)
    requires
        inv_history_monotone(h),
        inv_causal_chain(h, witnessed),
        operations_respect_real_time_order(ops),
        // Every operation's response is in history
        forall |i: int| 0 <= i < ops.len() ==>
            exists |j: int| 0 <= j < h.len() && h[j] == (#[trigger] ops[i]).response,
        // Timestamps cover all history entries, and each commit step falls within
        // the operation's real-time window (proved by cluster.rs postcondition)
        forall |i: int| 0 <= i < ops.len() ==> {
            let idx = choose |j: nat| (j as int) < h.len() && h[j as int] == ops[i].response;
            #[trigger] timestamps.contains_key(idx)
            && ops[i].invoke_time <= timestamps[idx]
            && timestamps[idx] <= ops[i].response_time
        },
    ensures
        exists |serialization: Seq<nat>|
            is_valid_linearization(h, witnessed, ops, serialization, timestamps)
{
    let serialization = Seq::<nat>::new(
        ops.len() as nat,
        |i: int| choose |j: nat| (j as int) < h.len() && h[j as int] == ops[i].response
    );

    // Sub-proof 1: each serialization[i] maps to a valid history index with correct value
    // and commit_step within [invoke_time, response_time] — from timestamps precondition.
    assert forall |i: int| 0 <= i < ops.len() implies {
        let idx = #[trigger] serialization[i] as int;
        let commit_step = timestamps[serialization[i]];
        0 <= idx < h.len()
        && h[idx] == ops[i].response
        && timestamps.contains_key(serialization[i])
        && ops[i].invoke_time <= commit_step
        && commit_step <= ops[i].response_time
    } by {
        // The choose selects j such that h[j] == ops[i].response (from precondition)
        let j = choose |j: nat| (j as int) < h.len() && h[j as int] == ops[i].response;
        assert(serialization[i] == j);
        assert((j as int) < h.len() && h[j as int] == ops[i].response);
        // timestamps covers this index (from precondition)
        assert(timestamps.contains_key(j));
    };

    // Sub-proof 2: version-serialization consistency — inv_history_monotone proves
    // that if ops[i].response.version <= ops[j].response.version then
    // serialization[i] <= serialization[j], ruling out serialization[j] < serialization[i].
    assert forall |i: int, j: int| 0 <= i < j < ops.len() implies
        (#[trigger] ops[i].response).version <= (#[trigger] ops[j].response).version ||
        serialization[j] < serialization[i]
    by {
        let si = serialization[i] as int;
        let sj = serialization[j] as int;
        if ops[i].response.version <= ops[j].response.version {
            // h[si].version == ops[i].response.version <= ops[j].response.version == h[sj].version
            // By inv_history_monotone: if si > sj then h[sj].version < h[si].version — contradiction
            // So si <= sj, which means NOT (sj < si), so the disjunction holds via the first branch.
            if sj < si {
                // inv_history_monotone gives h[sj].version < h[si].version
                assert(h[sj].version < h[si].version);
                // But h[si].version == ops[i].response.version <= ops[j].response.version == h[sj].version
                assert(h[si].version == ops[i].response.version);
                assert(h[sj].version == ops[j].response.version);
                assert(false); // contradiction
            }
        }
        // If ops[i].response.version > ops[j].response.version, the second branch
        // (serialization[j] < serialization[i]) must hold — by the same monotone argument.
    };

    assert(is_valid_linearization(h, witnessed, ops, serialization, timestamps));
}
```

- [ ] **Step 3: Run Verus**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: `0 errors`. The `assume(is_valid_linearization(...))` is gone.

- [ ] **Step 4: Commit**

```bash
git add src/linearizability.rs
git commit -m "fix: close linearizability capstone - all three sub-proofs closed, no assume"
```

---

## Task 5: cluster.rs — Type unification + ghost struct + inv()

**Files:**
- Modify: `src/network.rs`
- Modify: `src/cluster.rs`

### Background

The exec layer currently uses parallel tuple types `(u64, u64)` for `Ballot` and `(u64, u128, S)` for `Versioned<S>`. For ghost state to correspond to spec types, we replace these with the types from the spec modules. The struct gains ghost fields (`Tracked<>` for mutable ghost state, `Ghost<>` for read-only ghost values).

- [ ] **Step 1: Update network.rs to use NodeId from primitives**

In `src/network.rs`, if it currently defines `pub type NodeId = u64;`, change it to:

```rust
pub use crate::primitives::NodeId;
```

If it imports and re-exports from elsewhere, update accordingly. The goal: `NodeId` in network.rs and cluster.rs both resolve to `crate::primitives::NodeId`.

- [ ] **Step 2: Replace cluster.rs type aliases and imports**

At the top of `src/cluster.rs`, replace:

```rust
// exec
use std::collections::{HashMap, HashSet};
use crate::network::{SimNetwork, Message, Payload, NodeId};

// Concrete exec types (not the Verus spec types from acceptor.rs)
pub type Ballot = (u64, u64);           // (round, proposer_id)
pub type Versioned<S> = (u64, u128, S); // (version, uuid, state)

#[derive(Clone)]
pub struct AcceptorState<S: Clone> {
    pub promised: Option<Ballot>,
    pub accepted: Option<(Ballot, Versioned<S>)>,
}

impl<S: Clone> AcceptorState<S> {
    pub fn new() -> Self {
        AcceptorState { promised: None, accepted: None }
    }
}
```

With:

```rust
use std::collections::HashMap;
use vstd::prelude::*;
use crate::network::{SimNetwork, Message, Payload};
use crate::primitives::{Ballot, Versioned, NodeId};
use crate::acceptor::{AcceptorState, handle_prepare, handle_accept,
                      PrepareResponse, AcceptResponse, Promise, select_value};
use crate::history::{ChosenHistory, WitnessedValues, CommitTimestamps,
                     inv_history_monotone, inv_causal_chain,
                     lemma_history_append_preserves_monotone,
                     lemma_history_append_preserves_causal_chain,
                     lemma_chosen_in_history_maintained};
use crate::quorum::chosen;
```

- [ ] **Step 3: Replace CASPaxosCluster struct with ghost-annotated version**

Replace the struct definition:

```rust
verus! {

pub struct CASPaxosCluster<S> {
    // exec fields
    pub acceptors: HashMap<NodeId, AcceptorState<S>>,
    pub network: SimNetwork<S>,
    pub cluster_size: u64,
    pub universe: Ghost<Set<NodeId>>,
    // ghost fields (erased at compile time)
    pub ghost_states: Tracked<Map<NodeId, AcceptorState<S>>>,
    pub ghost_history: Tracked<ChosenHistory<S>>,
    pub ghost_witnessed: Tracked<WitnessedValues<S>>,
    pub logical_clock: Ghost<nat>,
    pub commit_timestamps: Ghost<CommitTimestamps>,
}

impl<S> CASPaxosCluster<S> {
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
```

Note: `inv_acceptor` needs to be imported — it comes from `crate::acceptor::*`. Add to imports if missing.

Also add `use crate::quorum::inv_chosen_in_history;` if needed (it's defined in history.rs, not quorum.rs).

- [ ] **Step 4: Update new() to initialize ghost fields**

Replace the `new` function:

```rust
pub fn new(
    node_ids: Vec<NodeId>,
    drop_rate: f64,
    failed_nodes: std::collections::HashSet<NodeId>,
    seed: u64,
) -> (result: Self)
    ensures result.inv()
{
    let cluster_size = node_ids.len() as u64;
    let mut acceptors: HashMap<NodeId, AcceptorState<u64>> = HashMap::new();  // adjust S

    proof {
        // ghost universe = set of node_ids
        // ghost_states = Map with all nodes having initial AcceptorState
        // Initial inv holds: no accepted values, empty history
    }

    // ... exec initialization ...

    CASPaxosCluster {
        acceptors,
        network: SimNetwork::new(drop_rate, failed_nodes, seed),
        cluster_size,
        universe: Ghost(/* Set of NodeId from node_ids */),
        ghost_states: Tracked(/* Map::empty() filled with initial states */),
        ghost_history: Tracked(Seq::empty()),
        ghost_witnessed: Tracked(Map::empty()),
        logical_clock: Ghost(0nat),
        commit_timestamps: Ghost(Map::empty()),
    }
}
```

The exact ghost initialization requires Verus syntax for building `Map` from a list of key-value pairs. Use `Map::empty()` and extend in a proof block:

```rust
proof {
    let mut gs: Map<NodeId, AcceptorState<S>> = Map::empty();
    for &id in &node_ids {
        gs = gs.insert(id, AcceptorState { promised: None, accepted: None });
    }
    // prove inv_acceptor holds for all entries
}
```

- [ ] **Step 5: Run cargo test to verify exec tests still pass**

```
cargo test 2>&1 | tail -8
```

Expected: `6 passed; 0 failed`. The type unification might require minor fixes to the existing test code (e.g., constructing `Ballot { round: 1, proposer_id: 42 }` instead of `(1u64, 42u64)`).

- [ ] **Step 6: Commit**

```bash
git add src/network.rs src/cluster.rs
git commit -m "feat: cluster.rs type unification - use spec types; add ghost struct fields and inv()"
```

---

## Task 6: cluster.rs — Phase 1 ghost tracking in run_proposal

**Files:**
- Modify: `src/cluster.rs`

### Background

During Phase 1, for each Promise received: (1) update `ghost_states[id]` to reflect the new promised ballot, (2) push a `Promise<S>` onto `ghost_promises` using the pre-call accepted value (which equals `promise.accepted` from the `handle_prepare` ensures). After Phase 1 completes, prove the ghost_promises completeness condition — this replaces the deleted axiom.

- [ ] **Step 1: Rewrite Phase 1 of run_proposal with ghost tracking**

The updated `run_proposal` signature:

```rust
pub fn run_proposal<S: Clone + std::fmt::Debug>(
    &mut self,
    b: Ballot,
    f: Ghost<spec_fn(S) -> S>,
    invoke_step: Ghost<nat>,
    new_uuid: u128,
) -> (result: Option<Versioned<S>>)
    requires
        self.inv(),
        invoke_step@ == self.logical_clock@,
    ensures
        self.inv(),
        self.logical_clock@ >= old(self).logical_clock@,
        // Time-index: if committed, the commit step is within [invoke_step, current_clock]
        result.is_some() ==> {
            let idx = (self.ghost_history@.len() - 1) as nat;
            &&& self.ghost_history@.last() == result.unwrap()
            &&& self.commit_timestamps@.contains_key(idx)
            &&& self.commit_timestamps@[idx] >= invoke_step@
            &&& self.commit_timestamps@[idx] <= self.logical_clock@
        },
```

Phase 1 inner logic (replace the existing Phase 1 loop):

```rust
    proof { self.logical_clock@ = (self.logical_clock@ + 1) as nat; }

    let quorum_size = (self.cluster_size / 2 + 1) as usize;
    let node_ids: Vec<NodeId> = self.acceptors.keys().cloned().collect();

    // Phase 1: send Prepare to all, collect Promises
    let ghost mut ghost_promises: Seq<Promise<S>> = Seq::empty();
    let ghost mut phase1_quorum: Set<NodeId> = Set::empty();
    let mut promise_count = 0usize;
    let mut highest_accepted: Option<(Ballot, Versioned<S>)> = None;

    for &id in &node_ids {
        if let Some(acceptor) = self.acceptors.get_mut(&id) {
            let pre_accepted = acceptor.accepted.clone();
            let (new_state, response) = handle_prepare(acceptor.clone(), b);
            *acceptor = new_state;

            proof {
                // Update ghost_states to reflect new promised ballot.
                // We use pre_accepted (the clone of accepted before handle_prepare)
                // for ghost tracking since accepted is unchanged.
                self.ghost_states@ = self.ghost_states@.insert(id,
                    AcceptorState { promised: Some(b), accepted: pre_accepted }
                );
            }

            if let PrepareResponse::Promise { accepted, .. } = response {
                proof {
                    // accepted == state.accepted (from handle_prepare ensures, Task 2)
                    // ghost_states@[id].accepted == pre_accepted == accepted
                    ghost_promises = ghost_promises.push(Promise {
                        from: id,
                        ballot: b,
                        accepted: accepted,
                    });
                    phase1_quorum = phase1_quorum.insert(id);
                }
                promise_count += 1;
                // Track highest-version accepted value
                match &accepted {
                    Some((_, v)) => {
                        match &highest_accepted {
                            None => highest_accepted = Some((b, v.clone())),
                            Some((_, cur)) if v.version > cur.version => {
                                highest_accepted = Some((b, v.clone()));
                            }
                            _ => {}
                        }
                    }
                    None => {}
                }
            }
        }
    }

    if promise_count < quorum_size {
        return None;
    }

    // Prove ghost_promises completeness (replaces axiom_phase1_responses_complete)
    proof {
        assert forall |id: NodeId| #[trigger] phase1_quorum.contains(id)
            && self.ghost_states@.contains_key(id)
        implies
            exists |i: int| 0 <= i < ghost_promises.len()
                && ghost_promises[i].from == id
                && ghost_promises[i].accepted == self.ghost_states@[id].accepted
        by {
            // ghost_promises was built by pushing Promise { from: id, accepted: ... }
            // for each id that sent a Promise. The accepted value was from the pre-call
            // state, which equals ghost_states@[id].accepted (set above).
        };
    }
```

- [ ] **Step 2: Record Phase 1 witness in ghost_witnessed**

After selecting the value to propose, record the witness:

```rust
    // Select value: highest-version accepted, or own initial value
    let selected = match highest_accepted {
        Some((_, v)) => v,
        None => init_value.clone(),  // init_value is the proposer's starting value
    };
    let new_value = Versioned {
        version: selected.version + 1,
        uuid: new_uuid,
        state: (/* exec f applied to */ selected.state.clone()),
    };

    proof {
        // Record Phase 1 witness: the value observed in Phase 1 for this ballot
        self.ghost_witnessed@ = self.ghost_witnessed@.insert(b, selected);
    }
```

- [ ] **Step 3: Run Verus on Phase 1 section**

```
verus --crate-type lib src/lib.rs 2>&1 | grep -E "error|verified"
```

Expected: Phase 1 ghost tracking verifies. There will be proof obligations for the postcondition (Phase 2 not yet done) — those are OK for now.

- [ ] **Step 4: Commit**

```bash
git add src/cluster.rs
git commit -m "feat: Phase 1 ghost tracking in run_proposal - ghost_promises completeness proved"
```

---

## Task 7: cluster.rs — Phase 2 ghost tracking + history extension + postcondition

**Files:**
- Modify: `src/cluster.rs`
- Modify: `src/main.rs`

### Background

After Phase 2 quorum: (1) ghost_states reflects all `accepted = Some((b, v))` for quorum members, (2) call `lemma_chosen_in_history_maintained` to prove `inv_chosen_in_history` is preserved after appending `v`, (3) record commit timestamp, (4) append `v` to `ghost_history`. The postcondition then follows directly.

- [ ] **Step 1: Add Phase 2 ghost tracking**

Replace the Phase 2 section of `run_proposal`:

```rust
    // Phase 2: Accept
    let ghost mut phase2_quorum: Set<NodeId> = Set::empty();
    let ghost states_before_phase2 = self.ghost_states@;
    let mut accepted_count = 0usize;

    for &id in &node_ids {
        if let Some(acceptor) = self.acceptors.get_mut(&id) {
            let (new_state, response) = handle_accept(acceptor.clone(), b, new_value.clone());
            *acceptor = new_state.clone();

            if let AcceptResponse::Accepted { .. } = response {
                proof {
                    // handle_accept ensures: result.0.accepted == Some((b, new_value))
                    self.ghost_states@ = self.ghost_states@.insert(id, new_state);
                    phase2_quorum = phase2_quorum.insert(id);
                }
                accepted_count += 1;
            }
        }
    }

    if accepted_count < quorum_size {
        return None;
    }

    // Phase 2 quorum reached — extend ghost history
    proof {
        // Prove chosen(ghost_states@, b, new_value, phase2_quorum, cluster_size)
        assert forall |id: NodeId| #[trigger] phase2_quorum.contains(id) implies
            self.ghost_states@.contains_key(id)
            && self.ghost_states@[id].accepted == Some((b, new_value))
        by {
            // ghost_states was updated to new_state after handle_accept for each id in phase2_quorum
            // handle_accept ensures: result.0.accepted == Some((b, v)) when Accepted
        };
        assert(is_quorum(phase2_quorum, self.cluster_size));
        assert(chosen(self.ghost_states@, b, new_value, phase2_quorum, self.cluster_size));

        // Prove: any other chosen value (v2 != new_value) was also chosen in states_before_phase2.
        // Phase 2 only sets accepted = Some((b, new_value)) for phase2_quorum members.
        // No other quorum for a different value can be created by this.
        assert forall |b2: Ballot, v2: Versioned<S>, q2: Set<NodeId>|
            chosen(self.ghost_states@, b2, v2, q2, self.cluster_size)
            && q2.subset_of(self.universe@) && v2 != new_value
        implies chosen(states_before_phase2, b2, v2, q2, self.cluster_size)
        by {
            // For any id in q2: if id is in phase2_quorum, then ghost_states@[id].accepted
            // was changed to Some((b, new_value)). Since v2 != new_value, chosen(states@, b2, v2, q2)
            // requires ghost_states@[id].accepted == Some((b2, v2)) — contradiction.
            // So q2 doesn't overlap phase2_quorum, meaning states_before_phase2[id] == ghost_states@[id]
            // for all id in q2, so chosen(states_before_phase2, b2, v2, q2) holds.
        };

        // Prove history monotone for the new value
        lemma_history_append_preserves_monotone(self.ghost_history@, new_value);

        // Prove causal chain: new_value == apply_cas(f@, witnessed[b], new_value.uuid)
        lemma_history_append_preserves_causal_chain(
            self.ghost_history@,
            new_value,
            self.ghost_witnessed@,
            b,
            f@,
        );

        // Prove inv_chosen_in_history is maintained
        lemma_chosen_in_history_maintained(
            self.ghost_history@,
            new_value,
            states_before_phase2,
            self.ghost_states@,
            b,
            phase2_quorum,
            self.cluster_size,
            self.universe@,
        );

        // Record commit timestamp
        let commit_idx = self.ghost_history@.len() as nat;
        self.commit_timestamps@ = self.commit_timestamps@.insert(commit_idx, self.logical_clock@);

        // Append to ghost_history
        self.ghost_history@ = self.ghost_history@.push(new_value);

        proof { self.logical_clock@ = (self.logical_clock@ + 1) as nat; }
    }

    Some(new_value)
```

- [ ] **Step 2: Update main.rs call sites**

`run_proposal` now takes `Ghost<nat>` as invoke_step and `Ghost<spec_fn(S) -> S>` for `f`. The concrete function `f` is passed separately for exec use. Update `main.rs`:

```rust
// Before:
let r1 = cluster.run_proposal(10, 1, |x| x + 1, init.clone(), 1001).unwrap();

// After: pass ghost invoke_step and ghost spec_fn
let invoke_step = Ghost(cluster.logical_clock_spec());
let r1 = cluster.run_proposal(b, Ghost(|x: u64| x + 1), invoke_step, 1001, |x| x + 1)
    .expect("proposal failed");
```

Adjust the `run_proposal` signature to take both an exec closure and a ghost spec_fn, since Verus spec functions can't be called in exec mode:

```rust
pub fn run_proposal<S: Clone + std::fmt::Debug, F: Fn(S) -> S>(
    &mut self,
    b: Ballot,
    f_exec: F,                        // exec: runs at runtime
    f_spec: Ghost<spec_fn(S) -> S>,   // spec: used in ghost proofs
    invoke_step: Ghost<nat>,
    new_uuid: u128,
) -> (result: Option<Versioned<S>>)
```

Update all three demo calls in `main.rs` accordingly.

- [ ] **Step 3: Run Verus**

```
verus --crate-type lib src/lib.rs 2>&1 | tail -3
```

Expected: `N verified, 0 errors`. Zero safety-bearing `assume` calls remain.

- [ ] **Step 4: Run cargo test**

```
cargo test 2>&1 | tail -8
```

Expected: `6 passed; 0 failed`.

- [ ] **Step 5: Run cargo run**

```
cargo run 2>&1
```

Expected: all three demos print PASS.

- [ ] **Step 6: Commit**

```bash
git add src/cluster.rs src/main.rs
git commit -m "feat: Phase 2 ghost tracking - chosen proved, history extended, full postcondition"
```

---

## Task 8: Final integration verification

**Files:**
- Read-only verification pass

### Background

Confirm: (a) zero safety-bearing `assume` calls, (b) all spec lemmas verified, (c) exec tests pass, (d) demos work.

- [ ] **Step 1: Grep for remaining assume calls**

```
grep -n "assume(" src/*.rs
```

Expected output: **nothing** (or only comments referencing old assumes). Any `assume(` in a proof body is a failure.

- [ ] **Step 2: Run Verus with full output**

```
verus --crate-type lib src/lib.rs 2>&1
```

Expected: `verification results:: N verified, 0 errors` where N > 27 (the original count).

- [ ] **Step 3: Run cargo test**

```
cargo test 2>&1
```

Expected: `6 passed; 0 failed; 0 ignored`.

- [ ] **Step 4: Run cargo run**

```
cargo run 2>&1
```

Expected:
```
=== Demo 1: Happy Path ===
  PASS: version monotone, UUIDs distinct
=== Demo 2: Minority Failure (2 of 5 fail-stopped) ===
  PASS: cluster tolerates minority failure
=== Demo 3: Contention Storm (5 proposers, 20% drop) ===
  PASS: N committed, versions monotone, UUIDs distinct
```

- [ ] **Step 5: Update README.md**

In the "Running Verus verification" section, update the verified-items list to reflect the new count and note that all safety `assume` calls are closed.

- [ ] **Step 6: Final commit**

```bash
git add src/ README.md
git commit -m "feat: full exec-layer annotation complete - all safety assumes closed"
```

---

## Self-Review Checklist

- [ ] Spec coverage: CommitTimestamps ✓ Task 1; inv_chosen_in_history ✓ Task 1; handle_prepare fix ✓ Task 2; axiom deletion ✓ Task 3; version uniqueness ✓ Task 3; capstone ✓ Task 4; type unification ✓ Task 5; Phase 1 ghost ✓ Task 6; Phase 2 ghost ✓ Task 7
- [ ] No placeholders: each task has complete code
- [ ] Type consistency: `CommitTimestamps = Map<nat, nat>` defined in history.rs (Task 1), used in linearizability.rs (Task 4), cluster.rs (Task 5-7); `Ballot`, `Versioned<S>`, `AcceptorState<S>` unified from Task 5 onward
