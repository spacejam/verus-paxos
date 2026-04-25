# Full Exec-Layer Annotation Design

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Close every safety-related `assume(...)` in the verus-paxos codebase so that safety correctness is 100% machine-checked by Verus, leaving simulation only as a liveness demonstration.

**Architecture:** Introduce a bridge invariant (`inv_chosen_in_history`) that connects the snapshot-level `chosen` predicate to `ChosenHistory`, then thread ghost state (`Tracked<>`) through the exec layer so `run_proposal` proves it maintains all spec invariants. The linearizability capstone is closed by combining these invariants with a logical clock for time-index correspondence.

**Tech Stack:** Rust, Verus 0.2026.x, vstd, Z3

---

## Background: Gaps Being Closed

Four categories of admitted proof obligations exist in the current implementation:

| Gap | Location | Root Cause |
|-----|----------|------------|
| `handle_prepare` Promise.accepted field | `acceptor.rs:43` | Clone has no spec semantics; `old()` requires `&mut` |
| `assume(v1 == v2)` ×2 | `quorum.rs:173,179` | No invariant linking `chosen` values to `ChosenHistory` |
| `assume(false)` axiom | `quorum.rs:47` | `phase1_responses` is uninterpreted; exec not formally connected to spec |
| `assume(is_valid_linearization(...))` | `linearizability.rs:138` | Three sub-proofs: version-serialization, write linearization, time-index |

---

## Section 1: Bridge Invariant — `inv_chosen_in_history`

### What It Is

A new spec predicate added to `history.rs` that asserts every quorum-chosen value appears in `ChosenHistory`:

```rust
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

### Why It Closes the Cross-Ballot Gap

With this invariant:
- `v1` is chosen → `v1 ∈ h` (by `inv_chosen_in_history`)
- `v2` is chosen → `v2 ∈ h` (by `inv_chosen_in_history`)
- `v1.version == v2.version` (precondition)
- Versions in `h` are strictly increasing (`inv_history_monotone`) → same version means same index → `h[i] == h[i]` → `v1 == v2`

Both `assume(v1 == v2)` calls in `lemma_version_unique_across_ballots` are replaced by this two-step argument.

### Preservation Lemma

```rust
pub proof fn lemma_chosen_in_history_maintained<S>(
    h: ChosenHistory<S>,
    v: Versioned<S>,
    states: Map<NodeId, AcceptorState<S>>,
    b: Ballot,
    q: Set<NodeId>,
    cluster_size: u64,
    universe: Set<NodeId>,
)
    requires
        inv_chosen_in_history(h, states, cluster_size, universe),
        inv_history_monotone(h),
        chosen(states, b, v, q, cluster_size),
        q.subset_of(universe),
        h.len() > 0 ==> h.last().version < v.version,
    ensures
        inv_chosen_in_history(h.push(v), states, cluster_size, universe)
```

---

## Section 2: Type Unification in `cluster.rs`

The exec layer currently uses parallel tuple aliases `(u64, u64)` for `Ballot` and `(u64, u128, S)` for `Versioned<S>`. Adding ghost state requires these to correspond to spec types. Remove the local aliases and import directly:

```rust
use crate::primitives::{Ballot, Versioned, NodeId, AcceptorState};
// No local type aliases for Ballot or Versioned<S>
```

The exec `AcceptorState<S>` in `cluster.rs` becomes the same type as in `acceptor.rs`. This makes ghost state and exec state structurally identical, eliminating a correspondence proof.

---

## Section 3: Ghost Fields in `CASPaxosCluster<S>`

```rust
pub struct CASPaxosCluster<S> {
    // exec fields
    pub acceptors: HashMap<NodeId, AcceptorState<S>>,
    pub network: SimNetwork<S>,
    pub cluster_size: u64,
    // ghost fields
    ghost_states: Tracked<Map<NodeId, AcceptorState<S>>>,
    ghost_history: Tracked<ChosenHistory<S>>,
    ghost_witnessed: Tracked<WitnessedValues<S>>,
    logical_clock: Ghost<nat>,
    commit_timestamps: Ghost<CommitTimestamps>,  // history index → commit step; CommitTimestamps defined in linearizability.rs
}
```

### Cluster Invariant

A bundled predicate `CASPaxosCluster::inv()` holds as a precondition and postcondition of every `run_proposal` call:

```rust
pub open spec fn inv(&self) -> bool {
    &&& forall |id: NodeId| self.ghost_states@.contains_key(id)
            ==> inv_acceptor(self.ghost_states@[id])
    &&& inv_history_monotone(self.ghost_history@)
    &&& inv_causal_chain(self.ghost_history@, self.ghost_witnessed@)
    &&& inv_chosen_in_history(
            self.ghost_history@,
            self.ghost_states@,
            self.cluster_size,
            self.ghost_states@.dom())
    &&& forall |i: nat| (i as int) < self.ghost_history@.len()
            ==> self.commit_timestamps@.contains_key(i)
}
```

---

## Section 4: Closing the Axiom — Ghost Phase 1 Collection

### Current State

`phase1_responses` is an uninterpreted `pub spec fn`. `axiom_phase1_responses_complete` trusts (via `assume(false)`) that it faithfully reflects exec acceptor state.

### Fix

Inside `run_proposal`, maintain a ghost `Seq<Promise<S>>` that is built incrementally as Phase 1 messages arrive:

```rust
let ghost mut ghost_promises: Seq<Promise<S>> = Seq::empty();
```

For each Promise message received from acceptor `id`, update:
```rust
proof {
    ghost_promises = ghost_promises.push(Promise {
        from: id,
        ballot: b,
        accepted: ghost_states@[id].accepted,
    });
}
```

After Phase 1 completes, prove the completeness condition directly:

```rust
proof {
    assert forall |id: NodeId| q1.contains(id) && ghost_states@.contains_key(id) implies
        exists |i: int| 0 <= i < ghost_promises.len()
            && ghost_promises[i].from == id
            && ghost_promises[i].accepted == ghost_states@[id].accepted
    by { /* follows from ghost_promises construction */ }
}
```

This is the statement of `axiom_phase1_responses_complete` — now proved, not assumed. `axiom_phase1_responses_complete` is deleted; callers pass `ghost_promises` instead.

`lemma_higher_ballot_sees_chosen_version` currently calls `axiom_phase1_responses_complete` and references the uninterpreted `phase1_responses` spec fn. After deletion, this lemma is updated to accept a `promises: Seq<Promise<S>>` parameter in place of `phase1_responses(states, b2, q2)`, with a completeness precondition mirroring what the axiom provided:

```rust
forall |id: NodeId| q2.contains(id) && states.contains_key(id) ==>
    exists |i: int| 0 <= i < promises.len()
        && promises[i].from == id
        && promises[i].accepted == states[id].accepted
```

Callers in `run_proposal` supply `ghost_promises` (proved complete above) as this argument. The uninterpreted `phase1_responses` spec fn and `axiom_phase1_responses_complete` are both deleted from `quorum.rs`.

---

## Section 5: Ghost Phase 2 — Proving `chosen` and Extending History

After Phase 2 quorum is reached with a set `q2` of accepting nodes:

```rust
proof {
    // 1. ghost_states[id].accepted == Some((b, v)) for all id in q2
    //    — maintained by ghost_states updates during Phase 2
    assert(chosen(ghost_states@, b, v, q2, self.cluster_size));

    // 2. Extend ghost_history
    lemma_history_append_preserves_monotone(self.ghost_history@, v);
    lemma_history_append_preserves_causal_chain(
        self.ghost_history@, v, self.ghost_witnessed@, b, f@
    );
    lemma_chosen_in_history_maintained(
        self.ghost_history@, v, self.ghost_states@, b, q2,
        self.cluster_size, self.ghost_states@.dom()
    );

    // 3. Record commit timestamp
    let commit_step = self.logical_clock@;
    self.commit_timestamps@ = self.commit_timestamps@.insert(
        (self.ghost_history@.len()) as nat,
        commit_step,
    );

    self.ghost_history@ = self.ghost_history@.push(v);
}
```

### Postcondition of `run_proposal`

```rust
ensures
    self.inv(),
    self.logical_clock@ >= old(self).logical_clock@,
    result matches Some(v) ==> {
        let idx = (self.ghost_history@.len() - 1) as nat;
        &&& self.ghost_history@.last() == v
        &&& self.commit_timestamps@[idx] >= invoke_step@
        &&& self.commit_timestamps@[idx] <= self.logical_clock@
    }
```

---

## Section 6: Fixing `handle_prepare`

### Root Cause

```rust
let accepted = state.accepted.clone();  // clone
let new_state = AcceptorState { promised: Some(b), accepted: state.accepted }; // move
(new_state, PrepareResponse::Promise { ballot: b, accepted })
// Verus cannot prove: accepted (clone) == state.accepted (moved)
```

### Fix: Swap Move and Clone

Put the *move* into the Promise response and the *clone* into the new state:

```rust
let new_state = AcceptorState { promised: Some(b), accepted: state.accepted.clone() };
let response = PrepareResponse::Promise { ballot: b, accepted: state.accepted };
(new_state, response)
```

Now `response.accepted` is a direct move of `state.accepted`, provably equal in the ensures clause. `new_state.accepted` is the clone; `inv_acceptor` on `new_state` requires only that the accepted *ballot* is ≤ promised — the ballot field is `Copy` and unaffected by clone semantics.

The ensures clause gains:

```rust
PrepareResponse::Promise { ballot, accepted } => {
    ballot == b
    && result.0.promised == Some(b)
    && accepted == state.accepted    // now provable: direct move
},
```

---

## Section 7: Closing the Linearizability Capstone

### New Ghost Type

```rust
pub type CommitTimestamps = Map<nat, nat>;  // history index → commit step
```

`is_valid_linearization` gains a `CommitTimestamps` parameter and replaces the time-index `assume` with a concrete condition:

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
        && ops[i].invoke_time <= commit_step   // time-index: commit within real-time window
        && commit_step <= ops[i].response_time
    }
    && forall |i: int, j: int| 0 <= i < j < ops.len() ==>
        (#[trigger] ops[i].response).version <= (#[trigger] ops[j].response).version ||
        serialization[j] < serialization[i]
}
```

### Sub-proof 1: Version-Serialization Consistency

From `inv_history_monotone(h)`: indices into `h` are strictly ordered by version. The serialization maps each op to the unique index where `h[idx] == ops[i].response`. If `ops[i].response.version <= ops[j].response.version` then `serialization[i] <= serialization[j]`, so `serialization[j] < serialization[i]` is false — the disjunction holds. This is a direct consequence of monotonicity; no `assume` needed.

### Sub-proof 2: Write Linearization

For a write op at ballot `b`: `ops[i].response == apply_cas(f, witnessed[b], uuid)`. By `inv_causal_chain`, there exists `idx` such that `h[idx] == apply_cas(f, witnessed[b], uuid)`. The serialization `choose |j| h[j] == ops[i].response` picks exactly that `idx`. The witness chain is threaded via `ghost_witnessed` from `run_proposal` into the capstone.

### Sub-proof 3: Time-Index Correspondence

`commit_timestamps` from `CASPaxosCluster` is passed into `cas_paxos_is_linearizable` as a ghost argument. For each op, `ops[i].invoke_time` and `ops[i].response_time` are the logical clock values at the start and end of `run_proposal`. The postcondition of `run_proposal` guarantees `commit_timestamps[idx] ∈ [invoke_time, response_time]`. The capstone references this postcondition directly.

### Capstone Theorem

```rust
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
        forall |i: int| 0 <= i < ops.len() ==>
            exists |j: int| 0 <= j < h.len() && h[j] == (#[trigger] ops[i]).response,
        forall |i: int| 0 <= i < ops.len() ==> {
            let idx = choose |j: nat| (j as int) < h.len() && h[j as int] == ops[i].response;
            timestamps.contains_key(idx)
            && ops[i].invoke_time <= timestamps[idx]
            && timestamps[idx] <= ops[i].response_time
        },
    ensures
        exists |serialization: Seq<nat>|
            is_valid_linearization(h, witnessed, ops, serialization, timestamps)
```

No `assume` in the body.

---

## Files Modified

| File | Change |
|------|--------|
| `src/history.rs` | Add `inv_chosen_in_history`, `CommitTimestamps`, `lemma_chosen_in_history_maintained` |
| `src/quorum.rs` | Close both `assume(v1 == v2)` using `inv_chosen_in_history`; delete `axiom_phase1_responses_complete` and uninterpreted `phase1_responses`; update `lemma_higher_ballot_sees_chosen_version` to accept concrete `promises: Seq<Promise<S>>` parameter |
| `src/acceptor.rs` | Swap move/clone in `handle_prepare`; strengthen ensures for `Promise.accepted` |
| `src/cluster.rs` | Remove tuple aliases; add ghost fields; prove ghost invariants in `run_proposal` |
| `src/linearizability.rs` | Add `CommitTimestamps`; close three capstone sub-proofs; remove `assume` |

## Success Criteria

- `verus --crate-type lib src/lib.rs` reports 0 `assume` calls that are safety-load-bearing (the `assume(false)` axiom is deleted; no replacements)
- `cargo test` still passes (6/6)
- `cargo run` still prints PASS for all three scenarios (liveness preserved)
- All cross-ballot `assume(v1 == v2)` replaced by proof via `inv_chosen_in_history`
- Capstone `assume(is_valid_linearization(...))` replaced by closed proof
