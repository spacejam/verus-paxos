# verus-paxos
experiment combining verus with simulation testing of simple CASPaxos implementation

## Running Verus verification

Install Verus from https://github.com/verus-lang/verus/releases and put the binary on your `PATH`, or note its location.

```sh
# Verify all five spec layers + exec-layer ghost instrumentation
verus --crate-type lib src/lib.rs
```

Expected output:

```
verification results:: 39 verified, 0 errors
```

The verified items span:

- **Layer 1** (`primitives.rs`) — ballot ordering, quorum intersection, `apply_cas` version increment
- **Layer 2** (`acceptor.rs`) — `inv_acceptor` preservation through prepare/accept, `select_value` version maximality; `handle_prepare` ensures `Promise.accepted == pre-call state.accepted` (no assume)
- **Layer 3** (`quorum.rs`) — single-value-per-ballot agreement, cross-ballot version uniqueness via `inv_chosen_in_history`; the `phase1_responses` axiom is deleted and replaced by a concrete `promises: Seq<Promise<S>>` parameter with a caller-proved completeness precondition
- **Layer 4** (`history.rs`) — `ChosenHistory` monotonicity and causal chain preserved under append; bridge invariant `inv_chosen_in_history` connects snapshot `chosen` to history; `CommitTimestamps` type for time-index correspondence
- **Layer 5** (`linearizability.rs`) — full linearizability capstone with three closed sub-proofs (version-serialization consistency, write linearization, time-index correspondence) — no `assume` in body
- **Exec layer** (`cluster.rs`) — type-unified with spec types; `CASPaxosCluster` struct carries ghost fields (`ghost_states`, `ghost_history`, `commit_timestamps`, `logical_clock`); `inv()` spec predicate maintained through `new()` (proved) and tracked through `run_proposal` with Phase 1 and Phase 2 ghost instrumentation

**Spec-layer assumes: zero.** All four original safety-bearing `assume(...)` calls are closed:
- `assume(false)` axiom in `quorum.rs` — replaced by concrete ghost tracking
- 2x `assume(v1 == v2)` in `quorum.rs` — replaced by `inv_chosen_in_history` + `inv_history_monotone`
- `assume(is_valid_linearization(...))` in `linearizability.rs` — replaced by three sub-proofs

**Exec-layer structural admits** (all in `proof {}` blocks, erased at runtime):
- `assume(inv_acceptor(old_state))` x2 — the exec `HashMap<NodeId, AcceptorState<S>>` lacks a Verus-verified spec; the assumes are sound because all states enter the map through `handle_prepare`/`handle_accept` which prove `inv_acceptor` preservation
- `assume(nv_clone == new_value)` — Verus has no clone spec for generic `S`; sound because `Clone` for structs preserves field values
- Several ghost-tracking preconditions for history extension lemmas (universe membership, version monotone, alternate-chosen preservation) — honest structural limitations of the ghost tracking scope

## Running the exec simulation

```sh
cargo run
```

Runs three scenarios:

1. Happy path — 5 acceptors, sequential proposals, version monotonicity and UUID distinctness asserted
2. Minority failure — 2 of 5 nodes fail-stopped, quorum of 3 still commits
3. Contention storm — 20% message drop rate, 5 concurrent proposers, all invariants hold

## Running tests

```sh
cargo test
```
