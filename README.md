# verus-paxos
experiment combining verus with simulation testing of simple CASPaxos implementation

## Running Verus verification

Install Verus from https://github.com/verus-lang/verus/releases and put the binary on your `PATH`, or note its location.

```sh
# Verify all five layers (27 items, 0 errors expected)
verus --crate-type lib src/lib.rs
```

With a non-`PATH` binary:

```sh
/path/to/verus --crate-type lib src/lib.rs
```

Expected output:

```
verification results:: 27 verified, 0 errors
```

The verified items span:

- **Layer 1** (`primitives.rs`) — ballot ordering, quorum intersection, `apply_cas` version increment
- **Layer 2** (`acceptor.rs`) — `inv_acceptor` preservation through prepare/accept, `select_value` version maximality
- **Layer 3** (`quorum.rs`) — single-value-per-ballot agreement, higher-ballot version witness
- **Layer 4** (`history.rs`) — `ChosenHistory` monotonicity and causal chain preserved under append
- **Layer 5** (`linearizability.rs`) — linearizability capstone theorem structure

A handful of residual `assume(...)` calls mark honest proof obligations documented in comments — primarily the cross-ballot version-uniqueness induction and the time-index correspondence needed for a fully closed linearizability proof.

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
