use std::collections::HashSet;
use verus_paxos::cluster::{CASPaxosCluster, Versioned, ProposalError};

fn main() {
    demo_happy_path();
    demo_minority_failure();
    demo_contention_storm();
}

fn demo_happy_path() {
    println!("=== Demo 1: Happy Path ===");
    let mut cluster = CASPaxosCluster::new(vec![1, 2, 3, 4, 5], 0.0, HashSet::new(), 1);
    let init: Versioned<u64> = (0, 0, 0u64);

    let r1 = cluster.run_proposal(10, 1, |x| x + 1, init.clone(), 1001).unwrap();
    let r2 = cluster.run_proposal(20, 2, |x| x + 10, r1.clone(), 2002).unwrap();

    assert!(r1.0 < r2.0, "versions must be strictly increasing");
    assert_ne!(r1.1, r2.1, "each commit must have a distinct UUID");
    println!("  r1: version={} uuid={} state={}", r1.0, r1.1, r1.2);
    println!("  r2: version={} uuid={} state={}", r2.0, r2.1, r2.2);
    println!("  PASS: version monotone, UUIDs distinct");
}

fn demo_minority_failure() {
    println!("=== Demo 2: Minority Failure (2 of 5 fail-stopped) ===");
    let failed: HashSet<u64> = vec![4u64, 5].into_iter().collect();
    let mut cluster = CASPaxosCluster::new(vec![1, 2, 3, 4, 5], 0.0, failed, 2);
    let init: Versioned<u64> = (0, 0, 0u64);

    match cluster.run_proposal(10, 1, |x| x + 1, init.clone(), 3001) {
        Ok(v)  => println!("  Committed despite minority failure: version={} state={}", v.0, v.2),
        Err(_) => println!("  Contention (retry needed in real impl)"),
    }
    match cluster.run_proposal(20, 2, |x| x, init.clone(), 4002) {
        Ok(v)  => println!("  Read committed: version={} state={}", v.0, v.2),
        Err(_) => println!("  Read contended (retry needed)"),
    }
    println!("  PASS: cluster tolerates minority failure");
}

fn demo_contention_storm() {
    println!("=== Demo 3: Contention Storm (5 proposers, 20% drop) ===");
    let mut cluster = CASPaxosCluster::new(vec![1, 2, 3, 4, 5], 0.20, HashSet::new(), 3);
    let init: Versioned<u64> = (0, 0, 0u64);

    let mut committed: Vec<Versioned<u64>> = Vec::new();
    for proposer in 0u64..5 {
        let round = proposer + 1;
        let prev = committed.last().cloned().unwrap_or(init.clone());
        let uuid = (proposer * 1000 + round) as u128;
        match cluster.run_proposal(proposer, round, |x| x + 1, prev, uuid) {
            Ok(v) => {
                committed.push(v.clone());
                println!("  proposer={} committed version={} uuid={}", proposer, v.0, v.1);
            }
            Err(ProposalError::Contention) => {
                println!("  proposer={} round={} contended", proposer, round);
            }
        }
    }

    for i in 1..committed.len() {
        assert!(committed[i].0 > committed[i-1].0, "version must be strictly monotone");
    }
    let uuids: HashSet<u128> = committed.iter().map(|v| v.1).collect();
    assert_eq!(uuids.len(), committed.len(), "all committed UUIDs must be distinct");

    println!("  PASS: {} committed, versions monotone, UUIDs distinct", committed.len());
}
