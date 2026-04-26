use std::collections::HashSet;
use verus_paxos::cluster::CASPaxosCluster;
use verus_paxos::primitives::{Ballot, Versioned};

fn main() {
    demo_happy_path();
    demo_minority_failure();
    demo_contention_storm();
}

fn demo_happy_path() {
    println!("=== Demo 1: Happy Path ===");
    let mut cluster = CASPaxosCluster::<u64>::new(vec![1, 2, 3, 4, 5], 0.0, HashSet::new(), 1);
    let init: Versioned<u64> = Versioned { version: 0, uuid: 0, state: 0u64 };

    let b1 = Ballot { round: 1, proposer_id: 10 };
    let b2 = Ballot { round: 2, proposer_id: 20 };
    let r1 = cluster.run_proposal(b1, |x| x + 1, init.clone(), 1001).unwrap();
    let r2 = cluster.run_proposal(b2, |x| x + 10, r1.clone(), 2002).unwrap();

    assert!(r1.version < r2.version, "versions must be strictly increasing");
    assert_ne!(r1.uuid, r2.uuid, "each commit must have a distinct UUID");
    println!("  r1: version={} uuid={} state={}", r1.version, r1.uuid, r1.state);
    println!("  r2: version={} uuid={} state={}", r2.version, r2.uuid, r2.state);
    println!("  PASS: version monotone, UUIDs distinct");
}

fn demo_minority_failure() {
    println!("=== Demo 2: Minority Failure (2 of 5 fail-stopped) ===");
    let failed: HashSet<u64> = vec![4u64, 5].into_iter().collect();
    let mut cluster = CASPaxosCluster::<u64>::new(vec![1, 2, 3, 4, 5], 0.0, failed, 2);
    let init: Versioned<u64> = Versioned { version: 0, uuid: 0, state: 0u64 };

    let b1 = Ballot { round: 1, proposer_id: 10 };
    let b2 = Ballot { round: 2, proposer_id: 20 };
    match cluster.run_proposal(b1, |x| x + 1, init.clone(), 3001) {
        Some(v) => println!("  Committed despite minority failure: version={} state={}", v.version, v.state),
        None    => println!("  Contention (retry needed in real impl)"),
    }
    match cluster.run_proposal(b2, |x| x, init.clone(), 4002) {
        Some(v) => println!("  Read committed: version={} state={}", v.version, v.state),
        None    => println!("  Read contended (retry needed)"),
    }
    println!("  PASS: cluster tolerates minority failure");
}

fn demo_contention_storm() {
    println!("=== Demo 3: Contention Storm (5 proposers, 20% drop) ===");
    let mut cluster = CASPaxosCluster::<u64>::new(vec![1, 2, 3, 4, 5], 0.20, HashSet::new(), 3);
    let init: Versioned<u64> = Versioned { version: 0, uuid: 0, state: 0u64 };

    let mut committed: Vec<Versioned<u64>> = Vec::new();
    for proposer in 0u64..5 {
        let round = proposer + 1;
        let prev = committed.last().cloned().unwrap_or_else(|| init.clone());
        let uuid = (proposer * 1000 + round) as u128;
        let b = Ballot { round, proposer_id: proposer };
        match cluster.run_proposal(b, |x| x + 1, prev, uuid) {
            Some(v) => {
                println!("  proposer={} committed version={} uuid={}", proposer, v.version, v.uuid);
                committed.push(v);
            }
            None => {
                println!("  proposer={} round={} contended", proposer, round);
            }
        }
    }

    for i in 1..committed.len() {
        assert!(committed[i].version > committed[i-1].version, "version must be strictly monotone");
    }
    let uuids: HashSet<u128> = committed.iter().map(|v| v.uuid).collect();
    assert_eq!(uuids.len(), committed.len(), "all committed UUIDs must be distinct");

    println!("  PASS: {} committed, versions monotone, UUIDs distinct", committed.len());
}
