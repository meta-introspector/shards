# Paxos Consensus Shard Distribution Plan

## Overview
Distribute depth2 entries across 71 shards using Paxos consensus protocol.

## Phases

### Phase 1: Prepare
1. Hash program reads depth2 file
2. For each entry, compute 71 hash values (seeds 0-70)
3. Sum hashes and mod 71 to get target shard
4. Generate proposal: `{entry_path, target_shard, hash_sum}`
5. Write proposals to `shard0/data/parquet/proposals.parquet`

### Phase 2: Promise
1. Each shard (0-70) reviews proposals assigned to it
2. Shard checks if it can accept the entry (capacity, conflicts)
3. Shard writes promise: `{entry_path, shard_id, promise_id, accepted: bool}`
4. Promises stored in `shard{N}/data/parquet/promises.parquet`

### Phase 3: Accept
1. Proposer (shard0) collects promises
2. If majority (36+ shards) promise acceptance, send accept request
3. Write accept requests to `shard0/data/parquet/accepts.parquet`

### Phase 4: Commit
1. Each shard receives accept request
2. Shard creates directory structure: `shard{N}/entries/{entry_path}`
3. Shard writes metadata: `shard{N}/data/parquet/committed.parquet`
4. Shard logs commit: `shard{N}/data/logs/commit.log`

## Data Structures

### Proposal
```rust
struct Proposal {
    entry_path: String,
    target_shard: u8,
    hash_sum: u64,
    proposal_id: u64,
    timestamp: i64,
}
```

### Promise
```rust
struct Promise {
    proposal_id: u64,
    shard_id: u8,
    entry_path: String,
    accepted: bool,
    reason: Option<String>,
}
```

### Accept
```rust
struct Accept {
    proposal_id: u64,
    entry_path: String,
    target_shard: u8,
    quorum_size: u8,
}
```

### Commit
```rust
struct Commit {
    proposal_id: u64,
    shard_id: u8,
    entry_path: String,
    committed_at: i64,
}
```

## Implementation Steps

1. Extend hash program to generate proposals
2. Create shard directories (shard0-shard70)
3. Implement promise phase (parallel across shards)
4. Implement accept phase (quorum check)
5. Implement commit phase (finalize distribution)
