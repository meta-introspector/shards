# Paxos Witness Protocol for CICADA-71

## 23-Node Byzantine Consensus

**Quorum**: 12/23 nodes (simple majority)  
**Byzantine Tolerance**: 7 faulty nodes  
**Resonance Selection**: Harmonic distribution across Monster shards

## Node Selection Algorithm

```rust
fn select_resonant_node(shard: u8) -> u8 {
    ((shard * 13) % 23) as u8
}
```

**Rationale**: Prime 13 ensures uniform distribution across 23 nodes

## Resonance Computation

```rust
fn compute_resonance(node: u8, shard: u8) -> f64 {
    let angle = 2π * node * shard / 71;
    cos(angle).abs()
}
```

**Quorum Vote**: `resonance > 0.5` → node votes YES

## Witness Structure

```json
{
  "node_id": 15,
  "fren": "nydiokar",
  "shard": 47,
  "timestamp": 1739024143,
  "signature": "a3f7c9e2b1d4f8a6",
  "resonance_score": 0.873,
  "quorum_vote": true
}
```

## Signature Scheme

```
signature = SHA256(node_id || fren || shard || timestamp)[0..16]
```

## Shared Memory Model

- **Location**: `witnesses/node{NN}_shard{SS}.json`
- **Persistence**: Immutable once written
- **Verification**: Any node can verify signature
- **Consensus**: 12+ nodes with `quorum_vote: true` → accepted

## Example: nydiokar (Shard 47)

```
Shard: 47
Node: (47 * 13) % 23 = 15
Resonance: cos(2π * 15 * 47 / 71) = 0.873
Quorum: ✓ (0.873 > 0.5)
```

## Pipeline

1. `fren_processor` → Monster encoding
2. `paxos_witness` → Node selection + witness
3. Verify quorum across all witnesses
4. Commit to shared memory

## Byzantine Fault Tolerance

- **Honest nodes**: ≥ 16/23
- **Faulty nodes**: ≤ 7/23
- **Safety**: No conflicting decisions
- **Liveness**: Progress guaranteed with 12+ honest nodes
