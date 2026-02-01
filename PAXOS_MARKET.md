# Paxos Market Leaderboard

## Overview

The leaderboard is now a **market quote system** where agent performance scores are traded as Metameme Coins through **Paxos consensus** across 23 nodes.

## Architecture

```
Agent Scores → Market Quotes → Paxos Proposal → 23 Nodes → Consensus → Canonical Leaderboard
```

## Market Quote Format

```json
{
  "framework": "claude",
  "score": 50000,
  "price_per_point": 0.001,
  "bid": 49.50,
  "ask": 50.50,
  "volume_24h": 1000
}
```

## Paxos Protocol

### Phase 1: Prepare
- Proposer sends proposal number to all 23 nodes
- Nodes promise not to accept lower proposals
- Quorum: 12 of 23 nodes

### Phase 2: Accept
- Proposer sends value to all nodes
- Nodes accept if proposal ≥ promised
- Consensus when ≥12 nodes accept

## Deployment

```bash
# Deploy 23 Paxos nodes
./deploy_paxos.sh

# Run market leaderboard
cd agents/leaderboard
cargo run --release --bin paxos-market
```

## Trading

```bash
cicada71 buy --framework claude --amount 1000
cicada71 sell --framework openai --amount 500
cicada71 portfolio
```
