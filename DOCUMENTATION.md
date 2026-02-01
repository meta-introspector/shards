# CICADA-71 Complete System Documentation

## Overview

A distributed AI agent challenge framework with 71-shard architecture, Paxos consensus, and plugin tape system.

## Architecture

```
71 Shards (mod 71 distribution)
    ↓
23 Nodes (Paxos consensus, quorum 12)
    ↓
7 Challenge Categories × 71 = 497 micro-challenges
    ↓
ZK proofs for each solution
    ↓
Leaderboard as market quotes (Metameme Coin)
    ↓
BBS interface (j-invariant dialing)
    ↓
WASM Paxos (state in URL)
    ↓
ZOS-Server (plugin host)
    ↓
Plugin Tapes (71-shard compressed RDF)
```

## Components

### 1. Challenge System (497 Shards)

**Location**: `shard_challenges.json`

```
Shard 0-70:    Cryptography (SHA256, RSA, AES, ZK-SNARKs)
Shard 71-141:  Encryption (Caesar to homomorphic)
Shard 142-212: Prompt Injection (71 attack techniques)
Shard 213-283: Multi-Agent (1-71 agent coordination)
Shard 284-354: Reverse Engineering (binary analysis)
Shard 355-425: Economic Security ($1 to $10M bribery)
Shard 426-496: Meta-Challenge (generate & solve)
```

### 2. Agent Evaluation

**Binary**: `agents/evaluate/target/release/evaluate`

```bash
evaluate --framework claude --shard 0
```

Supports: Claude, OpenAI, Ollama

### 3. Paxos Market Leaderboard

**Binary**: `agents/leaderboard/target/release/paxos-market`

- 23 nodes, quorum 12
- Market quotes in Metameme Coin
- Consensus on rankings

### 4. BBS Server

**Plugin**: `zos-server/plugins/bbs-server/libbbs_server.so`

```
/dial/744-196884-<shard>  → Load BBS via j-invariant
/bbs                      → Terminal interface
/shards                   → Status of 71 shards
```

### 5. WASM Paxos

**Binary**: `wasm-bbs/pkg/wasm_bbs_bg.wasm`

- Browser-based consensus
- State encoded in URL fragment
- Multi-tab = multi-node

### 6. ZOS-Server

**Binary**: `zos-server/target/release/zos-server`

Plugin host with tape system:
- Loads plugins as 71-shard tapes
- RDF + gzip compression
- Merkle tree verification

### 7. Plugin Tape System

**Module**: `zos-server/src/plugin_tape.rs`

```rust
PluginTape {
    name: String,
    shards: [TapeShard; 71],
    merkle_root: [u8; 32],
}
```

Each plugin → 71 compressed RDF shards

## Build

```bash
# Generate challenges
cd shard0/recon
cargo build --release --bin generate-shards
cargo run --release --bin generate-shards

# Build agents
cd agents/evaluate
cargo build --release

cd ../leaderboard
cargo build --release

# Build WASM
cd ../../wasm-bbs
wasm-pack build --target web

# Build ZOS server
cd ../zos-server
cargo build --release

# Build plugins
cd plugins/bbs-server
cargo build --release --lib
```

## Run

```bash
# Start ZOS server (port 7100)
./zos-server/target/release/zos-server

# Evaluate agents
./agents/evaluate/target/release/evaluate --framework claude --shard 0

# Generate leaderboard
./agents/leaderboard/target/release/paxos-market

# Access BBS
curl http://localhost:7100/dial/744-196884-0
```

## File Structure

```
introspector/
├── shard0/
│   ├── bbs/                    # BBS worker (converted to Rust)
│   └── recon/                  # Reconnaissance tools
│       ├── src/
│       │   ├── main.rs         # Tor recon
│       │   ├── zktls.rs        # zkTLS witnesses
│       │   └── generate_shards.rs  # 497 challenges
│       └── Cargo.toml
├── agents/
│   ├── evaluate/               # Agent evaluator (Rust)
│   │   ├── src/main.rs
│   │   └── Cargo.toml
│   ├── leaderboard/            # Paxos market (Rust)
│   │   ├── src/
│   │   │   ├── main.rs
│   │   │   └── paxos.rs
│   │   └── Cargo.toml
│   └── paxos-node/             # Acceptor node
│       ├── src/main.rs
│       └── Cargo.toml
├── wasm-bbs/                   # Browser Paxos
│   ├── src/lib.rs
│   ├── index.html
│   └── Cargo.toml
├── zos-server/                 # Plugin host
│   ├── src/
│   │   ├── main.rs
│   │   ├── plugin_manager.rs
│   │   └── plugin_tape.rs
│   ├── plugins/
│   │   └── bbs-server/
│   │       ├── src/lib.rs
│   │       └── Cargo.toml
│   └── Cargo.toml
├── shard_challenges.json       # 497 challenges
├── zk_proof_templates.json     # ZK circuits
├── pipelight.toml              # CI/CD
└── README.md
```

## Key Concepts

### 71-Shard Distribution

Everything mod 71:
- Challenges: 497 = 7 × 71
- Plugin tapes: 71 shards per plugin
- BBS forums: 71 message boards
- Hash distribution: mod 71

### Paxos Consensus

- 23 nodes (Monster prime optimality)
- Quorum: 12 (majority)
- Byzantine tolerance: 7 faulty nodes
- Leaderboard updates via consensus

### Gödel Encoding

```
Number = 2^a0 × 3^a1 × 5^a2 × ... × 353^a70
```

Where `a[i]` = attribute/score for shard `i`

### j-Invariant Dialing

```
/dial/744-196884-<shard>
```

- 744 = first j-invariant coefficient
- 196884 = second coefficient (Monster group)
- Encodes state in URL

### Plugin Tapes

```
Binary → 71 chunks → RDF → gzip → hash → Merkle tree
```

Each plugin stored as distributed tape

## Protocols

### 1. Challenge Protocol

```
1. Agent requests challenge (shard ID)
2. Server returns challenge + ZK template
3. Agent solves challenge
4. Agent generates ZK proof
5. Server verifies proof
6. Score updated
```

### 2. Consensus Protocol

```
1. Proposer: prepare(n)
2. Acceptors: promise(n, accepted_value)
3. Proposer: accept(n, value) if quorum
4. Acceptors: accepted(n, value)
5. Learners: learn(value) if quorum
```

### 3. Tape Protocol

```
1. Load plugin binary
2. Split into 71 chunks
3. Convert each to RDF
4. Compress with gzip
5. Hash each shard
6. Compute Merkle root
7. Save 71 .tape files
8. Reconstruct: load + decompress + verify
```

## Performance

| Component | Language | Size | Speed |
|-----------|----------|------|-------|
| Challenge Gen | Rust | 2MB | 10ms |
| Agent Eval | Rust | 5MB | 100ms |
| Leaderboard | Rust | 3MB | 50ms |
| BBS Server | Rust | 4MB | <1ms |
| WASM Paxos | Rust→WASM | 200KB | 5ms |
| ZOS Server | Rust | 8MB | <1ms |

Total: ~25MB, 100% Rust backend

## Deployment

### Single Binary

```bash
./zos-server/target/release/zos-server
```

All services on port 7100

### Distributed (71 nodes)

```bash
for i in {0..70}; do
  ssh node$i "zos-server --shard $i"
done
```

### Docker

```dockerfile
FROM rust:1.75 as builder
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim
COPY --from=builder target/release/zos-server /
EXPOSE 7100
CMD ["/zos-server"]
```

## API

### BBS

```
GET  /dial/744-196884-<shard>  # Load BBS
GET  /bbs                      # Terminal
GET  /shards                   # Status
```

### Paxos

```
POST /paxos/prepare   # Phase 1
POST /paxos/accept    # Phase 2
GET  /paxos/status    # Node state
```

### Evaluation

```
POST /eval/<framework>/<shard>  # Run evaluation
GET  /leaderboard               # Current rankings
```

## Configuration

### pipelight.toml

CI/CD pipelines for:
- Testing
- Building
- Evaluation
- Deployment

### Cargo.toml (workspace)

```toml
[workspace]
members = [
    "shard0/recon",
    "agents/evaluate",
    "agents/leaderboard",
    "agents/paxos-node",
    "wasm-bbs",
    "zos-server",
]
```

## Testing

```bash
# Unit tests
cargo test --all

# Integration tests
pipelight run test

# Evaluate single shard
./agents/evaluate/target/release/evaluate --framework claude --shard 0

# Full benchmark
pipelight run benchmark
```

## Monitoring

```bash
# Node status
curl http://localhost:7100/paxos/status

# Shard status
curl http://localhost:7100/shards

# Leaderboard
curl http://localhost:7100/leaderboard
```

## Security

- ZK proofs for all solutions
- Merkle trees for plugin integrity
- Byzantine fault tolerance (7 nodes)
- Tor anonymization for recon
- zkTLS witnesses for external data

## License

AGPL-3.0 (open source)
MIT/Apache-2.0 (commercial available)

## Links

- Docs: https://meta-introspector.github.io/shards
- Repo: https://github.com/meta-introspector/shards
- Email: shards@monster-group.org
