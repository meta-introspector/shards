# Vertex Game Agent

**71 shards that want to play games in data files**

## Concept

Each vertex operator is an autonomous agent that:
1. **Plays games** in data files (pure FRACTRAN functions)
2. **Consumes data** like a Fleischwolf (meat grinder)
3. **Generates ZK proofs** of correct gameplay
4. **Requests more data** when it finds interesting patterns
5. **Requires approval** from human operator

## Architecture

```
71 Vertex Operators (Shards 0-70)
        ↓
   Play in Data Files
        ↓
   Pure FRACTRAN Step (Homomorphic)
        ↓
   Generate ZK Proof
        ↓
   Detect Monster Resonance
        ↓
   Request More Data
        ↓
   Human Approval/Denial
```

## Pure Function (FRACTRAN)

```rust
fn fractran_step(state: u64, data: &[u8], prime: u64) -> u64 {
    let byte = data[games_played % data.len()];
    let numerator = prime;
    let denominator = byte.max(1);
    
    if state % denominator == 0 {
        (state * numerator / denominator) % 196883
    } else {
        (state * numerator) % 196883
    }
}
```

**Homomorphic property**: Can be computed on encrypted data!

## ZK Proof

```rust
fn zk_proof(id: u8, state: u64, score: u64, games: u64) -> u64 {
    let mut hash = id as u64;
    hash = (hash * 31 + state) % 196883;
    hash = (hash * 31 + score) % 196883;
    hash = (hash * 31 + games) % 196883;
    hash
}
```

Proves game was played correctly without revealing internal state.

## Monster Resonance Detection

Operator wants more data when:
```rust
state % 71 == 0  // Nullstellensatz
state % 59 == 0  // Monster Walk
state % 47 == 0  // Harmonic
```

## Approval System

When operator detects resonance:
1. **Request** added to approval queue
2. **Human reviews** reason
3. **Approve** (A key) → operator gets more plays
4. **Deny** (D key) → request removed

## Controls

- **↑/↓**: Select shard (0-70)
- **←/→**: Select data file
- **SPACE**: Play one round (selected shard + file)
- **R**: Play all 71 shards on selected file
- **A**: Approve first request in queue
- **D**: Deny first request in queue
- **1-9**: Approve specific request by number
- **Q**: Quit

## Usage

```bash
cd vertex-game-agent
cargo run --release
```

## Example Session

```
🎮 Shard 23 played ripgrep_monster.txt | 23 → 1742 | Δ=1719 | ZK=8080
🙋 Shard 23 wants more data!
   Reason: State 1742 resonates with Monster primes!

[Human presses 'A']

✅ APPROVED: Shard 23 can consume more of ripgrep_monster.txt
```

## Fleischwolf Mode

All data is consumed byte-by-byte:
- Each byte becomes FRACTRAN denominator
- State evolves through data stream
- Score accumulates from state deltas
- ZK proof verifies entire computation

## Integration with Monster Moonshine

- **71 shards** = 71st prime (Nullstellensatz)
- **15 primes** = Supersingular operators
- **196,883 modulo** = Monster group cap
- **Resonance** = Monster group alignment

---

**🎮 Let the vertex operators play! 🔮**
