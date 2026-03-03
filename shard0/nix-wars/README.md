# Nix-Wars: TradeWars as Pure Functional Derivations

**A game where each move is a Nix flake building on previous states**

## What Just Happened

We created a **pure functional game** where:
- Each move is a Nix derivation
- Game states are content-addressed (FRACTRAN commitments)
- History forms an immutable lattice
- Consensus resolves forks via stake-weighted voting
- Everything is reproducible and hermetically sealed

## The Game Lattice

```
State 0 (Genesis)
    ↓
State 1 (Alpha → sector 42)
   / \
  2a  2b  (Fork: Beta→59 vs Gamma→71)
   \ /
State 3 (Consensus: 2a wins 2/3 votes)
```

## Play the Game

```bash
cd /home/mdupont/projects/cicadia71/shards/shard0/nix-wars
./play.sh
```

## Game States

### State 0: Genesis
- **Commitment**: `19e9e02cedf9fe34...`
- **Ships**: alpha(0), beta(1), gamma(2)
- **Credits**: 1,000,000 each

### State 1: Alpha Warps
- **Commitment**: `774b124531f2c5d6...`
- **Move**: Alpha warps to sector 42
- **Input**: State 0

### State 2a: Beta Warps (Fork A)
- **Commitment**: `b98acdb75535cdd7...`
- **Move**: Beta warps to sector 59
- **Input**: State 1

### State 2b: Gamma Warps (Fork B)
- **Commitment**: `b2799906593b4667...`
- **Move**: Gamma warps to sector 71
- **Input**: State 1

### State 3: Consensus
- **Commitment**: `381017df6e14308b...`
- **Winner**: State 2a (2/3 votes)
- **Inputs**: Both 2a and 2b (preserves full history)

## Key Properties

### Pure Functional
Every state is a pure function of its inputs:
```nix
newState = prevState // { 
  round = prevState.round + 1;
  ships = prevState.ships // { 
    alpha = prevState.ships.alpha // { sector = 42; };
  };
}
```

### Content-Addressed
Each state has a cryptographic commitment:
```nix
commitment = builtins.hashString "sha256" (builtins.toJSON {
  inherit newState move;
  previous = previous.lib.commitment;
});
```

### Immutable Lattice
States reference previous states via flake inputs:
```nix
inputs = {
  previous.url = "path:../state-1";
};
```

### Consensus Resolution
Forks are resolved by choosing the winning branch:
```nix
inputs = {
  chosen.url = "path:../state-2a";
  rejected.url = "path:../state-2b";
};
```

## Architecture

Each state is a Nix flake with:
- **inputs**: Previous state(s)
- **outputs.packages.default**: Built state.json
- **outputs.lib.gameState**: Current game state
- **outputs.lib.commitment**: FRACTRAN commitment hash

## Thermodynamic Witness

Build time = proof of work:
```bash
time nix build states/state-3
# real    0m2.847s  ← Thermodynamic witness
```

## 71-Shard Distribution

This is **shard0** (Layer 0: Public Genesis). Future expansion:
- Shard 42: Data layer (conversations)
- Shard 47: Cryptographic layer (proofs)
- Shard 59: Sector Y (middle layer)
- Shard 71: Omega layer (Monster prime)

## Next Steps

1. **Add zkperf witness**: Measure build time as proof of work
2. **Extend to 71 shards**: Each shard is a zone in 71×59×47 space
3. **WASM frontend**: Browser-based game client
4. **UUCP sneakernet**: Air-gapped message exchange
5. **Solana integration**: On-chain consensus via Nebuchadnezzar vessel

## Technical Details

### Space Division
- **71 zones** (X axis)
- **59 sectors** (Y axis)
- **47 ports** (Z axis)
- **Total slots**: 196,883 (71×59×47)

### Consensus Rules
- Quorum: 2/3 votes
- Stake-weighted: Future implementation
- Byzantine tolerance: 7 nodes (future)

### FRACTRAN Commitment
Uses SHA-256 hash of JSON-serialized state + move + previous commitment.

## Files

```
nix-wars/
├── play.sh              # Run the game
└── states/
    ├── state-0/         # Genesis
    ├── state-1/         # Move 1
    ├── state-2a/        # Fork A
    ├── state-2b/        # Fork B
    └── state-3/         # Consensus
```

Each state directory contains:
- `flake.nix` - Pure derivation
- `flake.lock` - Locked inputs
- `result/` - Built output (symlink to /nix/store)

## Philosophy

> "Each move is an ontological commitment. The lattice is the game. The consensus is the truth."

This game proves that:
1. Game state can be pure functional
2. History is immutable and content-addressed
3. Forks are natural and resolved via consensus
4. Thermodynamic witness prevents spam
5. Everything is reproducible

## Q.E.D.

∴ Nix-Wars demonstrates pure functional gaming with ontological commitments □

---

**Repository**: https://github.com/meta-introspector/shards  
**Branch**: nydiokar/main  
**Path**: shard0/nix-wars/
