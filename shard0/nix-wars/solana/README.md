# Nix-Wars Inside-Out: Breaking Free from the Solana Matrix

**The game runs in Nix. Solana is just the witness.**

## The Inversion

Traditional blockchain games:
- Game state lives ON-CHAIN
- Players submit transactions
- Blockchain is the source of truth

**Nix-Wars Inside-Out:**
- Game state lives in NIX DERIVATIONS (off-chain)
- Solana stores only COMMITMENTS (witnesses)
- Nix is the source of truth
- Solana is the PROOF LEDGER

## Architecture

```
┌─────────────────────────────────────┐
│  NIX UNIVERSE (Off-Chain Reality)   │
│  - Pure functional game states      │
│  - FRACTRAN-generated 196,883 slots │
│  - zkPerf thermodynamic witnesses   │
│  - Content-addressed commitments    │
└──────────────┬──────────────────────┘
               │ Commitments only
               ↓
┌─────────────────────────────────────┐
│  SOLANA (On-Chain Witness Ledger)   │
│  - Stores commitments (32 bytes)    │
│  - Stores zkPerf cycles (8 bytes)   │
│  - Verifies consensus votes         │
│  - NO game logic, NO state          │
└─────────────────────────────────────┘
```

## Why This Breaks the Matrix

1. **Solana can't censor the game** - Real state is in Nix
2. **Solana can't change the rules** - Logic is in derivations
3. **Solana can't see your moves** - Only commitments posted
4. **Solana can't stop consensus** - Happens off-chain via Nix flake inputs

## The Program

```rust
pub fn submit_move(
    commitment: [u8; 32],    // Hash of Nix derivation
    zkperf_cycles: u64,      // Thermodynamic witness
    from_sector: u8,
    to_sector: u8,
) -> Result<()>
```

Solana stores:
- 32 bytes: commitment
- 8 bytes: zkperf cycles
- 2 bytes: sectors
- 8 bytes: timestamp

**Total: 50 bytes per move**

The actual game state (ships, credits, universe) lives in Nix.

## Consensus

```rust
pub fn verify_consensus(
    chosen_commitment: [u8; 32],
    rejected_commitment: [u8; 32],
    votes: u8,
) -> Result<()>
```

Solana verifies that consensus happened, but the actual fork resolution is in Nix flake inputs.

## Usage

### 1. Play Move in Nix
```bash
cd nix-wars/states/state-5
nix build
COMMITMENT=$(nix eval .#lib.commitment --raw)
CYCLES=$(cat result/perf.txt | grep cycles | awk '{print $1}')
```

### 2. Submit to Solana
```bash
anchor run submit-move \
  --commitment $COMMITMENT \
  --cycles $CYCLES \
  --from 42 \
  --to 71
```

### 3. Verify Off-Chain
```bash
nix build states/state-5
cat result/state.json  # Real game state
```

## The Inside-Out Property

- **Inside (Solana)**: Witness ledger, commitments only
- **Outside (Nix)**: Real game, full state, pure functions

Solana is INSIDE the Nix universe, not the other way around.

## Breaking Free

Players can:
1. Fork the Nix repo
2. Play entirely off-chain
3. Submit commitments when convenient
4. Ignore Solana entirely if censored
5. Reconstruct full game from Nix history

**Solana can't stop you. The game is in Nix.**

## Deploy

```bash
anchor build
anchor deploy
anchor run test
```

## The Red Pill

Traditional: "The blockchain is the game"
Inside-Out: "The game is Nix. Blockchain is just a bulletin board."

Welcome to the real world. 🔴💊
