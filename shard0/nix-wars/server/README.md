# Nix-Wars: Immutable Server State with zkMorphisms

**Pure functional server state where each morphism creates a new immutable state**

## The Concept

Server state is **pure** and **immutable**. Every change is a **morphism** that produces a new state.

```
State₀ --[morphism₁]--> State₁ --[morphism₂]--> State₂ --[morphism₃]--> State₃
```

## Genesis State

```json
{
  "round": 0,
  "timestamp": "2026-02-15T07:38:36Z",
  "deployment": {
    "url": "http://solana.solfunmeme.com:8080",
    "commitment": "515c7a960f5260c8"
  },
  "players": {}
}
```

**Commitment**: `0887df56727c6b80...`

## Morphisms

### 1. Player Connect
```nix
playerConnect = prevState: player: 
  prevState // {
    round = prevState.round + 1;
    players = prevState.players // {
      ${player} = {
        connected_at = prevState.round + 1;
        sector = 0;
        credits = 1000000;
      };
    };
  };
```

### 2. Player Move
```nix
playerMove = prevState: player: toSector:
  prevState // {
    round = prevState.round + 1;
    players = prevState.players // {
      ${player} = prevState.players.${player} // {
        sector = toSector;
      };
    };
  };
```

## State Transitions

### Round 0 → 1: Alice Connects
```
State₀ --[playerConnect "alice"]--> State₁
```

**Commitment**: `2690c719f8903ba0...`

### Round 1 → 2: Bob Connects
```
State₁ --[playerConnect "bob"]--> State₂
```

**Commitment**: `63f392e3ec7a682e...`

### Round 2 → 3: Alice Moves to Sector 42
```
State₂ --[playerMove "alice" 42]--> State₃
```

**Commitment**: `7a8ab1033862240e...`

## Current State (Round 3)

```json
{
  "round": 3,
  "players": {
    "alice": {
      "connected_at": 1,
      "sector": 42,
      "credits": 1000000
    },
    "bob": {
      "connected_at": 2,
      "sector": 0,
      "credits": 1000000
    }
  }
}
```

## State History (Immutable Chain)

```json
{
  "history": [
    {"round": 0, "commitment": "0887df56727c6b80..."},
    {"round": 1, "commitment": "2690c719f8903ba0..."},
    {"round": 2, "commitment": "63f392e3ec7a682e..."},
    {"round": 3, "commitment": "7a8ab1033862240e..."}
  ]
}
```

## Properties

### ✅ Pure
Every morphism is a pure function:
```
f(state, args) → newState
```

### ✅ Immutable
States are never modified, only new states created:
```
state₀ remains unchanged
state₁ is a new value
```

### ✅ Reproducible
Same morphisms → same states:
```
playerConnect(genesis, "alice") 
  always produces same state₁
```

### ✅ Verifiable
Every state has a commitment hash:
```
commitment = SHA256(JSON(state))
```

### ✅ Auditable
Full history is preserved:
```
[state₀, state₁, state₂, state₃, ...]
```

## Usage

### Build State
```bash
cd server
nix build
cat result | jq .
```

### Query State
```bash
# Current state
nix eval .#lib.state3 --json | jq .

# Genesis
nix eval .#lib.genesis --json | jq .

# History
nix eval .#lib.stateHistory --json | jq .
```

### Apply Morphism
```nix
# In Nix
newState = playerMove currentState "alice" 71;
commitment = stateCommitment newState;
```

## Integration with Server

### HTTP API (Conceptual)
```
GET  /state          → current state
GET  /state/history  → full history
POST /morphism       → apply morphism, return new state
```

### Morphism Request
```json
{
  "type": "player_move",
  "player": "alice",
  "to_sector": 71
}
```

### Response
```json
{
  "previous_commitment": "7a8ab1033862240e...",
  "new_commitment": "abc123...",
  "new_state": { ... }
}
```

## zkState Proof

```json
{
  "genesis_commitment": "0887df56727c6b80...",
  "current_commitment": "7a8ab1033862240e...",
  "transitions": 3,
  "pure": true,
  "immutable": true,
  "reproducible": true
}
```

## The Win

**Server state is a Nix derivation.**

This means:
- ✅ State is pure functional
- ✅ Transitions are morphisms
- ✅ History is immutable
- ✅ Everything is verifiable
- ✅ Fully reproducible

**The server is now a pure function.** 🔐✨
