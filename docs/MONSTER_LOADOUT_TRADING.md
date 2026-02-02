# Monster Ship Loadout Trading System

## Overview

A zero-knowledge proof system for trading Monster Group ship loadouts with selective disclosure across 4 privacy levels.

## Architecture

### Monster Primes (15 total)
- **Sources**: 2, 3, 5, 7 (high out-degree)
- **Hubs**: 11, 13 (centrality = 1.0)
- **Life Bearers (BDI)**: 3, 13, 23 (mod 10 = 3)
- **Rooster**: 71 (ultimate attractor)
- **Sinks**: 29, 31, 41, 47, 59 (high in-degree)
- **Connectors**: 17, 19 (balanced)

### Ship Loadout Structure
```typescript
type Loadout = {
  primes: Set<Prime>,        // 0-15 primes
  tunnels: [Prime, Prime][],  // Connections
  sidechannels: [Prime, Prime, Depth][]  // Nested tunnels
}
```

### ZK Proof Properties
```typescript
type ZKProof = {
  commitment: SHA256Hash,     // Binds to exact loadout
  conformant: Boolean,        // Monster conformance
  properties: {
    hasBDI: Boolean,          // Has life-bearing prime
    hasRooster: Boolean,      // Has prime 71
    primeCount: Nat,          // 0-15
    flowRate: Nat,            // Sum of prime flows
    tunnelCount: Nat          // Number of tunnels
  }
}
```

### Disclosure Levels

#### 1. Minimal (Public Safe)
**Reveals**: Stats only  
**Hides**: All primes, tunnels  
**Use**: Public leaderboards, flexing

```json
{
  "type": "minimal",
  "primeCount": 3,
  "hasBDI": true,
  "hasRooster": true
}
```

#### 2. Partial (Semi-Private)
**Reveals**: 50% of primes, total flow  
**Hides**: 50% of primes, tunnels  
**Use**: Guild recruitment, build discussions

```json
{
  "type": "partial",
  "revealedPrimes": [2, 13],
  "hiddenCount": 1,
  "totalFlow": 37
}
```

#### 3. Tunnels (Structure Only)
**Reveals**: Tunnel count, strengths  
**Hides**: Tunnel endpoints, primes  
**Use**: Alliance strategy, meta discussions

```json
{
  "type": "tunnels",
  "tunnelCount": 2,
  "sidechannelCount": 3,
  "tunnelStrengths": [29, 23]
}
```

#### 4. Full (Trusted Only)
**Reveals**: Complete loadout  
**Hides**: Nothing  
**Use**: Direct trades with trusted players

```json
{
  "type": "full",
  "primes": [2, 13, 71],
  "tunnels": [[2, 13], [13, 71]],
  "sidechannels": []
}
```

## Formal Properties

### Monster Conformance
A loadout is **Monster conformant** if:
1. `hasBDI = true` (at least one life-bearing prime)
2. `flowRate >= 10` (minimum 10M decls/s)
3. `primeCount >= 1` (at least one prime)

### ZK Proof Correctness
For any loadout `L` and proof `P = zkProof(L)`:
1. **Binding**: `P.commitment = SHA256(sort(L.primes))`
2. **Soundness**: `P.conformant = true ⟹ isConformant(L)`
3. **Zero-Knowledge**: `P` reveals no information about exact prime selection beyond public properties

### Selective Disclosure Invariants
For disclosure level `d` and loadout `L`:
1. **Minimal**: `|revealed(d)| = 0`
2. **Partial**: `|revealed(d)| = ⌊|L.primes| / 2⌋`
3. **Tunnels**: `revealed(d) ∩ L.primes = ∅`
4. **Full**: `revealed(d) = L`

## Implementation

### Storage Options
1. **ZK-RDF URL**: `#<base64(loadout + zkProof)>`
2. **localStorage**: Auto-save/load
3. **Private Gist**: Cloud backup with GitHub API

### Trading Protocol
1. **Create**: Press `X` → Select level (1-4)
2. **Share**: Copy URL `?trade=<base64>`
3. **Receive**: Auto-load on page open
4. **Accept**: Full disclosure only, saves to localStorage

### Security Properties
- **Commitment**: SHA-256 binds proof to exact loadout
- **Non-repudiation**: Timestamp + commitment prevents tampering
- **Selective disclosure**: Each level reveals only specified data
- **Privacy**: Minimal/Partial/Tunnels hide sensitive strategy

## Verification

### Lean 4 Proof
See `MonsterLoadoutTrading.lean`

### MiniZinc Model
See `monster_loadout_trading.mzn`

### Nix Build
```bash
nix build .#monster-loadout-proofs
```

## References
- Monster Group: 71-fold symmetry
- 10-fold way: Topological classification
- BDI primes: 3, 13, 23, 43, 53, 63 (mod 10 = 3)
- Rooster prime: 71 (ultimate attractor)
- Flow rates: From 66.8M Lean constant analysis
