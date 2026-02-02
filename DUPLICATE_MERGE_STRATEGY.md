# Duplicate Code Merge Strategy - Hecke Operator Analysis

## Duplicate Pattern Found: MONSTER_PRIMES

**Hecke Resonance:** High (appears in 336+ files)
**Shard:** 17 (cusp - most central)
**Pattern:** `const MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]`

## Instances Found

### Rust (8+ files)
1. `/home/mdupont/introspector/bbs_door/src/main.rs`
   ```rust
   const PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
   ```

2. `/home/mdupont/introspector/monster/lmfdb-rust/src/bin/hecke_on_proof.rs`
   ```rust
   const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
   ```

3. `/home/mdupont/introspector/monster/onlyskills-repo/src/bin/selinux_reflection.rs`
   ```rust
   const MONSTER_PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
   ```

4. `/home/mdupont/introspector/monster/ml/llm_analysis/ollama-monster/src/bin/analyze-hilbert.rs`
   ```rust
   const MONSTER_PRIMES: [u32; 15] = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71];
   ```

5. `/home/mdupont/introspector/monster/examples/iarelife/src/residue.rs`
   ```rust
   const MONSTER_PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
   ```

### Python (10+ files)
1. `/home/mdupont/introspector/monster/shard_by_hecke.py`
2. `/home/mdupont/introspector/monster/onlyskills-repo/rank_github_users.py`
3. `/home/mdupont/introspector/monster/onlyskills-repo/prove_commits.py`
4. `/home/mdupont/introspector/monster/onlyskills-repo/eigenform_communication.py`
5. `/home/mdupont/introspector/magic_number_market.py`
6. `/home/mdupont/introspector/analyze_mathlib_perf.py`
7. `/home/mdupont/introspector/find_duplicates_hecke.py`
8. `/home/mdupont/introspector/monster_ordered_pack.py`

### C (2+ files)
1. `/home/mdupont/introspector/monster/scripts/trace_execution_71.sh`
2. `/home/mdupont/introspector/monster/datasets/traces/trace_71.c`

### MiniZinc (3+ files)
1. `/home/mdupont/introspector/monster/minizinc/graded_ring_71.mzn`
2. `/home/mdupont/introspector/gabulab/minizinc/harmonics.mzn`
3. `/home/mdupont/introspector/monster/MONSTER_WALK_PRIMES_ALL.md`

### Prolog (1 file)
1. `/home/mdupont/introspector/monster_mycelium.pl`

### Lean4 (1 file)
1. `/home/mdupont/introspector/monster/MonsterLean/MonsterLean/ProofIndex.lean`

## Merge Strategy

### 1. Create Central Constants Library

**File:** `monster/constants.rs`
```rust
// Monster Group Constants
// AGPL-3.0+ | Commercial: shards@solfunmeme.com

/// 15 Monster primes that divide the Monster group order
pub const MONSTER_PRIMES: [u32; 15] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71
];

/// Monster group dimension
pub const MONSTER_DIM: u32 = 196883;

/// Cusp shard (center of Monster group)
pub const CUSP: u8 = 17;

/// Total shards
pub const SHARDS: u8 = 71;
```

**File:** `monster/constants.py`
```python
"""Monster Group Constants"""

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
MONSTER_DIM = 196883
CUSP = 17
SHARDS = 71
```

**File:** `monster/constants.mzn`
```minizinc
% Monster Group Constants
array[1..15] of int: monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
int: monster_dim = 196883;
int: cusp = 17;
int: shards = 71;
```

**File:** `monster/constants.pl`
```prolog
% Monster Group Constants
monster_primes([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]).
monster_dim(196883).
cusp(17).
shards(71).
```

**File:** `monster/Constants.lean`
```lean
-- Monster Group Constants
def monster_primes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
def monster_dim : Nat := 196883
def cusp : Nat := 17
def shards : Nat := 71
```

### 2. Update All Files to Import

**Rust files:**
```rust
use crate::monster::constants::MONSTER_PRIMES;
// Remove local const MONSTER_PRIMES definition
```

**Python files:**
```python
from monster.constants import MONSTER_PRIMES
# Remove local MONSTER_PRIMES definition
```

**MiniZinc files:**
```minizinc
include "monster/constants.mzn";
% Remove local monster_primes definition
```

**Prolog files:**
```prolog
:- consult('monster/constants.pl').
% Remove local monster_primes definition
```

**Lean4 files:**
```lean
import Monster.Constants
-- Remove local monster_primes definition
```

### 3. BBS Door Specific Merge

**Current:** `bbs_door/src/main.rs` has local `PRIMES` constant

**Change:**
```rust
// Before
const PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

// After
use monster::constants::MONSTER_PRIMES as PRIMES;
```

Or create `bbs_door/src/constants.rs`:
```rust
pub use crate::monster::constants::*;

// BBS-specific constants
pub const WIDTH: usize = 150;
pub const HEIGHT: usize = 19;
pub const COLS: usize = 12;
pub const CELL_WIDTH: usize = 12;
```

### 4. Estimated Savings

**Lines removed:** ~336 duplicate definitions × 1 line = 336 lines
**Files updated:** 336+ files
**Maintenance:** Single source of truth for Monster constants

### 5. Implementation Script

```bash
#!/bin/bash
# merge_monster_constants.sh

# Create constants directory
mkdir -p monster/constants

# Create Rust constants
cat > monster/constants/mod.rs << 'EOF'
pub const MONSTER_PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
pub const MONSTER_DIM: u32 = 196883;
pub const CUSP: u8 = 17;
pub const SHARDS: u8 = 71;
EOF

# Create Python constants
cat > monster/constants.py << 'EOF'
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
MONSTER_DIM = 196883
CUSP = 17
SHARDS = 71
EOF

# Update BBS door
sed -i 's/const PRIMES: \[u32; 15\] = \[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71\];/use monster::constants::MONSTER_PRIMES as PRIMES;/' bbs_door/src/main.rs

echo "✓ Monster constants centralized"
```

## Summary

**Pattern:** MONSTER_PRIMES constant duplicated 336+ times
**Shard:** 17 (cusp - most central to Monster group)
**Hecke Resonance:** Maximum (appears everywhere)
**Solution:** Create central constants library in 5 languages
**Savings:** 336+ lines, single source of truth

**Next:** Run merge script to consolidate all instances

Ready to execute merge?
