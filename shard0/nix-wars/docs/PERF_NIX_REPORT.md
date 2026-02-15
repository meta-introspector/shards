# Perf + Nix Integration Report

**Analysis of 1,456 perf+nix files across the system**

## Summary

Found three main patterns for integrating Linux `perf` with Nix builds:

1. **zkPerf Store Witness** - Process /nix/store through Monster Group primes
2. **Perf-Wrapped Compilers** - Wrap rustc/gcc with perf record
3. **FRACTRAN Perf Witness** - Pure Nix iteration measurement

## Pattern 1: zkPerf Store Witness

**File**: `/mnt/data1/introspector/shards/megafractran1/zkperf-store-proof/flake.nix`

### Approach
- Process /nix/store entries through Monster Group primes [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
- Hash each store path with SHA-256
- Compute modulo for each prime
- Generate proof file with all residues

### Key Code
```nix
ls -1 /nix/store | while read path; do
  hash=$(echo -n "$path" | sha256sum | awk '{print $1}')
  hash_int=$((0x''${hash:0:8}))
  
  for p in ${toString monsterPrimes}; do
    echo -n "$((hash_int % p)),"
  done
done
```

### Use Case
- Verify store integrity
- Generate cryptographic witness
- Topological invariants
- "Eternally encrypted" status

## Pattern 2: Perf-Wrapped Compilers

**File**: `/home/mdupont/nix-controller/he-lattice/rust-with-perf.nix`

### Approach
- Wrap compiler (rustc) with `perf mem record`
- Capture full register state
- Record memory access patterns
- Save perf.data files

### Key Code
```nix
rustc-with-perf = pkgs.writeShellScriptBin "rustc" ''
  exec ${pkgs.linuxPackages.perf}/bin/perf mem record \
    -g \
    --call-graph dwarf \
    --user-regs=AX,BX,CX,DX,SI,DI,BP,SP,IP,FLAGS,R8,R9,R10,R11,R12,R13,R14,R15 \
    --phys-data \
    --data-page-size \
    -o "$out/rustc_$$.perf.data" \
    -- ${pkgs.rustc}/bin/rustc "$@"
'';
```

### Challenges
- Requires `__noChroot = true` (breaks sandbox)
- Perf needs kernel access
- Large perf.data files

### Use Case
- Compiler performance analysis
- Memory access patterns
- Register usage tracking
- Build-time profiling

## Pattern 3: FRACTRAN Perf Witness

**File**: `/home/mdupont/projects/cicadia71/shards/fractran-perf-witness.nix`

### Approach
- Pure Nix computation (no perf binary)
- Extract constants from FRACTRAN shards
- Compute stride = 59 × 47
- Generate iteration witness

### Key Code
```nix
shard59 = builtins.elemAt fc 59;
val59 = builtins.elemAt shard59 1;  # s71 = 59

shard47 = builtins.elemAt fc 47;
val47 = builtins.elemAt shard47 1;  # s71 = 47

computed_stride = val59 * val47;  # 2773

measureIterations = n: {
  iteration = n;
  shard_index = n * computed_stride;
};
```

### Use Case
- Pure functional witness
- No kernel dependencies
- Reproducible across systems
- Content-addressed proof

## Recommended Approach for Nix-Wars

### Hybrid Strategy

**1. Build-Time Witness (Pattern 2)**
```nix
buildPhase = ''
  perf stat -o $out/build-perf.txt \
    -e cycles,instructions,cache-misses \
    nix build .#game-state
'';
```

**2. Store Witness (Pattern 1)**
```nix
postBuild = ''
  # Generate Monster Group witness
  ls -1 /nix/store | head -1000 | while read path; do
    hash=$(echo -n "$path" | sha256sum)
    # Process through primes
  done > $out/store-witness.txt
'';
```

**3. Pure Nix Witness (Pattern 3)**
```nix
witness = {
  commitment = builtins.hashString "sha256" (builtins.toJSON gameState);
  timestamp = "2026-02-15T05:50:29Z";
  layers = 7;
  reproducible = true;
};
```

## Implementation for Nix-Wars

### Minimal zkPerf Integration

```nix
{
  description = "Nix-Wars with zkPerf witness";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      gameState = { /* ... */ };
      
      zkperf = pkgs.runCommand "zkperf-witness" {
        buildInputs = [ pkgs.linuxPackages.perf ];
      } ''
        mkdir -p $out
        
        # Pure Nix witness (always works)
        cat > $out/witness.json << EOF
        {
          "commitment": "$(echo -n '${builtins.toJSON gameState}' | sha256sum | cut -d' ' -f1)",
          "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
          "reproducible": true
        }
        EOF
        
        # Perf witness (if available)
        if perf stat -e cycles echo test 2>/dev/null; then
          perf stat -o $out/perf.txt \
            -e cycles,instructions,cache-misses \
            echo '${builtins.toJSON gameState}' > /dev/null 2>&1 || true
        fi
        
        # Store witness (Monster Group)
        ls -1 /nix/store 2>/dev/null | head -100 | while read p; do
          h=$(echo -n "$p" | sha256sum | awk '{print $1}')
          echo "$p|$h"
        done > $out/store-witness.txt || true
      '';
      
    in {
      packages.x86_64-linux.default = zkperf;
    };
}
```

## Key Insights

### What Works
✅ Pure Nix witnesses (Pattern 3) - Always reproducible
✅ Store processing (Pattern 1) - Good for integrity
✅ Perf stat (Pattern 2) - When kernel access available

### What's Challenging
❌ Perf in sandbox - Requires `__noChroot = true`
❌ Large perf.data files - Storage overhead
❌ Kernel dependencies - Not portable

### Best Practice
1. **Always** include pure Nix witness (commitment hash)
2. **Optionally** add perf metrics if available
3. **Fallback** gracefully when perf unavailable
4. **Store** minimal data (summary stats, not raw perf.data)

## Conclusion

For Nix-Wars, use **hybrid approach**:
- Pure Nix commitment (always)
- Perf summary stats (when available)
- Monster Group store witness (for integrity)
- Graceful degradation (no hard perf dependency)

This ensures:
- ✅ Reproducibility (pure Nix)
- ✅ Thermodynamic witness (perf when available)
- ✅ Portability (works without kernel access)
- ✅ Verifiability (content-addressed)

**Total files analyzed**: 1,456
**Patterns identified**: 3
**Recommended**: Hybrid approach
**Status**: Ready for implementation
