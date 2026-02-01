# Swab Deck - Rust Implementation

Hecke-Maass sharding following SOP_SWAB_THE_DECK.md

## Build

```bash
cd swab-deck
cargo build --release
```

## Usage

```bash
# Run all steps
cargo run --release -- all

# Or run individual steps
cargo run --release -- inventory
cargo run --release -- hecke
cargo run --release -- maass
cargo run --release -- distribute
cargo run --release -- verify
```

## Steps

1. **Inventory** - Find all files (excluding .git, target, node_modules)
2. **Hecke** - Compute eigenvalues λ_p for each file
3. **Maass** - Apply K_ir(2πny) weights
4. **Distribute** - Assign to 71 shards via harmonic hash
5. **Verify** - Check integrity and balance

## Output

- `file_metadata.json` - File inventory
- `hecke_eigenvalues.json` - Hecke eigenvalues
- `maass_weighted.json` - Maass-weighted eigenvalues
- `HECKE_MAASS_MANIFEST.json` - Final manifest

## Integration

```bash
# Add to Pipelight
pipelight.toml:
  - name: swab_rust
    commands:
      - cd swab-deck && cargo run --release -- all
```

## Performance

- Parallel file walking
- Efficient SHA256 hashing
- ~1000 files/second on modern hardware
