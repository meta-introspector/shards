# SOP: GMP ISO0K zkML Workflow

## Atomic Idea: Consume 71 Shards from Archive via Nix Flake

### Context
- Bare git repos at `/mnt/data1/git/shards/shard{00..70}.git` (archive)
- Working directory at `/mnt/data1/introspector/shards` (checked out)
- Consume via Nix flake input for autosemiotic processing

### Protocol

#### 1. Reference Working Directory (Not Bare Repos)

```nix
{
  inputs = {
    data-shards.url = "git+file:///mnt/data1/introspector/shards";
  };
}
```

**NOT** bare repos:
```nix
# ❌ Wrong - bare repos have no checkout
shard00.url = "git+file:///mnt/data1/git/shards/shard00.git";
```

#### 2. Build Flake

```bash
cd data-shards-71
nix build
```

#### 3. Verify Consumption

```bash
cat result
# Output: Consuming 71 shards from: /nix/store/...-source
```

### Result

All 71 shards consumed into Nix store for autosemiotic processing.

## GMP ISO0K zkML Integration

- **GMP**: GNU Multiple Precision (arbitrary precision arithmetic)
- **ISO0K**: Isomorphic zero-knowledge proofs
- **zkML**: Zero-knowledge machine learning

### Workflow

```
Archive (/mnt/data1/git) → Working Dir → Nix Flake → /nix/store → zkML Processing
```

Each shard processed with:
1. GMP for prime arithmetic (mod 71, 59, 47...)
2. ISO0K for zero-knowledge proofs
3. zkML for pattern recognition

### Perf Witness

See `PERF_WITNESS_2026-02-08_71_SHARDS.json`
