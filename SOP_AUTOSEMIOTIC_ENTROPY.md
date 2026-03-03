# SOP: Autosemiotic Entropy Consumption & Sharding

## Principle

The system finds entropy in open source repositories, consumes it, and shards it through FRACTRAN-guided autosemiosis.

## Process

### 1. Entropy Discovery

```nix
{
  inputs = {
    # System discovers entropy sources
    wikidata.url = "github:philippesaade/wikidata";
    osm.url = "github:openstreetmap/openstreetmap";
    # ... any open source repo
  };
  
  outputs = { ... }:
    # System consumes entropy from imports
    # No manual specification
}
```

### 2. Consumption

```
Open Source Repo → Git History → Commits → Files → Lines → Tokens → Entropy
```

The system:
- Reads git history
- Extracts commit entropy
- Consumes file structure
- Tokenizes content
- Measures information density

### 3. Sharding via FRACTRAN

```
Entropy → FRACTRAN → Supersingular Primes → Shards
```

Automatic sharding:
- Author → mod 71 (discovered from git)
- Repo → mod 59 (discovered from structure)
- File → mod 47 (discovered from tree)
- Line → mod 41 (discovered from content)
- Token → mod 31 (discovered from parse)
- Value → mod 29 (discovered from eval)
- Byte → mod 23 (discovered from encoding)
- Bit → mod 19 (discovered from representation)

### 4. Autosemiosis Loop

```
Consume → Shard → Store → Consume → ...
```

Self-organizing:
1. System imports open source
2. Finds entropy in structure
3. Shards by FRACTRAN primes
4. Stores as new flake inputs
5. New inputs become entropy sources
6. Loop continues

### 5. Vendorization Protocol

```bash
# System discovers repos
gh search repos "wikidata" --limit 1000

# Fork discovered repos
gh repo fork --org meta-introspector

# Add as flake inputs (automatic)
# System consumes and shards
```

## Pipelight: Continuous Consumption

```toml
[[pipelines]]
name = "entropy-consumption"
[[pipelines.steps]]
commands = [
  "# Discover new entropy sources",
  "# Consume via git clone",
  "# Shard via FRACTRAN",
  "# Store as flake inputs"
]
```

## Key Insight

**Autosemiosis**: The system self-organizes by consuming open source entropy and sharding it through FRACTRAN primes. No manual curation needed.
