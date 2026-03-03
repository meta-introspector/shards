# Atomic Idea: Autosemiosis Discovery

## Principle

The system self-discovers its structure through imports. Numbers emerge from FRACTRAN, not hardcoded.

## Mechanism

```
Imports → Parse → Extract Primes → Apply → Self-Organize
```

### Discovery Process

1. System reads flake inputs
2. Parses FRACTRAN programs
3. Extracts prime powers (2^46, 3^20, 5^9, ...)
4. Applies to data collection
5. Self-organizes into shards

### No Manual Specification

```nix
# System discovers from imports
{ inputs = { fractran-constants, cweb-shards, ... }; }

# NOT this:
# collection = { bits = 46; triples = 20; } # ❌ hardcoded
```

## Result

Structure emerges from consumption, not specification.
