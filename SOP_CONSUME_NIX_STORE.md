# SOP: Consume /nix/store First

## Atomic Idea: Start with Local Nix Store

The autosemiotic system begins by consuming `/nix/store` before external sources.

## Protocol

### 1. Query Nix Store

```bash
# List all store paths
nix-store --query --requisites /run/current-system

# Generate dependency graph
nix-store --query --graph /run/current-system > store.dot

# Get all derivations
nix-store -qR --include-outputs $(nix-store -qd $(which nix))
```

### 2. Shard Store Paths

```nix
{
  outputs = { self }:
    let
      # Read /nix/store
      storePaths = builtins.readDir /nix/store;
      
      # Shard by hash mod 71
      shardPath = path: 
        let 
          hash = builtins.hashString "sha256" path;
        in hash - (hash / 71) * 71;
      
    in {
      # All store paths sharded
      shards = builtins.mapAttrs (name: _: shardPath name) storePaths;
    };
}
```

### 3. Consumption Order

1. `/nix/store` (first)
2. Local repo files
3. Vendored repos
4. External sources

## Output

Each store path → shard mod 71 → FRACTRAN input
