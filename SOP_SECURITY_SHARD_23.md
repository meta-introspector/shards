# SOP: Monadic Execution in Security Shard 23

## Principle

All cryptographic operations execute ONLY in security shard 23 (Paxos witness prime).

## Security Model

```
Shard 23 (Paxos) → sops-nix secrets → Monadic execution → Solana testnet
```

## Implementation

### 1. Secrets via sops-nix

```yaml
# secrets/solana-keypair.yaml (encrypted)
solana:
  keypair: ENC[...]
ipfs:
  api-key: ENC[...]
```

### 2. NixOS Module

```nix
sops.secrets."solana/keypair" = {
  mode = "0400";
  owner = "torrent-witness";
};
```

### 3. Monadic Execution

```rust
impl SolanaWitness {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // Read from sops-managed path
        let keypair_path = env::var("SOLANA_KEYPAIR_PATH")?;
        let keypair = read_keypair_file(Path::new(&keypair_path))?;
        
        // Verify security shard
        let shard: u64 = env::var("SECURITY_SHARD")?.parse()?;
        if shard != 23 {
            return Err("Must execute in shard 23".into());
        }
        
        Ok(Self { client, keypair, shard })
    }
}
```

## Enforcement

- Keypair only accessible in shard 23
- Environment variable enforces shard check
- No hardcoded secrets
- All from sops-nix managed paths

## Result

Cryptographic operations isolated to security shard with proper secret management.
