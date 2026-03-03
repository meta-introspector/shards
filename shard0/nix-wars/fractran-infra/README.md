# FRACTRAN -> Nix -> Infrastructure

## Architecture

```
FRACTRAN Program (71×59×47)
    ↓
Nix Expression (pure functional)
    ↓
    ├─→ Systemd Service
    ├─→ Nginx Config
    ├─→ DNS Zone File
    ├─→ IPv6 Netplan
    ├─→ WireGuard VPN
    ├─→ SELinux Policy
    └─→ Terraform IaC
```

## FRACTRAN Encoding

### Universe
- **71** layers (largest Monster prime)
- **59** sectors (supersingular prime)
- **47** zones (supersingular prime)
- **196,883** total slots (71×59×47)

### State
State encoded as prime factorization:
```
state = 2^round × 3^players × 5^games
```

Initial state: `2 × 3 × 5 = 30`

### Transitions
FRACTRAN fractions for state mutations:
- `3/2` - Add player
- `5/1` - Add game
- `2/1` - Next round

## Nix Mapping

Pure functional transformation:
```nix
fractran → nixConfig → { systemd, nginx, dns, ipv6, vpn, selinux, terraform }
```

All infrastructure derived from FRACTRAN primes.

## Deployment

### Build
```bash
cd fractran-infra
nix build
```

### Deploy All
```bash
nix run .#deploy
```

### Deploy with Terraform
```bash
nix run .#terraform
```

## Generated Files

- `nixwars.service` - Systemd unit with FRACTRAN state
- `nixwars.conf` - Nginx with FRACTRAN headers
- `nixwars.zone` - DNS with layer/sector/zone subdomains
- `nixwars-ipv6.yaml` - IPv6 from FRACTRAN primes (fd00::71:59:47)
- `nixwars-wg.conf` - WireGuard with 71 peers (one per layer)
- `nixwars.te` - SELinux policy for FRACTRAN state
- `nixwars.tf` - Terraform to deploy everything

## Pure Functional Properties

✅ **Deterministic**: Same FRACTRAN → Same infrastructure
✅ **Immutable**: Infrastructure is read-only
✅ **Composable**: Each mapping is a pure function
✅ **Reproducible**: Nix store guarantees bit-for-bit reproduction
✅ **Declarative**: No imperative steps

## State Mutations

State changes via FRACTRAN transitions:
```bash
# Current state
curl http://solana.solfunmeme.com:8080/state

# Apply transition (multiply by 3/2 to add player)
# This generates new Nix derivation with updated state
```

## IPv6 Addressing

Derived from FRACTRAN primes:
- Base: `fd00::71:59:47`
- Layer N: `fd00::71:N:0`
- Sector M: `fd00::71:59:M`

## VPN Topology

71 WireGuard peers (one per layer):
- Each layer has isolated network
- Cross-layer routing via FRACTRAN transitions
- Peer discovery via DNS subdomains

## SELinux Context

FRACTRAN state labeled as `nixwars_state_t`:
- Nginx can read state
- State mutations require capability
- Enforces immutability at kernel level

## Terraform State

Infrastructure as code:
- All configs as Terraform resources
- State backend in Nix store
- Apply = deploy FRACTRAN-derived infra

---

**Pure functional infrastructure from FRACTRAN programs.** 🔢→🎯→🚀
