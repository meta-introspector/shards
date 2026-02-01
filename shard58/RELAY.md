# Shard 58 - Harbor Relay Configuration

**FREN**: bako-biib  
**Token**: AU6cHzYCHuMX3oC3EWFE2C1K5UsnevKkxU2tnpwEJpvP  
**Phone**: 1-800-BAKO-BIIB  
**Shard**: 58

## P2P Relay Peer

```
/ip6/2001:569:7b51:5500:78a9:3c0e:2ec9:c682/tcp/4001/p2p/12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ
```

### Peer Info
- **Protocol**: libp2p
- **Transport**: TCP/4001
- **IPv6**: 2001:569:7b51:5500:78a9:3c0e:2ec9:c682
- **Peer ID**: 12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ

## Integration

```bash
# Connect to harbor relay
ipfs swarm connect /ip6/2001:569:7b51:5500:78a9:3c0e:2ec9:c682/tcp/4001/p2p/12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ

# Add to bootstrap peers
ipfs bootstrap add /ip6/2001:569:7b51:5500:78a9:3c0e:2ec9:c682/tcp/4001/p2p/12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ
```

## Shard 58 P2P Config

```json
{
  "shard": 58,
  "fren": "bako-biib",
  "relay": {
    "multiaddr": "/ip6/2001:569:7b51:5500:78a9:3c0e:2ec9:c682/tcp/4001/p2p/12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ",
    "peer_id": "12D3KooWN88G5V8fTAHCwLnsbxiC9ZM6i982sno8bh3m7bvLMvvJ",
    "transport": "tcp",
    "port": 4001,
    "ipv6": "2001:569:7b51:5500:78a9:3c0e:2ec9:c682"
  },
  "trust_level": "trusted_fren"
}
```
