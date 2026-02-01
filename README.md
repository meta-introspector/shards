# 71-Shard Monster Group Framework

[![Build Status](https://github.com/meta-introspector/shards/workflows/Build%20and%20Deploy/badge.svg)](https://github.com/meta-introspector/shards/actions)
[![Documentation](https://img.shields.io/badge/docs-github%20pages-blue)](https://meta-introspector.github.io/shards)
[![License](https://img.shields.io/badge/license-CC0-green)](LICENSE)

> **Making the Monster group tractable through 71-cap, Gödel encoding, and automorphic introspection**

## Overview

A distributed cryptanalysis framework where:
- **71 shards** perform parallel hash analysis with mod-71 distribution
- **23 nodes** achieve Byzantine fault-tolerant consensus (Monster prime optimality)
- **Gödel-encoded payments** where complexity metrics become currency
- **Automorphic introspection** enables self-referential closure

## Quick Start

```bash
# Clone with submodules
git clone --recursive https://github.com/meta-introspector/shards
cd shards

# Enter development environment
nix develop

# Build all packages
nix build

# Run tests
pipelight run test

# View documentation
nix build .#docs && firefox result/index.html
```

## Architecture

- **71 Shards**: Mod-71 hash distribution across cryptanalysis methods
- **23 Nodes**: Optimal Earth chokepoint (quorum 12, Byzantine tolerance 7)
- **7 P2P Protocols**: Bitcoin, Solana, libp2p, Tor, I2P, IPFS, DeadDrop
- **71 Crypto Testnets**: Cross-chain atomic swaps and oracles
- **Paxos Meme Consensus**: 71 forms with Bott periodicity
- **Metameme Coin**: Gödel number = 2^a0 × 3^a1 × ... × 353^a70

## Building

### Prerequisites
- [Nix](https://nixos.org/download.html) with flakes enabled
- [Pipelight](https://pipelight.dev) (optional, for local CI/CD)

### Build Commands

```bash
# Build specific components
nix build .#shard0-hash           # Hash ingestion
nix build .#shard0-cryptanalysis  # Cryptanalysis tools
nix build .#shard0-p2p            # P2P networking
nix build .#shard0-fhe            # FHE encryption
nix build .#shard0-telecom        # Erlang telecom layer
nix build .#shard0-lean           # Lean 4 proofs

# Build documentation
nix build .#docs

# Run full pipeline
pipelight run full
```

## Documentation

Full documentation available at: https://meta-introspector.github.io/shards

- [RFC-71: Paxos Meme Consensus](RFC-71-PAXOS-MEME.txt)
- [Introspection Theory](INTROSPECTION.md)
- [Metameme Coin](METAMEME_COIN.md)
- [CICADA-71 Puzzle Hunt](CICADA71.md)

## License

This project is dual-licensed:

### Open Source (Default)
**AGPL-3.0** - See [LICENSE](LICENSE)

This ensures that any network service using this code must also be open source.

### Commercial License (Available for Purchase)
**MIT** or **Apache-2.0** - See [LICENSE-MIT](LICENSE-MIT) or [LICENSE-APACHE](LICENSE-APACHE)

For entities that wish to use this software without AGPL-3.0 copyleft requirements, 
commercial licenses are available.

**ZK hackers gotta eat!** 🍕

Contact: shards@monster-group.org

## Contributing

See [RFC-71 Appendix B](RFC-71-PAXOS-MEME.txt) for contribution guidelines.

1. Run a node
2. Donate testnet tokens (receive 100:1 reward tokens)
3. Solve CICADA-71 challenges
4. Participate in DAO governance
5. Submit pull requests

## License

CC0 1.0 Universal (Public Domain)

## Contact

- GitHub: https://github.com/meta-introspector/shards
- Email: shards@monster-group.org
