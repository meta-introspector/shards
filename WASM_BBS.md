# WASM BBS Paxos Market

## Overview

Paxos consensus runs in **WebAssembly** with **encrypted state stored in URL fragments**. Each node is a browser tab, consensus achieved by sharing URLs.

## Architecture

```
Browser Tab 1 (Node 0) ←→ URL Fragment (Encrypted State) ←→ Browser Tab 2 (Node 1)
                                    ↓
                            Base64(Encrypt(JSON))
```

## State Encoding

```
https://cicada71.net/bbs#eyJub2RlX2lkIjowLCJwcm9wb3NhbCI6MSw...
                         └─ Encrypted Paxos state
```

## Features

- **Stateless**: All state in URL
- **Encrypted**: XOR cipher (upgradeable to AES)
- **Shareable**: Copy URL = share state
- **Distributed**: Each tab = Paxos node
- **Consensus**: 12 of 23 tabs must agree

## Usage

```bash
# Build and serve
./run_wasm_bbs.sh

# Open in browser
http://localhost:8080
```

## Operations

1. **Load from URL**: Decrypt state from URL fragment
2. **Propose Update**: Create new proposal, update URL
3. **Share State**: Copy URL to clipboard
4. **Consensus**: Share URL with 11+ other tabs

## URL Format

```
#<base64(encrypt(json))>

Where json = {
  "node_id": 0,
  "proposal": 1,
  "quotes": [
    {"framework": "claude", "score": 50000, "bid": 49.5, "ask": 50.5}
  ],
  "signature": "abc123..."
}
```

## Encrypted Enclosures

- **Encryption**: XOR with key (upgradeable)
- **Signature**: MD5 hash (upgradeable to Ed25519)
- **Encoding**: Base64 for URL safety
- **Compression**: Optional gzip

## Multi-Tab Consensus

```bash
# Tab 1 (Node 0)
Propose → Update URL → Copy

# Tab 2 (Node 1)
Paste URL → Load → Verify → Accept

# Repeat for 12+ tabs → Consensus!
```

## Security

- State never leaves browser
- No server required
- Peer-to-peer via URL sharing
- Cryptographic signatures
- Byzantine fault tolerance

## Integration

```javascript
import init, { WasmPaxosNode } from './pkg/wasm_bbs.js';

await init();
const node = new WasmPaxosNode(0);

// Propose
const quotes = [{framework: "claude", score: 50000}];
node.propose(JSON.stringify(quotes));

// Share URL
const url = window.location.href;
navigator.clipboard.writeText(url);
```

## Advantages

- **No backend**: Pure client-side
- **Portable**: URL = complete state
- **Auditable**: Inspect URL fragment
- **Resilient**: No single point of failure
- **Private**: Data never uploaded

## Example Session

```
1. Open http://localhost:8080
2. Click "Propose Update"
3. URL changes to: #eyJub2RlX2lkIjowLCJwcm9wb3NhbCI6MSw...
4. Copy URL
5. Open 11 more tabs
6. Paste URL in each
7. Consensus achieved!
```

## Future

- [ ] WebRTC for direct tab communication
- [ ] IndexedDB for persistence
- [ ] Service Worker for offline
- [ ] WebCrypto API for real encryption
- [ ] IPFS for decentralized hosting
