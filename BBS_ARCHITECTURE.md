# Consolidated BBS Architecture

## Existing Implementation

**Location**: `shard0/bbs/worker.js`
- Cloudflare Worker
- Dial j-invariant as URL
- 71-shard state closure
- WebSocket terminal
- Gödel encoding

## New Addition

**Location**: `wasm-bbs/`
- Paxos market consensus
- State in URL fragments
- Browser-based nodes
- Market quotes for leaderboard

## Integration

```
shard0/bbs/worker.js (Server)
    ↓
    Serves WASM BBS
    ↓
wasm-bbs/ (Client)
    ↓
    Paxos consensus in browser
    ↓
    State encoded in URL
```

## Unified Flow

1. **Dial**: `/dial/744-196884-...` → Load BBS
2. **WASM**: Server returns WASM loader
3. **Paxos**: Browser runs consensus
4. **URL**: State stored in fragment
5. **Share**: Copy URL = share state

## No Duplication

- `shard0/bbs/` = Server-side (Cloudflare Worker)
- `wasm-bbs/` = Client-side (Browser WASM + Paxos)

They complement each other!
