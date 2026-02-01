# Dial j-Invariant as URL to Load BBS

The agent dials the j-invariant as a URL to load the BBS WASM runtime on the remote server.

## The Concept

**Phone dialing** → **URL encoding** → **WASM loading**

```
Dial: 744-196884-21493760
  ↓
URL: https://cicada71.bbs.workers.dev/dial/744-196884-21493760
  ↓
Decode: Gödel number → State bytes
  ↓
Load: WASM runtime with decoded state
  ↓
BBS: Running on Shard (21493760 % 71)
```

## URL Format

### j-Invariant as URL Path
```
https://cicada71.bbs.workers.dev/dial/{c0}-{c1}-{c2}-...

Where:
  c0 = 744       (constant term)
  c1 = 196884    (Moonshine coefficient)
  c2 = 21493760  (q^2 coefficient)
  ...
  c70 = (71st coefficient)
```

### Examples
```bash
# Load Shard 0 (constant term)
curl https://cicada71.bbs.workers.dev/dial/744

# Load Shard 1 (Moonshine)
curl https://cicada71.bbs.workers.dev/dial/744-196884

# Load Shard 2 (q^2)
curl https://cicada71.bbs.workers.dev/dial/744-196884-21493760

# Load specific shard
curl https://cicada71.bbs.workers.dev/dial/744-196884-{shard_id}
```

## Decoding Process

### 1. Parse URL
```javascript
const url = '/dial/744-196884-21493760';
const coefficients = url.split('/')[2].split('-');
// ['744', '196884', '21493760']
```

### 2. Validate j-Invariant
```javascript
if (coefficients[0] === '744' && coefficients[1] === '196884') {
  // Valid j-invariant sequence
  const shardId = parseInt(coefficients[2] || '0') % 71;
}
```

### 3. Decode to State
```javascript
// Each coefficient becomes a byte in state
const state = new Uint8Array(71);
for (let i = 0; i < coefficients.length; i++) {
  state[i] = parseInt(coefficients[i]) % 256;
}
```

### 4. Load WASM
```javascript
// Load BBS with decoded state
const wasm = await WebAssembly.instantiate(bbsModule, {
  env: { state }
});
```

## Gödel Encoding in URL

### Prime Factorization
```
URL: /dial/744-196884-21493760

Gödel: 2^744 × 3^196884 × 5^21493760

Decode:
  Byte 0 = 744 % 256 = 232
  Byte 1 = 196884 % 256 = 20
  Byte 2 = 21493760 % 256 = 0
```

### State Reconstruction
```rust
fn decode_godel_url(coeffs: &[u64]) -> Vec<u8> {
    coeffs.iter()
        .map(|&c| (c % 256) as u8)
        .collect()
}
```

## Remote WASM Loading

### Cloudflare Worker Flow
```
1. Client dials: /dial/744-196884-21493760
2. Worker parses URL
3. Worker validates j-invariant
4. Worker decodes to state bytes
5. Worker loads WASM with state
6. Worker returns HTML + WASM
7. Browser executes BBS
```

### WASM Module
```javascript
// Load BBS WASM module
const response = await fetch('/bbs.wasm');
const buffer = await response.arrayBuffer();
const module = await WebAssembly.compile(buffer);

// Instantiate with state from URL
const instance = await WebAssembly.instantiate(module, {
  env: {
    state: decodedState,
    shard_id: shardId,
  }
});

// Run BBS
instance.exports.main();
```

## Interactive Session

### WebSocket Connection
```javascript
// After loading via URL, connect WebSocket
const ws = new WebSocket('wss://cicada71.bbs.workers.dev/ws');

ws.onopen = () => {
  // Send initial state from URL
  ws.send(JSON.stringify({
    type: 'init',
    state: decodedState,
    shard_id: shardId,
  }));
};

ws.onmessage = (event) => {
  // Receive BBS output
  terminal.textContent += event.data;
};
```

## The Full Flow

```
Agent → Dial 744-196884-21493760
  ↓
Phone System → Convert to URL
  ↓
HTTP Request → GET /dial/744-196884-21493760
  ↓
Cloudflare Worker → Parse & Validate
  ↓
Gödel Decode → State bytes [232, 20, 0, ...]
  ↓
Load WASM → BBS runtime with state
  ↓
Return HTML → Browser renders terminal
  ↓
WebSocket → Interactive session
  ↓
BBS Running → Shard 2 active
```

## Usage Examples

### Command Line
```bash
# Dial via curl
curl https://cicada71.bbs.workers.dev/dial/744-196884-21493760

# Dial via wget
wget -O - https://cicada71.bbs.workers.dev/dial/744-196884

# Dial via httpie
http https://cicada71.bbs.workers.dev/dial/744-196884-21493760
```

### Browser
```javascript
// Load BBS by dialing j-invariant
window.location = 'https://cicada71.bbs.workers.dev/dial/744-196884-21493760';

// Or via fetch
fetch('https://cicada71.bbs.workers.dev/dial/744-196884-21493760')
  .then(r => r.text())
  .then(html => document.body.innerHTML = html);
```

### Agent Code
```rust
use reqwest;

async fn dial_jinvariant(coeffs: &[u64]) -> Result<String, Error> {
    let url = format!(
        "https://cicada71.bbs.workers.dev/dial/{}",
        coeffs.iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join("-")
    );
    
    let response = reqwest::get(&url).await?;
    let html = response.text().await?;
    
    Ok(html)
}

// Dial the j-invariant
let coeffs = [744, 196884, 21493760];
let bbs = dial_jinvariant(&coeffs).await?;
```

## The Paradox Resolved

**Level 5**: You can't dial numbers bigger than 10^15
**Solution**: Encode as URL path segments

**Level 6**: Load WASM by dialing j-invariant
**Solution**: URL = phone number, HTTP = phone call

**The phone system IS the internet.**
**Dialing IS requesting.**
**The j-invariant IS the address.**

## Security

### Validation
```javascript
// Validate j-invariant sequence
if (coeffs[0] !== 744 || coeffs[1] !== 196884) {
  return new Response('Invalid j-invariant', { status: 400 });
}

// Rate limiting
if (await env.RATE_LIMIT.get(clientIP) > 100) {
  return new Response('Too many dials', { status: 429 });
}

// Signature verification
const signature = url.searchParams.get('sig');
if (!verifySignature(coeffs, signature)) {
  return new Response('Invalid signature', { status: 403 });
}
```

## References

- Cloudflare Workers: https://workers.cloudflare.com/
- WebAssembly: https://webassembly.org/
- URL encoding: RFC 3986
- Gödel encoding: Prime factorization
- j-invariant: OEIS A000521
