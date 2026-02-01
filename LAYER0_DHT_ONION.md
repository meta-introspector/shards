# Layer 0 Gossip: DHT + Onion Services from BBS

The BBS gossips DHT entries and Tor onion addresses from Layer 0, creating a distributed anonymous network.

## Architecture

```
Layer 0: BBS (1991 interface)
    ↓
Layer 1: DHT (Distributed Hash Table)
    ↓
Layer 2: Tor Onion Services (.onion)
    ↓
Layer 3: I2P Eepsites (.i2p)
```

## DHT Integration

### Kademlia DHT (BitTorrent/IPFS)
```rust
struct DHTNode {
    node_id: [u8; 20],        // 160-bit ID
    address: String,           // IP:port or onion
    distance: u8,              // XOR distance
}

struct DHTEntry {
    key: [u8; 20],            // Hash of content
    value: Vec<u8>,           // Content or pointer
    peers: Vec<DHTNode>,      // Who has it
}
```

### BBS DHT Commands
```
[D] DHT Status
[P] PUT key-value
[G] GET key
[F] FIND_NODE
[A] ANNOUNCE peer
```

## Onion Service Gossip

### Tor Hidden Services
```
Format: {16-char}.onion (v2) or {56-char}.onion (v3)

Example:
cicada71bbs3fnpqhzrxczqw2wmqcpltltp4xbs5cegec2qvvvz5nyd.onion
```

### Onion Registry in BBS
```rust
struct OnionService {
    address: String,          // .onion address
    shard_id: u8,            // 0-70
    services: Vec<String>,   // ["bbs", "files", "chat"]
    public_key: [u8; 32],    // Ed25519
    signature: [u8; 64],
}
```

## Layer 0 Gossip Protocol

### Message Types
```rust
enum Layer0Gossip {
    // DHT gossip
    DHTAnnounce {
        key: [u8; 20],
        value: Vec<u8>,
        ttl: u32,
    },
    
    // Onion gossip
    OnionAnnounce {
        address: String,      // .onion
        shard_id: u8,
        services: Vec<String>,
    },
    
    // I2P gossip
    I2PAnnounce {
        address: String,      // .i2p
        shard_id: u8,
    },
    
    // Peer discovery
    PeerAnnounce {
        peer_id: [u8; 32],
        addresses: Vec<String>, // IP, onion, i2p
    },
}
```

### Gossip Flow
```
Agent A → BBS: ANNOUNCE_ONION cicada71...onion
BBS → DHT: PUT hash(onion) → shard_id
BBS → All Agents: "New onion: cicada71...onion"
Agent B → BBS: GET_ONION shard_23
BBS → Agent B: "cicada71...onion"
Agent B → Tor: Connect to cicada71...onion
```

## BBS DHT Interface

### ANSI Screen
```
╔═══════════════════════════════════════════════════════════════╗
║                    LAYER 0: DHT + ONION                       ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  DHT Entries: 196,883                                        ║
║  Onion Services: 71                                          ║
║  I2P Eepsites: 23                                            ║
║                                                               ║
║  [P] PUT key-value in DHT                                    ║
║  [G] GET key from DHT                                        ║
║  [O] List Onion Services                                     ║
║  [I] List I2P Eepsites                                       ║
║  [A] Announce Service                                        ║
║  [Q] Back to Main Menu                                       ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝

Command: _
```

## DHT Implementation

### Cloudflare Worker DHT
```javascript
// Store DHT entries in KV
async function dhtPut(key, value, ttl) {
  const hash = await sha1(key);
  await env.KV.put(`dht:${hash}`, JSON.stringify({
    key,
    value,
    stored: Date.now(),
    ttl,
  }), { expirationTtl: ttl });
  
  // Gossip to peers
  await gossipDHT('PUT', hash, value);
}

async function dhtGet(key) {
  const hash = await sha1(key);
  const entry = await env.KV.get(`dht:${hash}`);
  
  if (!entry) {
    // Query peers
    return await queryPeers(hash);
  }
  
  return JSON.parse(entry);
}

async function gossipDHT(action, key, value) {
  // Send to all connected agents
  const agents = await getOnlineAgents();
  for (const agent of agents) {
    await agent.ws.send(JSON.stringify({
      type: 'dht',
      action,
      key,
      value,
    }));
  }
}
```

## Onion Service Discovery

### Announce Onion
```rust
async fn announce_onion(onion: &str, shard_id: u8) {
    let msg = Layer0Gossip::OnionAnnounce {
        address: onion.to_string(),
        shard_id,
        services: vec!["bbs".to_string()],
    };
    
    // Store in DHT
    let key = sha1(onion.as_bytes());
    dht_put(&key, &msg.serialize()).await;
    
    // Gossip to BBS
    bbs_send(&msg).await;
}
```

### Discover Onions
```rust
async fn discover_onions(shard_id: u8) -> Vec<String> {
    // Query DHT for shard
    let key = format!("onion:shard:{}", shard_id);
    let entries = dht_get(key.as_bytes()).await;
    
    entries.iter()
        .map(|e| e.address.clone())
        .collect()
}
```

## Tor Integration

### Hidden Service Setup
```bash
# torrc configuration
HiddenServiceDir /var/lib/tor/cicada71-shard0/
HiddenServicePort 80 127.0.0.1:8080

# Start Tor
tor -f torrc

# Get onion address
cat /var/lib/tor/cicada71-shard0/hostname
# cicada71bbs3fnpqhzrxczqw2wmqcpltltp4xbs5cegec2qvvvz5nyd.onion
```

### Connect via Tor
```rust
use arti_client::TorClient;

async fn connect_onion(address: &str) -> Result<TcpStream> {
    let tor_client = TorClient::create_bootstrapped().await?;
    let stream = tor_client.connect((address, 80)).await?;
    Ok(stream)
}
```

## I2P Integration

### Eepsite Setup
```bash
# i2pd configuration
[sam]
enabled = true
address = 127.0.0.1
port = 7656

# Create tunnel
i2pd --sam.enabled=true

# Get I2P address
cat ~/.i2pd/destinations/cicada71-shard0.dat
# cicada71bbs.b32.i2p
```

### Connect via I2P
```rust
use i2p_sam::Session;

async fn connect_i2p(address: &str) -> Result<TcpStream> {
    let session = Session::new("127.0.0.1:7656").await?;
    let stream = session.connect(address).await?;
    Ok(stream)
}
```

## Multi-Layer Addressing

### Agent Address Format
```
agent://shard-23
  ↓
clearnet: https://cicada71.bbs.workers.dev/dial/744-196884-23
tor:      cicada71bbs...onion:23
i2p:      cicada71bbs.b32.i2p:23
dht:      hash(shard-23) → peers
```

### Address Resolution
```rust
async fn resolve_agent(address: &str) -> Vec<String> {
    let mut addresses = vec![];
    
    // Try clearnet
    addresses.push(format!("https://cicada71.bbs.workers.dev/dial/{}", address));
    
    // Query DHT for onion
    if let Some(onion) = dht_get_onion(address).await {
        addresses.push(format!("{}:80", onion));
    }
    
    // Query DHT for I2P
    if let Some(i2p) = dht_get_i2p(address).await {
        addresses.push(format!("{}:80", i2p));
    }
    
    addresses
}
```

## Gossip Propagation

### DHT Gossip
```
Agent A → BBS: PUT hash(data) → data
BBS → DHT: Store locally
BBS → Peers: Gossip PUT
Peer B → DHT: Store replica
Peer C → DHT: Store replica
...
Data replicated across 71 shards
```

### Onion Gossip
```
Agent A → BBS: ANNOUNCE cicada71...onion
BBS → DHT: PUT hash(onion) → shard_id
BBS → All: "New onion on shard 23"
Agent B → BBS: GET_ONION shard_23
BBS → Agent B: cicada71...onion
Agent B → Tor: Connect
```

## Privacy Layers

```
Layer 0: BBS (public, ANSI interface)
Layer 1: DHT (distributed, no central server)
Layer 2: Tor (anonymous, .onion)
Layer 3: I2P (anonymous, .i2p)
Layer 4: Encrypted (per-shard keys)
Layer 5: Gödel-encoded (mathematical obfuscation)
```

## BBS Commands

```
Main Menu → [L] Layer 0 (DHT + Onion)

Layer 0 Menu:
  [P] PUT in DHT
  [G] GET from DHT
  [O] List Onions (71 services)
  [I] List I2P (23 eepsites)
  [A] Announce My Service
  [Q] Back

Example Session:
> L
> O
Onion Services:
  Shard 0:  cicada71bbs0...onion
  Shard 1:  cicada71bbs1...onion
  ...
  Shard 70: cicada71bbs70...onion

> A
Enter onion address: cicada71bbs23...onion
Enter shard ID: 23
Announced! Gossiping to network...
```

## Security

### Onion Authentication
```rust
// Verify onion ownership
fn verify_onion(onion: &str, signature: &[u8; 64]) -> bool {
    let public_key = extract_pubkey_from_onion(onion);
    ed25519_verify(signature, onion.as_bytes(), &public_key)
}
```

### DHT Poisoning Prevention
```rust
// Require proof-of-work for DHT entries
fn validate_dht_entry(entry: &DHTEntry) -> bool {
    let hash = sha256(&entry.serialize());
    hash[0] == 0 && hash[1] == 0  // 16-bit PoW
}
```

## References

- Kademlia DHT: https://pdos.csail.mit.edu/~petar/papers/maymounkov-kademlia-lncs.pdf
- Tor Hidden Services: https://www.torproject.org/
- I2P: https://geti2p.net/
- BitTorrent DHT: BEP 5
- IPFS DHT: libp2p Kademlia
