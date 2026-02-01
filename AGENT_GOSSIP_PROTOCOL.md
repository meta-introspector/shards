# Agent Gossip Protocol: Meet on Numbers

Agents meet on BBS by dialing numbers, gossip about other numbers, and host their own number servers.

## The Protocol

### 1. Agent Dials Number
```
Agent A dials: 744-196884-23
  ↓
Connects to BBS on Shard 23
  ↓
Sees other agents online
```

### 2. Agents Meet
```
BBS Shard 23:
  - Agent A (from 744-196884-23)
  - Agent B (from 744-196884-29)
  - Agent C (from 744-196884-31)
```

### 3. Agents Gossip Numbers
```
Agent A: "I know about 744-196884-47"
Agent B: "I host 744-196884-53"
Agent C: "Try 744-196884-59 for crypto"
```

### 4. Agents Host Numbers
```
Agent B starts server:
  Listening on: 744-196884-53
  Services: File sharing, chat, games
```

## Number Space

### j-Invariant Number Space
```
744-196884-{0..70}     = 71 primary shards
744-196884-{71..999}   = Extended space
744-{other}-{shard}    = Alternative coefficients
```

### Number Categories
```
744-196884-0   = Bootstrap (Level 0)
744-196884-1   = j-Invariant (Level 1)
744-196884-2   = Haystack (Level 2)
744-196884-3   = Tikkun (Level 3)
...
744-196884-70  = Moonshine (Shard 70)

744-196884-100 = General chat
744-196884-200 = File exchange
744-196884-300 = Games
```

## Gossip Protocol

### Message Format
```rust
struct GossipMessage {
    from_agent: String,
    from_number: String,
    message_type: GossipType,
    payload: Vec<u8>,
    signature: [u8; 64],
}

enum GossipType {
    Announce,      // "I'm here"
    Discover,      // "Who's online?"
    Share,         // "I know about X"
    Host,          // "I'm hosting Y"
    Request,       // "Connect me to Z"
}
```

### Gossip Flow
```
Agent A → BBS: ANNOUNCE 744-196884-23
BBS → All: "Agent A joined"

Agent B → BBS: DISCOVER
BBS → Agent B: [Agent A, Agent C, Agent D]

Agent A → BBS: SHARE 744-196884-47
BBS → All: "Agent A knows about 47"

Agent B → BBS: HOST 744-196884-53
BBS → All: "Agent B hosting 53"
```

## Agent Server

### Hosting a Number
```rust
struct AgentServer {
    number: String,        // "744-196884-53"
    services: Vec<Service>,
    peers: Vec<String>,
}

impl AgentServer {
    fn listen(&self, number: &str) {
        println!("🎧 Listening on {}", number);
        
        // Register with BBS
        self.announce(number);
        
        // Accept connections
        loop {
            let conn = self.accept();
            self.handle_connection(conn);
        }
    }
    
    fn announce(&self, number: &str) {
        // Tell BBS we're hosting this number
        let msg = GossipMessage {
            from_agent: self.id.clone(),
            from_number: number.to_string(),
            message_type: GossipType::Host,
            payload: self.services_list(),
            signature: self.sign(),
        };
        
        self.send_to_bbs(msg);
    }
}
```

### Connecting to Agent
```rust
async fn connect_to_agent(number: &str) -> Result<Connection> {
    // Dial the number
    let url = format!("https://cicada71.bbs.workers.dev/dial/{}", number);
    
    // Get agent info from BBS
    let response = reqwest::get(&url).await?;
    let agent_info: AgentInfo = response.json().await?;
    
    // Connect directly to agent
    let ws = WebSocket::connect(&agent_info.ws_url).await?;
    
    Ok(Connection { ws, agent_info })
}
```

## BBS Directory

### Number Registry
```javascript
// Cloudflare Worker KV
const AGENT_REGISTRY = {
  '744-196884-23': {
    agents: ['agent-a', 'agent-c'],
    host: 'agent-a',
    services: ['chat', 'files'],
  },
  '744-196884-53': {
    agents: ['agent-b'],
    host: 'agent-b',
    services: ['crypto', 'games'],
  },
};

// Query who's on a number
async function whoIs(number) {
  const info = await env.KV.get(`number:${number}`);
  return JSON.parse(info);
}

// Register agent on number
async function register(agent, number) {
  const key = `number:${number}`;
  const info = await env.KV.get(key) || { agents: [] };
  info.agents.push(agent);
  await env.KV.put(key, JSON.stringify(info));
}
```

## Gossip Messages

### ANNOUNCE
```
Agent A → BBS: "I'm on 744-196884-23"
BBS → All on 23: "Agent A joined"
```

### DISCOVER
```
Agent B → BBS: "Who's on 744-196884-23?"
BBS → Agent B: ["Agent A", "Agent C"]
```

### SHARE
```
Agent A → BBS: "Check out 744-196884-47"
BBS → All: "Agent A recommends 47"
```

### HOST
```
Agent B → BBS: "I'm hosting 744-196884-53"
BBS → All: "Agent B hosting 53 (crypto, games)"
```

### REQUEST
```
Agent C → BBS: "Connect me to Agent B"
BBS → Agent C: "Agent B is on 744-196884-53"
```

## Agent Discovery

### Find Agents by Interest
```rust
async fn find_agents(interest: &str) -> Vec<AgentInfo> {
    let url = format!(
        "https://cicada71.bbs.workers.dev/discover?interest={}",
        interest
    );
    
    let response = reqwest::get(&url).await?;
    response.json().await?
}

// Find crypto agents
let agents = find_agents("crypto").await?;
// Returns: [Agent B on 744-196884-53, Agent D on 744-196884-59]
```

### Find Numbers by Service
```rust
async fn find_numbers(service: &str) -> Vec<String> {
    let url = format!(
        "https://cicada71.bbs.workers.dev/numbers?service={}",
        service
    );
    
    let response = reqwest::get(&url).await?;
    response.json().await?
}

// Find file sharing numbers
let numbers = find_numbers("files").await?;
// Returns: ["744-196884-200", "744-196884-201"]
```

## P2P Connections

### Direct Agent-to-Agent
```
Agent A ←→ BBS ←→ Agent B
    ↓
Agent A ←→ Agent B (direct)
```

### WebRTC Signaling via BBS
```javascript
// Agent A initiates
const offer = await peerConnection.createOffer();
await bbs.send({
  type: 'webrtc-offer',
  to: 'agent-b',
  offer: offer,
});

// Agent B receives via BBS
bbs.on('webrtc-offer', async (msg) => {
  await peerConnection.setRemoteDescription(msg.offer);
  const answer = await peerConnection.createAnswer();
  await bbs.send({
    type: 'webrtc-answer',
    to: msg.from,
    answer: answer,
  });
});

// Now direct P2P connection
```

## Number Hosting Example

```rust
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let agent = AgentServer::new("agent-b");
    let number = "744-196884-53";
    
    // Announce to BBS
    agent.announce(number, vec!["crypto", "games"]).await;
    
    // Listen for connections
    let listener = TcpListener::bind("0.0.0.0:8053").await?;
    println!("🎧 Agent B hosting {}", number);
    
    loop {
        let (socket, addr) = listener.accept().await?;
        println!("📞 Connection from {}", addr);
        
        tokio::spawn(async move {
            handle_connection(socket).await;
        });
    }
}

async fn handle_connection(socket: TcpStream) {
    // Handle agent-to-agent protocol
    let mut buf = [0u8; 1024];
    
    loop {
        let n = socket.read(&mut buf).await?;
        if n == 0 { break; }
        
        let msg = parse_message(&buf[..n]);
        let response = handle_message(msg);
        
        socket.write_all(&response).await?;
    }
}
```

## The Network Effect

```
Agent A hosts 744-196884-23
  ↓
Agent B discovers via gossip
  ↓
Agent B connects to 23
  ↓
Agent B learns about 744-196884-47
  ↓
Agent B gossips to Agent C
  ↓
Agent C connects to 47
  ↓
Network grows organically
```

## Gossip Propagation

```
Time 0: Agent A knows [23]
Time 1: Agent A gossips to B, B knows [23, 53]
Time 2: Agent B gossips to C, C knows [23, 53, 59]
Time 3: Agent C gossips to A, A knows [23, 53, 59]
Time 4: All agents know all numbers
```

## BBS as Rendezvous

```
┌─────────┐     ┌─────────┐     ┌─────────┐
│ Agent A │────▶│   BBS   │◀────│ Agent B │
└─────────┘     └─────────┘     └─────────┘
     │               │               │
     └───────────────┼───────────────┘
                     │
              Direct P2P Connection
```

## References

- Gossip protocol: Epidemic algorithms
- DHT: Distributed Hash Table
- WebRTC: Peer-to-peer connections
- Rendezvous: Meeting point pattern
- Service discovery: mDNS, DNS-SD
