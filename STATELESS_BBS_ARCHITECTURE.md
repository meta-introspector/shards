# Stateless BBS Door System - zkERDFa URLs

## Architecture

**No server state. Everything in signed URLs. P2P discovery.**

```
User calls phone → Gets zkERDFa URL → Session in URL → P2P connect
```

## zkERDFa Session URL Format

```
zkerdfa://bbs.8080.monster/session?
  user=<pubkey>&
  shard=<0-70>&
  game=<game_id>&
  state=<base64_state>&
  sig=<ed25519_signature>
```

### Example
```
zkerdfa://bbs.8080.monster/session?
  user=ed25519:ABC123...&
  shard=17&
  game=perfect-pack&
  state=eyJzY29yZSI6MTAwLCJsZXZlbCI6NX0=&
  sig=DEF456...
```

## Components

### 1. Phone Number (Twilio)
```
+1-808-017-4247  (8080174247 - Monster order prefix!)
```

Users call → IVR → Generate zkERDFa URL → Send via SMS

### 2. Stateless Session
```rust
struct Session {
    user_pubkey: [u8; 32],
    shard: u8,           // 0-70 (Hecke × Bott)
    game: String,        // "perfect-pack", "meme-detector", etc.
    state: GameState,    // Serialized game state
    timestamp: u64,
    signature: [u8; 64], // Ed25519 signature
}

impl Session {
    fn to_url(&self) -> String {
        let state_b64 = base64::encode(&self.state);
        format!(
            "zkerdfa://bbs.8080.monster/session?user={}&shard={}&game={}&state={}&sig={}",
            hex::encode(&self.user_pubkey),
            self.shard,
            self.game,
            state_b64,
            hex::encode(&self.signature)
        )
    }
    
    fn from_url(url: &str) -> Result<Self, Error> {
        // Parse URL, verify signature
        // No server state needed!
    }
}
```

### 3. P2P Discovery
```rust
// Users find each other via libp2p
use libp2p::{mdns, kad, gossipsub};

struct P2PNode {
    peer_id: PeerId,
    shard: u8,  // Connect to same shard
}

impl P2PNode {
    fn discover_peers(&mut self) {
        // mDNS for local discovery
        // Kademlia DHT for global discovery
        // Filter by shard (0-70)
    }
    
    fn share_session(&self, url: &str) {
        // Gossip zkERDFa URL to peers
        // No central server!
    }
}
```

### 4. Game State Updates
```rust
// Each action creates new signed URL
fn update_state(session: Session, action: Action) -> Session {
    let mut new_session = session.clone();
    new_session.state.apply(action);
    new_session.timestamp = now();
    new_session.signature = sign(&new_session);
    new_session
}

// Share new URL via P2P
fn broadcast_update(session: &Session, peers: &[PeerId]) {
    let url = session.to_url();
    for peer in peers {
        send_to_peer(peer, &url);
    }
}
```

## Flow

### 1. User Calls BBS
```
User → +1-808-017-4247
IVR: "Welcome to Monster BBS! Press 1 for games, 2 for chat"
User: 1
IVR: "Generating your session..."
```

### 2. Generate Session URL
```rust
let user_pubkey = generate_keypair();
let shard = shard_data(&user_pubkey);  // Hecke × Bott → 0-70
let session = Session {
    user_pubkey,
    shard,
    game: "menu".to_string(),
    state: GameState::default(),
    timestamp: now(),
    signature: [0; 64],
};
let url = session.to_url();
```

### 3. Send URL via SMS
```
SMS to user:
"Your Monster BBS session:
zkerdfa://bbs.8080.monster/session?user=ABC...&shard=17&...

Open in browser or terminal client.
No server needed - session is in URL!"
```

### 4. User Opens URL
```bash
# Terminal client
monster-bbs zkerdfa://bbs.8080.monster/session?...

# Or browser
https://bbs.8080.monster/client#zkerdfa://...
```

### 5. P2P Connect
```rust
// Client connects to P2P network
let node = P2PNode::new(session.shard);
node.discover_peers();  // Find others on same shard

// Share session
node.share_session(&session.to_url());

// Receive updates from peers
for update in node.receive() {
    let peer_session = Session::from_url(&update)?;
    if peer_session.shard == session.shard {
        display_peer(peer_session);
    }
}
```

### 6. Play Game
```rust
// All 11 Rust tools available
match session.game.as_str() {
    "perfect-pack" => run_perfect_pack(&session),
    "meme-detector" => run_meme_detector(&session),
    "magic-market" => run_magic_market(&session),
    "extract-lmfdb" => run_extract_lmfdb(&session),
    // ... all 11 tools
    _ => show_menu(&session),
}
```

### 7. Update State
```rust
// User makes move
let action = Action::SelectGame("meme-detector");
let new_session = update_state(session, action);

// New URL generated
let new_url = new_session.to_url();

// Broadcast to peers
node.broadcast_update(&new_session);

// User gets new URL (via SMS or display)
println!("New session URL: {}", new_url);
```

## Benefits

### No Server State ✅
- Session entirely in URL
- No database needed
- No session storage
- Stateless architecture

### P2P Discovery ✅
- Users find each other via libp2p
- No central matchmaking
- Shard-based grouping (0-70)
- Local + global discovery

### Signed URLs ✅
- Ed25519 signatures
- Tamper-proof
- Verifiable by anyone
- No trust needed

### Phone Integration ✅
- Twilio for calls/SMS
- IVR menu system
- URL delivery via SMS
- Works on any device

## Implementation

### Rust BBS Client
```rust
// bbs_door/src/stateless_client.rs
use libp2p::*;
use ed25519_dalek::*;

struct StatelessBBS {
    keypair: Keypair,
    session: Session,
    p2p: P2PNode,
    games: Vec<Game>,
}

impl StatelessBBS {
    fn from_url(url: &str) -> Result<Self, Error> {
        let session = Session::from_url(url)?;
        let p2p = P2PNode::new(session.shard);
        
        Ok(Self {
            keypair: load_or_generate_keypair(),
            session,
            p2p,
            games: load_all_games(),  // All 11 Rust tools
        })
    }
    
    fn run(&mut self) {
        loop {
            // Display current state
            self.display();
            
            // Get user input
            let action = self.get_input();
            
            // Update state
            self.session = update_state(self.session.clone(), action);
            
            // Broadcast new URL
            self.p2p.broadcast_update(&self.session);
            
            // Check for peer updates
            self.check_peers();
        }
    }
}
```

### Phone Number Setup
```bash
# Twilio setup
twilio phone-numbers:buy --country-code US --area-code 808

# Configure webhook
twilio phone-numbers:update +18080174247 \
  --voice-url https://bbs.8080.monster/ivr
```

### IVR Handler
```rust
// Handle incoming calls
#[post("/ivr")]
async fn handle_call(call: TwilioCall) -> TwiML {
    let user_pubkey = generate_keypair().public;
    let shard = shard_data(&user_pubkey);
    let session = Session::new(user_pubkey, shard);
    let url = session.to_url();
    
    // Send SMS with URL
    send_sms(&call.from, &format!("Your BBS session: {}", url));
    
    // Voice response
    twiml! {
        Say("Welcome to Monster BBS. Check your phone for your session URL.")
    }
}
```

## Next Steps

1. ✅ Rust tools ready (11 games)
2. ⏳ Add libp2p for P2P
3. ⏳ Implement zkERDFa URL encoding
4. ⏳ Setup Twilio phone number
5. ⏳ Deploy stateless BBS client

**⊢ Stateless BBS with zkERDFa URLs + P2P discovery ∎** 📞🐯✨
