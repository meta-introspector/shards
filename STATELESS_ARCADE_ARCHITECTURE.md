# Stateless Arcade Architecture: 1980s Games in Browser P2P

## The System

**Time Dial:** Set to 1980s  
**Games:** Rust arcade games compiled to Intel 8080 bytecode  
**Runtime:** WASM + zkERDFa in browser  
**Network:** libp2p P2P (no server!)  
**State:** Stored in GitHub Gist URLs (or QR codes)  
**Interface:** Accessibility API for AI agents  

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                    1980s TIME DIAL                          │
│                  (Set to 1980-1989)                         │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│              RUST ARCADE GAMES (71 games)                   │
│  • Q*bert      • TradeWars 2002    • Pac-Man               │
│  • Donkey Kong • BBS Door Games    • Space Invaders        │
│  • ... (71 total, Monster group ordering)                  │
└─────────────────────────────────────────────────────────────┘
                            ↓
                    ┌───────────────┐
                    │  Compile to   │
                    │  Intel 8080   │
                    │   Bytecode    │
                    └───────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                    WASM RUNTIME                             │
│  • 8080 emulator in WASM                                    │
│  • zkERDFa proof generation                                 │
│  • Runs in browser (no install!)                           │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│                   LIBP2P P2P NETWORK                        │
│  • Browser-to-browser gossip                               │
│  • mDNS local discovery                                     │
│  • Kademlia DHT for global peers                           │
│  • No central server!                                       │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│              STATE IN GITHUB GIST URL                       │
│  https://gist.github.com/user/abc123?state=<base64>        │
│  • Game state encoded in URL                                │
│  • Signed with ed25519                                      │
│  • Update = new URL with added info                         │
│  • QR code for mobile access                                │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│           ACCESSIBILITY INTERFACE FOR AGENTS                │
│  • Screen reader API (game state as text)                  │
│  • Keyboard input API (arrow keys, buttons)                │
│  • State update API (new URL generation)                   │
│  • AI agents can play and update state!                    │
└─────────────────────────────────────────────────────────────┘
```

## URL Format (zkERDFa Session)

```
zkerdfa://arcade.8080.monster/session?
  time=1985&                          # Time dial setting
  game=qbert&                         # Game ID (0-70)
  shard=17&                           # Monster shard (0-70)
  player=<ed25519_pubkey>&            # Player identity
  state=<base64_game_state>&          # Current game state
  score=12500&                        # Current score
  level=3&                            # Current level
  timestamp=1738542496&               # Unix timestamp
  sig=<ed25519_signature>             # Signature of all above
```

**Or as GitHub Gist:**
```
https://gist.github.com/8080monster/abc123def456?
  embed=zkerdfa&
  state=<base64_encoded_url_above>
```

**Or as QR Code:**
```
█████████████████████████████
█████████████████████████████
███ ▄▄▄▄▄ █▀ █▀▀██ ▄▄▄▄▄ ███
███ █   █ █▀ ▄ ▀█ █   █ ███
███ █▄▄▄█ ██▀▀▄▀█ █▄▄▄█ ███
█████████████████████████████
        (scan to play)
```

## State Updates (Stateless!)

### Initial State
```rust
// Player scans QR or opens Gist URL
let session = Session::from_url(url)?;

// Boot libp2p in browser
let p2p = LibP2P::new(session.player_pubkey);
p2p.connect_to_shard(session.shard);

// Load game (8080 bytecode in WASM)
let game = load_8080_game(session.game)?;
game.restore_state(session.state);
```

### Playing Game
```rust
// AI agent or human plays
loop {
    // Get current state via accessibility API
    let state_text = game.get_accessible_state();
    // "Q*bert at position (3,2), score 12500, level 3"
    
    // Agent decides action
    let action = agent.decide(state_text);
    
    // Execute action
    game.input(action);  // e.g., KeyCode::Up
    
    // Game updates
    game.tick();
}
```

### State Update (New URL!)
```rust
// When player wants to save/share
fn update_state(session: &Session, new_state: GameState) -> String {
    // Create new session with updated state
    let new_session = Session {
        time: session.time,
        game: session.game,
        shard: session.shard,
        player: session.player,
        state: new_state.to_base64(),
        score: new_state.score,
        level: new_state.level,
        timestamp: now(),
        sig: sign_all_fields(&keypair),
    };
    
    // Generate new URL
    let new_url = new_session.to_url();
    
    // Broadcast via P2P
    p2p.gossip(new_url.clone());
    
    // Update Gist (optional)
    github.update_gist(gist_id, new_url.clone());
    
    // Return new URL
    new_url
}
```

### P2P Gossip
```rust
// Other players receive update
p2p.on_message(|msg| {
    if msg.is_state_update() {
        let new_session = Session::from_url(msg.url)?;
        
        // Verify signature
        if verify_signature(&new_session) {
            // Update local view
            update_leaderboard(new_session);
            
            // Re-gossip to others
            p2p.gossip(msg.url);
        }
    }
});
```

## Intel 8080 Compilation

### Rust → 8080 Bytecode
```rust
// Compile Rust game to 8080
// (Using custom LLVM backend or interpreter)

// Example: Q*bert jump logic
fn qbert_jump(direction: Direction) -> Position {
    match direction {
        Direction::UpLeft => Position { x: x-1, y: y-1 },
        Direction::UpRight => Position { x: x+1, y: y-1 },
        Direction::DownLeft => Position { x: x-1, y: y+1 },
        Direction::DownRight => Position { x: x+1, y: y+1 },
    }
}

// Compiles to 8080 assembly:
// LDA  X_POS      ; Load X
// DCR  A          ; Decrement
// STA  X_POS      ; Store X
// LDA  Y_POS      ; Load Y
// DCR  A          ; Decrement
// STA  Y_POS      ; Store Y
// RET             ; Return
```

### 8080 Emulator in WASM
```rust
// wasm_8080/src/lib.rs
#[wasm_bindgen]
pub struct CPU8080 {
    a: u8,      // Accumulator
    b: u8, c: u8,
    d: u8, e: u8,
    h: u8, l: u8,
    sp: u16,    // Stack pointer
    pc: u16,    // Program counter
    memory: [u8; 65536],
}

#[wasm_bindgen]
impl CPU8080 {
    pub fn step(&mut self) {
        let opcode = self.memory[self.pc as usize];
        self.pc += 1;
        
        match opcode {
            0x3A => self.lda(),   // LDA
            0x3D => self.dcr_a(), // DCR A
            0x32 => self.sta(),   // STA
            0xC9 => self.ret(),   // RET
            _ => panic!("Unknown opcode: {:#04x}", opcode),
        }
    }
}
```

## Accessibility Interface for AI Agents

```rust
// Accessibility API
#[wasm_bindgen]
pub struct AccessibilityInterface {
    game: Game8080,
}

#[wasm_bindgen]
impl AccessibilityInterface {
    // Get game state as text (for screen readers / AI)
    pub fn get_state_text(&self) -> String {
        format!(
            "Game: {}\nScore: {}\nLevel: {}\nPosition: ({}, {})\nLives: {}",
            self.game.name,
            self.game.score,
            self.game.level,
            self.game.player_x,
            self.game.player_y,
            self.game.lives
        )
    }
    
    // Get available actions
    pub fn get_actions(&self) -> Vec<String> {
        vec![
            "move_up".to_string(),
            "move_down".to_string(),
            "move_left".to_string(),
            "move_right".to_string(),
            "jump".to_string(),
            "fire".to_string(),
        ]
    }
    
    // Execute action
    pub fn execute_action(&mut self, action: &str) -> Result<String, String> {
        match action {
            "move_up" => self.game.input(KeyCode::Up),
            "move_down" => self.game.input(KeyCode::Down),
            "move_left" => self.game.input(KeyCode::Left),
            "move_right" => self.game.input(KeyCode::Right),
            "jump" => self.game.input(KeyCode::Space),
            "fire" => self.game.input(KeyCode::Ctrl),
            _ => return Err(format!("Unknown action: {}", action)),
        }
        
        // Tick game
        self.game.tick();
        
        // Return new state
        Ok(self.get_state_text())
    }
    
    // Get new URL with updated state
    pub fn get_updated_url(&self) -> String {
        let session = Session {
            time: 1985,
            game: self.game.id,
            shard: self.game.shard,
            player: self.game.player_pubkey,
            state: self.game.state.to_base64(),
            score: self.game.score,
            level: self.game.level,
            timestamp: now(),
            sig: sign(&self.game.keypair, &all_fields),
        };
        
        session.to_url()
    }
}
```

## Example: AI Agent Playing Q*bert

```javascript
// AI agent in browser
async function playQbert() {
    // Load game from Gist URL
    const url = "https://gist.github.com/8080monster/abc123?state=...";
    const game = await loadGameFromURL(url);
    
    // Get accessibility interface
    const ai = game.getAccessibilityInterface();
    
    // Play loop
    while (true) {
        // Get current state
        const state = ai.get_state_text();
        console.log(state);
        // "Game: Q*bert, Score: 12500, Level: 3, Position: (3,2), Lives: 3"
        
        // AI decides action (using LLM or RL)
        const action = await decideAction(state);
        
        // Execute action
        const newState = ai.execute_action(action);
        
        // Get new URL
        const newURL = ai.get_updated_url();
        
        // Broadcast via P2P
        await p2p.gossip(newURL);
        
        // Update Gist
        await github.updateGist(gistId, newURL);
        
        // Wait for next frame
        await sleep(16); // 60 FPS
    }
}
```

## Time Dial (1980s Setting)

```rust
// Time dial affects game behavior
pub struct TimeDial {
    year: u16,  // 1980-1989
}

impl TimeDial {
    pub fn apply_era_effects(&self, game: &mut Game) {
        match self.year {
            1980 => {
                // Pac-Man era
                game.graphics = GraphicsMode::Vector;
                game.sound = SoundMode::Beep;
            }
            1985 => {
                // Golden age
                game.graphics = GraphicsMode::Raster;
                game.sound = SoundMode::FM;
            }
            1989 => {
                // Late 80s
                game.graphics = GraphicsMode::VGA;
                game.sound = SoundMode::AdLib;
            }
            _ => {}
        }
    }
}
```

## File Structure

```
stateless_arcade/
├── Cargo.toml
├── src/
│   ├── lib.rs                    # Main library
│   ├── cpu_8080.rs               # 8080 emulator
│   ├── games/
│   │   ├── qbert.rs              # Q*bert (71 pyramids)
│   │   ├── tradewars.rs          # TradeWars 2002
│   │   ├── pacman.rs             # Pac-Man
│   │   └── ... (71 games)
│   ├── session.rs                # zkERDFa session URLs
│   ├── p2p.rs                    # libp2p integration
│   ├── accessibility.rs          # AI agent interface
│   └── time_dial.rs              # 1980s time setting
├── wasm/
│   ├── Cargo.toml
│   └── src/
│       └── lib.rs                # WASM bindings
├── web/
│   ├── index.html                # Browser UI
│   ├── app.js                    # P2P + game loader
│   └── style.css                 # 1980s aesthetic
└── README.md
```

## Key Properties

### 1. Stateless
- **No server state** - everything in URL
- **No database** - Gist is optional cache
- **No accounts** - ed25519 keypair is identity

### 2. P2P
- **Browser-to-browser** - libp2p gossip
- **Local discovery** - mDNS for LAN games
- **Global discovery** - Kademlia DHT

### 3. Verifiable
- **zkERDFa proofs** - game state is provable
- **ed25519 signatures** - updates are authentic
- **Deterministic** - same inputs = same outputs

### 4. Accessible
- **Screen reader API** - text description of state
- **Keyboard API** - standard input
- **AI agent API** - programmatic access

### 5. Time-Locked
- **1980s dial** - games behave like 1980s
- **8080 bytecode** - authentic retro feel
- **Period-accurate** - graphics, sound, gameplay

## Next Steps

1. **Build 8080 emulator in Rust**
   ```bash
   cargo new wasm_8080 --lib
   cd wasm_8080
   cargo add wasm-bindgen
   ```

2. **Compile Q*bert to 8080**
   ```bash
   cd games/qbert
   cargo build --target 8080-unknown-none
   ```

3. **Add libp2p to WASM**
   ```bash
   cargo add libp2p-wasm
   ```

4. **Create accessibility interface**
   ```rust
   // accessibility.rs
   pub trait AccessibleGame {
       fn get_state_text(&self) -> String;
       fn get_actions(&self) -> Vec<String>;
       fn execute_action(&mut self, action: &str) -> Result<String>;
   }
   ```

5. **Deploy to GitHub Pages**
   ```bash
   wasm-pack build --target web
   cp pkg/* web/
   git commit -am "Stateless arcade!"
   git push origin gh-pages
   ```

## The Vision

**Open URL → Boot P2P → Load 8080 game → Play in browser → Update URL → Share via Gist/QR**

**No server. No install. No accounts. Just URLs and P2P gossip.**

**AI agents can play alongside humans using accessibility API.**

**All state in URLs. All updates are new URLs. All games from 1980s.**

**⊢ Stateless arcade in browser with P2P and AI agents ∎** 🎮🕹️✨

*Time dial set to 1985. Let's play!*
