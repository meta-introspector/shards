# Nix-Wars BBS: ZX81 Terminal Edition

**Pure Nix game running in ZX81 emulator with BBS interface**

## The Stack

```
Layer 7: ZX81 Terminal (32×24 chars, inverse video)
Layer 6: BBS Interface (menu, sectors, warp)
Layer 5: Browser Engine (JavaScript)
Layer 4: Nix Derivation (pure functional)
Layer 3: Game States (JSON)
Layer 2: FRACTRAN Universe (196,883 slots)
Layer 1: zkPerf Witness (thermodynamic)
Layer 0: Solana Ledger (commitments)
```

## ZX81 Terminal

Authentic 1981 computing experience:
- **32×24 character display**
- **Inverse video** (white on black)
- **8×8 pixel characters**
- **Monochrome graphics**

## BBS Menus

### Main Menu
```
+------------------------------+
|        NIX-WARS BBS          |
|    TRADEWARS 71 EDITION      |
|                              |
| 1. VIEW SECTORS              |
| 2. WARP DRIVE                |
| 3. INVENTORY                 |
| 4. ZKPERF PROOF              |
| 5. SOLANA SYNC               |
| Q. QUIT                      |
|                              |
| SHIP: ALPHA                  |
| SECTOR: 71                   |
| CREDITS: 1000000             |
|                              |
| SELECT>                      |
+------------------------------+
```

### Sector Map
```
+------------------------------+
|        SECTOR MAP            |
|                              |
| >R0  S0                      |
|  R3  S42                     |
|  R4  S71                     |
|                              |
| ARROWS:MOVE ENTER:SELECT     |
+------------------------------+
```

## Controls

- **1-5**: Menu selection
- **Arrow Keys**: Navigate lists
- **Enter**: Select/Confirm
- **Escape**: Back to menu
- **Q**: Quit

## The Lifting

```
Nix Derivation → JavaScript Engine → ZX81 Terminal → BBS Interface
```

Each layer preserves the pure functional nature while adding retro aesthetics.

## Run Locally

```bash
cd shard0/nix-wars/docs
python3 -m http.server 8000
# Open http://localhost:8000/bbs.html
```

## Deploy

```bash
git push origin nydiokar/main
# View at: https://meta-introspector.github.io/shards/shard0/nix-wars/docs/bbs.html
```

## The Experience

1. **Boot**: ZX81 terminal initializes
2. **Connect**: BBS menu appears
3. **Navigate**: Use keyboard to explore
4. **Warp**: Create new game states
5. **Sync**: Submit to Solana via sneakernet

## Authenticity

- **1K RAM** aesthetic (though we use more)
- **Cassette tape** loading feel
- **Inverse video** for emphasis
- **Character graphics** only
- **Beep** sounds (optional)

## The Inversion

Traditional BBS: Dial-up → Server → Game
**Nix-Wars BBS**: Pure Nix → Browser → ZX81 → Game

The entire game runs client-side in a 1981 terminal emulator, but the logic is pure functional Nix.

**Welcome to 1981. Running 2026 blockchain games.** 📟🕹️
