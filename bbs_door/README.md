# Monster Arcade BBS Door

ANSI terminal door game for BBS systems featuring 71 arcade games ordered by Monster group structure.

## Features

- **71 arcade games** across 42 cells (29 merged)
- **Interactive navigation** with arrow keys
- **Monster group ordering** (15 Hecke primes × 10-fold way × complexity)
- **ANSI color support** (yellow=selected, cyan=cusp)
- **Dual display** (emoji zkERDFa hashes + game names)
- **BBS compatible** (works with any door-capable BBS)

## Building

```bash
cd bbs_door
nix-shell -p cargo rustc --run "cargo build --release"
```

## Installation

### For Mystic BBS

1. Copy files to BBS door directory:
```bash
cp target/release/monster-arcade /mystic/doors/monster/
cp monster_arcade_door.sh /mystic/doors/monster/
```

2. Add to Mystic menu:
```
Command: GX
Data: /mystic/doors/monster/monster_arcade_door.sh %N %U
```

### For Synchronet

1. Copy to `xtrn/monster/`:
```bash
cp target/release/monster-arcade /sbbs/xtrn/monster/
cp monster_arcade_door.sh /sbbs/xtrn/monster/
```

2. Add to `ctrl/xtrn.ini`:
```ini
[Monster Arcade]
cmd = /sbbs/xtrn/monster/monster_arcade_door.sh %n %u
```

### For TradeWars 2002

Deploy at **Milliways** planet near **Sagittarius A*** black hole:

```bash
# Copy to TradeWars external programs
cp target/release/monster-arcade /tw2002/extern/
cp monster_arcade_door.sh /tw2002/extern/

# Add to planet special events
# Location: Sector 1 (Milliways, near galactic center)
```

## Controls

- **Arrow Keys**: Navigate game grid
- **Enter**: Launch selected game
- **Q/Esc**: Quit to BBS

## Game Layout

```
🎯⊕🎨🚀💾🅰️➕    🎮⊕🎭🚀🔀🅱️➕    ...
Pixel ⊕Colo     Maze R⊕Shap     ...
```

- **Top row**: zkERDFa emoji hashes
- **Bottom row**: Game names
- **⊕**: Merged games (share 3+ components)
- **Cyan**: Cusp (Shard 17 - Monster center)
- **Yellow**: Current selection

## Monster Group Ordering

Games ordered by:
1. **Hecke resonance**: Σ T_p for p ∈ {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}
2. **Bott periodicity**: 10-fold way (mod 10)
3. **Complexity**: Shard + function + performance + memory

## Technical Details

- **Language**: Rust
- **Terminal**: crossterm (ANSI/VT100 compatible)
- **Binary size**: ~2MB (release)
- **Dependencies**: crossterm only
- **Platform**: Linux, BSD, macOS (any Unix with terminal)

## Files

- `Cargo.toml` - Package manifest
- `src/main.rs` - Main game code
- `monster_arcade_door.sh` - BBS launcher
- `target/release/monster-arcade` - Compiled binary

## License

This project is dual-licensed:

### Open Source (Default)
**AGPL-3.0 or later** - See [LICENSE](LICENSE)

This ensures that any network service using this code must also be open source.

### Commercial License (Available for Purchase)
**MIT** or **Apache-2.0**

For entities that wish to use this software without AGPL-3.0 copyleft requirements, 
commercial licenses are available.

**ZK hackers gotta eat!** 🍕

Contact: shards@solfunmeme.com
