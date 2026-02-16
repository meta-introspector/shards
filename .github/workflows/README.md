# Nix-Wars: GitHub Actions Game Engine

**Play the game via commits, comments, and escaped RDFa**

## How to Play

### Method 1: Commit Message
```bash
git commit -m "move:warp(alice, 0, 42)"
git push
```

### Method 2: Issue Comment
```
@alice wants to warp to sector 42
move:warp(alice, 0, 42)
```

### Method 3: Emoji Encoding
```
🚀 @alice → 42 🌌
```

### Method 4: Escaped RDFa
```
@prefix move: <http://nixwars.local/move#> .
@prefix player: <http://nixwars.local/player#> .

player:alice move:warp [
  move:from 0 ;
  move:to 42 ;
] .
```

### Method 5: Code Comment
```rust
// move:warp(bob, 42, 71)
fn main() {
    println!("Bob warps to 71!");
}
```

## What Happens

1. **GitHub Action triggers** on commit/comment
2. **Extracts move** from message (RDFa, emoji, text)
3. **Applies morphism** to current state
4. **Generates zkPerf witness** with perf metrics
5. **Commits new state** to repo
6. **Comments result** on issue/PR
7. **Deploys to server** (optional)

## Move Formats

### RDFa Format
```
move:warp(player, from, to)
```

### Emoji Format
```
🚀 @player → sector 🌌
```

### Natural Language
```
@player wants to move to sector 42
```

## Example Workflow

### 1. Alice Commits
```bash
git commit -m "Add feature X

move:warp(alice, 0, 42)
"
git push
```

### 2. Action Runs
- Extracts: `player=alice, from=0, to=42`
- Applies morphism
- Generates witness
- Commits new state

### 3. Bob Comments on PR
```
Looks good! 🚀 @bob → 71 🌌
```

### 4. Action Runs Again
- Extracts: `player=bob, to=71`
- Applies morphism
- Comments result

### 5. State Updated
```json
{
  "round": 5,
  "players": {
    "alice": {"sector": 42},
    "bob": {"sector": 71}
  }
}
```

## Witness Generated

```json
{
  "commit": "abc123...",
  "event": "push",
  "player": "alice",
  "move": {"from": 0, "to": 42},
  "timestamp": "2026-02-15T07:41:57Z",
  "commitment": "7a8ab1033862240e..."
}
```

## RDFa Symmetries

### Prefix Notation
```
move:warp(alice, 0, 42)
```

### Turtle Notation
```turtle
@prefix : <http://nixwars.local/> .
:alice :warp [ :from 0 ; :to 42 ] .
```

### JSON-LD
```json
{
  "@context": "http://nixwars.local/",
  "@type": "Move",
  "player": "alice",
  "from": 0,
  "to": 42
}
```

### Escaped in URL
```
http://nixwars.local/move?player=alice&from=0&to=42
```

### Escaped in Emoji
```
🚀(alice)→42
```

## Integration

### Local Testing
```bash
# Simulate action
cd .github/workflows
act push -e event.json
```

### View State
```bash
cd shard0/nix-wars/server
nix build
cat result | jq .
```

### Query History
```bash
git log --grep="move:warp" --oneline
```

## Security

- ✅ Moves validated before applying
- ✅ State transitions are pure
- ✅ zkPerf witness for each move
- ✅ Full audit trail in git
- ✅ Reproducible from history

## The Win

**Every commit is a game move.**

This means:
- Development = gameplay
- Code review = strategy
- Git history = game history
- Commits = state transitions
- Comments = player actions

**The repository IS the game.** 🎮✨
