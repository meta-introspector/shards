# CICADA-71 Door Game 🔮⚡

## Standalone GitHub Pages Version

A BBS-style door game that runs entirely in the browser with eRDFa data storage.

## Features

- **71 Shards**: Visit all 71 shards (0-71)
- **ZK Proofs**: Generate zero-knowledge proofs
- **LocalStorage**: All data stored locally with eRDFa
- **No Server**: Pure client-side, works offline
- **Monster Group**: Based on 15 Monster primes
- **Hecke Operators**: Each shard maps to T_p

## Play Now

https://meta-introspector.github.io/shards/doorgame/

## Commands

```
help          - Show available commands
shard N       - Visit shard N (0-71)
proof         - Generate ZK proof
stats         - Show statistics
reset         - Reset game
name NAME     - Set player name
```

## Game Mechanics

### Shards
- 72 shards total (0-71)
- Each shard corresponds to a Hecke operator
- Visit shards to earn points (+10 per new shard)
- Click shard grid or type `shard N`

### ZK Proofs
- Generate proofs for current shard
- Earn bonus points (+50 per proof)
- Proofs stored in localStorage
- Hash verification included

### Points
- Visit new shard: +10 points
- Generate ZK proof: +50 points
- Track progress across sessions

## eRDFa Data Structure

All game data is stored with eRDFa (embedded RDF annotations):

```json
{
  "@context": "https://schema.org",
  "@type": "VideoGame",
  "name": "CICADA-71 Door Game",
  "gameItem": [
    {
      "@type": "Thing",
      "name": "Shard",
      "description": "71 shards with Hecke operators"
    }
  ]
}
```

### LocalStorage Schema

```javascript
{
  "player": "Guest",
  "currentShard": 0,
  "points": 0,
  "shardsVisited": [0, 1, 2, ...],
  "zkProofs": [
    {
      "shard": 0,
      "timestamp": 1738454400000,
      "hash": "abc123...",
      "player": "Guest"
    }
  ]
}
```

## Integration with CICADA-71

### Monster Primes
Shards map to the 15 Monster primes:
```
2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71
```

### Hecke Operators
Each shard has a Hecke operator T_p where p is prime:
- Shard 0 → T_2
- Shard 1 → T_3
- Shard 2 → T_5
- ...
- Shard 70 → T_71

### ZK Proofs
Proofs use simple hash verification:
```javascript
hash = SHA256(player + shard + timestamp + state)
```

## Deployment

### GitHub Pages

1. Enable GitHub Pages in repo settings
2. Source: `main` branch, `/doorgame` folder
3. URL: `https://meta-introspector.github.io/shards/doorgame/`

### Local Testing

```bash
cd doorgame
python -m http.server 8000
open http://localhost:8000
```

## Files

```
doorgame/
├── index.html          # Complete standalone game
└── README.md          # This file
```

## Promptbook Integration

### What is Promptbook?

[Promptbook](https://github.com/webgptorg/promptbook) is a framework for writing software in plain human language using `.book.md` files. It's the next generation of programming - executable by both humans and AI.

### CICADA-71 Book

The door game is now available as a Promptbook pipeline:

```bash
# Install promptbook
npm install -g promptbook

# Run the book
npx ptbk run cicada71.book.md \
  --input playerName="Alice" \
  --input targetShard="42"

# Or use the runner
node promptbook_runner.js Alice 42
```

### Book Structure

```markdown
# CICADA-71 Door Game

- INPUT PARAMETER {playerName}
- INPUT PARAMETER {targetShard}
- OUTPUT PARAMETER {shardResult}

## Visit Shard
- PERSONA Jane, cryptographer
- EXPECT JSON
...
```

### Features

- ✅ Visit shards via natural language
- ✅ Generate ZK proofs with AI
- ✅ Track stats and achievements
- ✅ Atmospheric lore generation
- ✅ JSON output for automation

## Future Enhancements

- [x] Promptbook integration
- [ ] Multiplayer via WebRTC
- [ ] Real ZK-SNARKs (Groth16)
- [ ] Brainfuck tape execution
- [ ] LMFDB data integration
- [ ] Monster harmonic visualization
- [ ] 8080 BBS server sync

## Technical Details

### Pure Client-Side
- No server required
- No build step
- No dependencies
- Works offline after first load

### eRDFa Annotations
- Schema.org vocabulary
- Embedded in HTML
- Machine-readable
- SEO-friendly

### Browser Compatibility
- Modern browsers (ES6+)
- LocalStorage support required
- No polyfills needed

## License

CC0 1.0 Universal (Public Domain)

## Links

- **CICADA-71**: https://github.com/meta-introspector/shards
- **Monster Group**: https://en.wikipedia.org/wiki/Monster_group
- **eRDFa**: https://www.w3.org/TR/rdfa-primer/

---

🔮⚡ **Play the game. Visit the shards. Generate the proofs.** ⚡🔮
