# TradeWars BBS - GitHub Pages Static Site

**Pure static HTML/JS game. No server. LocalStorage + ZK-RDFa shards.**

## Architecture

```
GitHub Pages (Static Host)
    ↓
index.html (Single file game)
    ↓
LocalStorage (Ship data, bets, intel)
    ↓
shards/*.json (ZK-RDFa secured bot data)
```

## Features

- ✅ Pure static HTML/CSS/JS
- ✅ No build step required
- ✅ LocalStorage for persistence
- ✅ Fetch shards from static JSON
- ✅ ZK-RDFa signature verification
- ✅ ZX81 terminal aesthetic
- ✅ Works offline after first load

## File Structure

```
frontend/
├── index.html          # Complete game (single file)
└── shards/
    ├── shard-0.json    # Nix store data
    ├── shard-1.json    # Functions data
    ├── shard-71.json   # GitHub repos data
    └── ...             # All 71 shards
```

## LocalStorage Schema

```javascript
// Ship data
localStorage.ship = {
  name: "Nebuchadnezzar",
  points: 8200,
  hunts: 12
}

// Bets
localStorage.bets = [
  {
    bot: "ElizaOS",
    predicted: 42,
    timestamp: 1738440000000
  }
]

// Intel purchased
localStorage.intel = [
  {
    type: "Location",
    purchased: 1738440000000
  }
]
```

## Shard Format (ZK-RDFa)

```json
{
  "shard_id": 71,
  "name": "GitHub Repos",
  "rdfa_namespace": "http://stego.solfunmeme.com/shard/71",
  "signature": "0x7f3a9c2b...",
  "timestamp": "2026-02-01T14:47:00Z",
  "bots": [
    {
      "name": "ElizaOS",
      "repo": "elizaos/eliza",
      "commits": 42,
      "prs": 3
    }
  ]
}
```

## Deployment

### GitHub Pages (Automatic)

1. Push to main branch
2. GitHub Actions runs
3. Deploys `frontend/` to Pages
4. Live at: `https://meta-introspector.github.io/shards/`

### Manual Deploy

```bash
# Just commit and push
git add vessels/nebuchadnezzar/frontend/
git commit -m "Update game"
git push origin main

# GitHub Actions handles the rest
```

## Local Development

```bash
# Serve locally
cd vessels/nebuchadnezzar/frontend
python -m http.server 8000

# Open browser
open http://localhost:8000
```

## Game Flow

1. **Load** - Fetch index.html from GitHub Pages
2. **Init** - Check LocalStorage for ship data
3. **Menu** - Display BBS menu
4. **Hunt** - Place bet, store in LocalStorage
5. **Scan** - Fetch shard JSON, verify signature
6. **Score** - Calculate accuracy, update points
7. **Persist** - Save to LocalStorage

## Shard Updates

```bash
# Update bot data
echo '{
  "shard_id": 71,
  "bots": [...]
}' > frontend/shards/shard-71.json

# Commit and push
git add frontend/shards/
git commit -m "Update shard 71"
git push

# Live in ~1 minute
```

## Offline Support

After first load:
- HTML cached by browser
- LocalStorage persists
- Shards cached
- Works offline

## Security

- ZK-RDFa signatures on all shards
- Verification in browser
- No server-side code
- No API keys needed
- Pure client-side

## URLs

- **Live**: https://meta-introspector.github.io/shards/
- **Repo**: https://github.com/meta-introspector/shards
- **Shards**: https://meta-introspector.github.io/shards/shards/shard-71.json

## Benefits

- ✅ Free hosting (GitHub Pages)
- ✅ No server costs
- ✅ Instant deploys
- ✅ Works offline
- ✅ No build step
- ✅ Pure static
- ✅ Fast load
- ✅ Secure (ZK-RDFa)

🌐⚡ **Static site. LocalStorage. ZK-RDFa shards. No server needed!**
