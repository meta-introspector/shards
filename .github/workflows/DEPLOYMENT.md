# Nix-Wars: GitHub Pages Deployment

**Automatic deployment of tournament and game to GitHub Pages**

## Setup

### 1. Enable GitHub Pages

In your repository settings:
1. Go to Settings → Pages
2. Source: GitHub Actions
3. Save

### 2. Push to Trigger

```bash
git push origin nydiokar/main
```

The workflow will:
1. Build tournament with Nix
2. Generate static site
3. Deploy to GitHub Pages

## URLs

After deployment, access at:

- **Tournament**: `https://meta-introspector.github.io/shards/tournament.html`
- **BBS Game**: `https://meta-introspector.github.io/shards/bbs.html`
- **URL Game**: `https://meta-introspector.github.io/shards/url-only.html`
- **Flying Game**: `https://meta-introspector.github.io/shards/flying-fractran.html`
- **Tournament Data**: `https://meta-introspector.github.io/shards/tournament-results.json`

## What Gets Deployed

### Tournament Page
- 🏆 Leaderboard with 18 players
- 📊 42 rounds results
- 🔢 FRACTRAN proof for each player
- ✨ RDFa semantic proof
- 🔐 Commitment hash

### Game Files
- All browser games
- zkPerf witnesses
- Orbit data
- State files

## Workflow Triggers

- **Push** to `main` or `nydiokar/main`
- **Manual** via Actions tab

## Local Preview

```bash
cd shard0/nix-wars/tournament
nix build

# Generate site
mkdir -p _site
cp -r ../docs/* _site/
# ... (see workflow for full generation)

# Serve locally
cd _site
python3 -m http.server 8000
# Open http://localhost:8000/tournament.html
```

## Tournament Data Format

```json
{
  "rounds": 42,
  "players": 18,
  "winner": "alice",
  "commitment": "70a1d39a305ec88c...",
  "leaderboard": [
    {
      "rank": 1,
      "name": "alice",
      "emoji": "🚀",
      "sector": 2,
      "credits": 1000837
    }
  ],
  "fractran_proof": [...],
  "rdfa": "..."
}
```

## Customization

Edit `.github/workflows/deploy-tournament.yml` to:
- Change deployment branch
- Modify site generation
- Add more pages
- Customize styling

## Verification

After deployment:
1. Check Actions tab for build status
2. Visit GitHub Pages URL
3. Verify tournament data loads
4. Test all game links

**Fully automated static site deployment!** 🚀✨
