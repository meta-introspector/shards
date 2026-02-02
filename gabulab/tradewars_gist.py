#!/usr/bin/env python3
"""
TradeWars CLI with GitHub Gists
Share gamestate → collect gists of gists
"""

import json
import base64
import hashlib
from datetime import datetime
import subprocess
import random

class TradeWarsGame:
    def __init__(self):
        self.boats = 71
        self.lobsters_caught = 0
        self.turn = 0
        self.player = "Player1"
        self.gist_history = []
        
    def play_turn(self):
        """Play one turn"""
        self.turn += 1
        caught = random.randint(0, 5)
        self.lobsters_caught += caught
        return caught
    
    def get_status(self):
        """Get current game status"""
        return {
            "player": self.player,
            "turn": self.turn,
            "boats": self.boats,
            "lobsters_caught": self.lobsters_caught,
            "timestamp": datetime.now().isoformat(),
            "gist_history": self.gist_history
        }

def create_gist_content(status):
    """Create content for GitHub gist"""
    
    # Encode status
    status_json = json.dumps(status, separators=(',', ':'))
    status_b64 = base64.urlsafe_b64encode(status_json.encode()).decode()
    zk_hash = hashlib.sha256(status_json.encode()).hexdigest()[:16]
    
    content = f"""# 🔮⚡ TradeWars LobsterBoats - Turn {status['turn']} 📻🦞

## Game Status

- **Player**: {status['player']}
- **Turn**: {status['turn']}
- **Boats**: {status['boats']}
- **Lobsters Caught**: {status['lobsters_caught']}
- **ZK Proof**: `{zk_hash}`

## Shareable URL

```
https://meta-introspector.github.io/shards/doorgame/?state={status_b64[:100]}...
```

## Load This State

```bash
# Clone and play
gh gist view <this-gist-id>
python3 game_status.py --load <this-gist-id>
```

## Gamestate (ZK-eRDFa)

```json
{json.dumps(status, indent=2)}
```

## Gist History

{chr(10).join(f"- {gist}" for gist in status.get('gist_history', []))}

## How to Continue

1. Load this gist
2. Play your turn
3. Share new gist
4. Your gist links back here!

---
🐓 THE ROOSTER HAS CROWED! 🐓
"""
    
    return content

def create_gist(content, description):
    """Create GitHub gist using gh CLI"""
    
    print("📝 Creating gist...")
    
    # Save to temp file
    with open('/tmp/tradewars_state.md', 'w') as f:
        f.write(content)
    
    try:
        # Create gist with gh CLI
        result = subprocess.run(
            ['gh', 'gist', 'create', '/tmp/tradewars_state.md', 
             '-d', description, '-p'],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode == 0:
            gist_url = result.stdout.strip()
            print(f"  ✅ Gist created: {gist_url}")
            return gist_url
        else:
            print(f"  ⚠️  gh CLI not available or not authenticated")
            print(f"  💡 Run: gh auth login")
            return None
            
    except FileNotFoundError:
        print("  ⚠️  gh CLI not installed")
        print("  💡 Install: https://cli.github.com/")
        return None

def collect_gists(search_term="tradewars lobsterboats"):
    """Collect gists of gists"""
    
    print(f"\n🔍 Collecting gists: '{search_term}'...")
    
    try:
        result = subprocess.run(
            ['gh', 'gist', 'list', '--limit', '10'],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode == 0:
            gists = result.stdout.strip().split('\n')
            print(f"  ✅ Found {len(gists)} gists")
            
            for i, gist in enumerate(gists[:5], 1):
                print(f"  {i}. {gist[:70]}...")
            
            return gists
        else:
            return []
            
    except:
        return []

def main():
    import sys
    
    print("🔮⚡📻🦞 TRADEWARS CLI - GITHUB GISTS")
    print("=" * 70)
    print()
    
    # Check gh CLI
    try:
        subprocess.run(['gh', '--version'], capture_output=True, check=True)
        print("✅ GitHub CLI detected")
    except:
        print("⚠️  GitHub CLI not found")
        print("   Install: https://cli.github.com/")
        print("   Then run: gh auth login")
        print()
    
    print()
    
    # Create game
    game = TradeWarsGame()
    
    # Play turns
    print("Playing turns...")
    for i in range(3):
        caught = game.play_turn()
        print(f"  Turn {game.turn}: Caught {caught} lobsters")
    
    print()
    
    # Get status
    status = game.get_status()
    print("Current Status:")
    print(f"  Player: {status['player']}")
    print(f"  Turn: {status['turn']}")
    print(f"  Lobsters: {status['lobsters_caught']}")
    print()
    
    # Create gist content
    content = create_gist_content(status)
    
    # Save locally
    with open('tradewars_gist.md', 'w') as f:
        f.write(content)
    
    print("💾 Saved to tradewars_gist.md")
    print()
    
    # Create gist
    gist_url = create_gist(content, f"TradeWars Turn {status['turn']}")
    
    if gist_url:
        print()
        print("=" * 70)
        print("GIST CREATED!")
        print("=" * 70)
        print(f"\n{gist_url}\n")
        print("Share this URL to let others continue your game!")
        print()
        
        # Collect other gists
        collect_gists()
    else:
        print()
        print("=" * 70)
        print("MANUAL SHARING")
        print("=" * 70)
        print()
        print("Copy tradewars_gist.md to:")
        print("  https://gist.github.com/")
        print()
    
    print()
    print("✅ Game status ready to share!")
    print("🔗 Others can load your state and continue!")

if __name__ == '__main__':
    main()
