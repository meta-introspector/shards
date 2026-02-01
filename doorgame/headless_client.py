#!/usr/bin/env python3
"""
Headless client for CICADA-71 Door Game
Plays the game autonomously via localStorage simulation
"""

import json
import hashlib
import time
from datetime import datetime

class HeadlessPlayer:
    def __init__(self, name="Bot"):
        self.player = name
        self.current_shard = 0
        self.points = 0
        self.shards_visited = []
        self.zk_proofs = []
        
    def visit_shard(self, n):
        """Visit a shard"""
        if n > 71:
            print(f"🚨 Shard {n} is in jail! (sus)")
            return False
            
        self.current_shard = n
        
        if n not in self.shards_visited:
            self.shards_visited.append(n)
            self.points += 10
            print(f"🔮 Entered Shard {n} (T_{self.get_prime(n)})")
            print(f"   Points +10! Total: {self.points}")
            return True
        else:
            print(f"🔮 Already visited Shard {n}")
            return False
    
    def generate_zk_proof(self):
        """Generate ZK proof for current shard"""
        proof = {
            "shard": self.current_shard,
            "timestamp": int(time.time() * 1000),
            "hash": self.hash_state(),
            "player": self.player
        }
        
        self.zk_proofs.append(proof)
        self.points += 50
        
        print(f"✅ ZK Proof Generated!")
        print(f"   Hash: {proof['hash'][:16]}...")
        print(f"   Points +50! Total: {self.points}")
        
        return proof
    
    def get_prime(self, n):
        """Get prime for shard"""
        primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]
        return primes[n % 20] if n < len(primes) * 4 else 71
    
    def hash_state(self):
        """Hash current state"""
        data = json.dumps({
            "player": self.player,
            "shard": self.current_shard,
            "points": self.points,
            "visited": self.shards_visited
        })
        return hashlib.sha256(data.encode()).hexdigest()
    
    def stats(self):
        """Show statistics"""
        print(f"\n📊 Statistics:")
        print(f"   Player: {self.player}")
        print(f"   Current Shard: {self.current_shard}")
        print(f"   Points: {self.points}")
        print(f"   Shards Visited: {len(self.shards_visited)}/72")
        print(f"   ZK Proofs: {len(self.zk_proofs)}")
        print()
    
    def save_state(self, filename="headless_state.json"):
        """Save state to file (simulates localStorage)"""
        state = {
            "player": self.player,
            "currentShard": self.current_shard,
            "points": self.points,
            "shardsVisited": self.shards_visited,
            "zkProofs": self.zk_proofs
        }
        
        with open(filename, 'w') as f:
            json.dump(state, f, indent=2)
        
        print(f"💾 State saved to {filename}")
    
    def load_state(self, filename="headless_state.json"):
        """Load state from file"""
        try:
            with open(filename, 'r') as f:
                state = json.load(f)
            
            self.player = state['player']
            self.current_shard = state['currentShard']
            self.points = state['points']
            self.shards_visited = state['shardsVisited']
            self.zk_proofs = state['zkProofs']
            
            print(f"📂 State loaded from {filename}")
            return True
        except FileNotFoundError:
            print(f"⚠️  No saved state found")
            return False

def play_autonomous(player_name="HeadlessBot", num_shards=71):
    """Play the game autonomously"""
    
    print("🔮⚡ CICADA-71 Headless Client")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print()
    
    player = HeadlessPlayer(player_name)
    
    # Try to load existing state
    player.load_state()
    
    print(f"\n🤖 Bot: {player.player}")
    print(f"🎯 Mission: Visit all {num_shards} shards")
    print()
    
    # Visit all shards
    for shard in range(num_shards):
        if shard not in player.shards_visited:
            player.visit_shard(shard)
            
            # Generate proof every 10 shards
            if (shard + 1) % 10 == 0:
                player.generate_zk_proof()
                time.sleep(0.1)  # Simulate processing
    
    # Final stats
    player.stats()
    
    # Save state
    player.save_state()
    
    # Check completion
    if len(player.shards_visited) >= 71:
        print("🏆 MISSION COMPLETE!")
        print(f"   All 71 shards visited!")
        print(f"   Total points: {player.points}")
        print(f"   ZK Proofs: {len(player.zk_proofs)}")
    
    return player

if __name__ == "__main__":
    import sys
    
    player_name = sys.argv[1] if len(sys.argv) > 1 else "HeadlessBot"
    player = play_autonomous(player_name)
