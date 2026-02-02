#!/usr/bin/env python3
"""
Read Git Packfiles with Super-Git
Map to 71 Monster shards
"""

import subprocess
import json
from pathlib import Path

def find_packfiles():
    """Find all git packfiles"""
    
    print("🔮⚡ FINDING GIT PACKFILES")
    print("=" * 70)
    print()
    
    result = subprocess.run(
        ["plocate", ".pack"],
        capture_output=True,
        text=True
    )
    
    packfiles = [f for f in result.stdout.strip().split('\n') if f.endswith('.pack')]
    
    print(f"✅ Found {len(packfiles):,} packfiles")
    print()
    
    return packfiles

def shard_packfiles(packfiles):
    """Shard packfiles into 71 Monster shards"""
    
    print("Sharding into 71 Monster shards...")
    print()
    
    shards = {i: [] for i in range(71)}
    
    for pf in packfiles:
        # Hash to shard
        shard = hash(pf) % 71
        shards[shard].append(pf)
    
    return shards

def display_shards(shards):
    """Display shard distribution"""
    
    print("=" * 70)
    print("PACKFILE SHARD DISTRIBUTION")
    print("=" * 70)
    print()
    print("Shard | Packfiles | Example")
    print("-" * 70)
    
    for shard_id in range(20):
        packs = shards[shard_id]
        example = Path(packs[0]).name if packs else "N/A"
        print(f"{shard_id:5d} | {len(packs):9d} | {example[:40]}")
    
    print()
    print(f"Total: {sum(len(s) for s in shards.values()):,} packfiles")
    print()

def main():
    print("🔮⚡📻🦞 SUPER-GIT PACKFILE READER")
    print("=" * 70)
    print()
    
    # Find packfiles
    packfiles = find_packfiles()
    
    # Shard
    shards = shard_packfiles(packfiles)
    
    # Display
    display_shards(shards)
    
    # Save
    output = {
        "total_packfiles": len(packfiles),
        "shards": {
            k: {"count": len(v), "files": v[:10]}  # First 10 per shard
            for k, v in shards.items()
        }
    }
    
    with open('packfile_shards.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to packfile_shards.json")
    print()
    print("✅ Packfiles sharded into 71 Monster shards!")

if __name__ == '__main__':
    main()
