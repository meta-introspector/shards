#!/usr/bin/env python3
"""
Shard all objects from all git packfiles
Extract objects → 71 Monster shards
"""

import subprocess
import json
from pathlib import Path
from collections import defaultdict

def extract_packfile_objects(packfile):
    """Extract objects from a packfile"""
    try:
        result = subprocess.run(
            ["git", "verify-pack", "-v", packfile],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        objects = []
        for line in result.stdout.strip().split('\n'):
            if line and not line.startswith('non delta') and not line.startswith('chain'):
                parts = line.split()
                if len(parts) >= 3:
                    objects.append({
                        "sha": parts[0],
                        "type": parts[1],
                        "size": int(parts[2]) if parts[2].isdigit() else 0
                    })
        
        return objects
    except:
        return []

def shard_object(obj_sha):
    """Map object SHA to shard (0-70)"""
    # Use first 8 chars of SHA, convert to int, mod 71
    return int(obj_sha[:8], 16) % 71

def process_packfiles(packfiles, max_packs=100):
    """Process packfiles and shard objects"""
    
    print("🔮⚡ SHARDING PACKFILE OBJECTS")
    print("=" * 70)
    print()
    print(f"Processing {min(len(packfiles), max_packs)} packfiles...")
    print()
    
    shard_objects = defaultdict(list)
    total_objects = 0
    
    for i, packfile in enumerate(packfiles[:max_packs]):
        if i % 10 == 0:
            print(f"  Progress: {i}/{min(len(packfiles), max_packs)}", end='\r')
        
        objects = extract_packfile_objects(packfile)
        
        for obj in objects:
            shard = shard_object(obj["sha"])
            shard_objects[shard].append({
                "sha": obj["sha"],
                "type": obj["type"],
                "size": obj["size"],
                "packfile": Path(packfile).name
            })
            total_objects += 1
    
    print(f"\n✅ Extracted {total_objects:,} objects")
    print()
    
    return dict(shard_objects), total_objects

def display_shard_stats(shard_objects):
    """Display shard statistics"""
    
    print("=" * 70)
    print("OBJECT SHARD DISTRIBUTION")
    print("=" * 70)
    print()
    print("Shard | Objects | Types | Total Size")
    print("-" * 70)
    
    for shard_id in range(min(20, 71)):
        if shard_id in shard_objects:
            objs = shard_objects[shard_id]
            types = len(set(o["type"] for o in objs))
            total_size = sum(o["size"] for o in objs)
            print(f"{shard_id:5d} | {len(objs):7d} | {types:5d} | {total_size:12,}")
    
    print()
    
    # Summary
    total_objs = sum(len(objs) for objs in shard_objects.values())
    total_size = sum(sum(o["size"] for o in objs) for objs in shard_objects.values())
    
    print(f"Total Objects: {total_objs:,}")
    print(f"Total Size: {total_size:,} bytes ({total_size / (1024**3):.2f} GB)")
    print(f"Shards Used: {len(shard_objects)}/71")
    print()

def main():
    import sys
    
    print("🔮⚡📻🦞 PACKFILE OBJECT SHARDER")
    print("=" * 70)
    print()
    
    # Load packfiles
    try:
        with open('packfile_shards.json', 'r') as f:
            data = json.load(f)
            all_packfiles = []
            for shard_data in data['shards'].values():
                all_packfiles.extend(shard_data['files'])
    except:
        print("⚠️  Run read_packfiles.py first")
        return
    
    print(f"Found {len(all_packfiles)} packfiles")
    print()
    
    # Process (limit to avoid timeout)
    max_packs = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    shard_objects, total = process_packfiles(all_packfiles, max_packs)
    
    # Display
    display_shard_stats(shard_objects)
    
    # Save (compact - just counts)
    output = {
        "total_objects": total,
        "packfiles_processed": min(len(all_packfiles), max_packs),
        "shards": {
            k: {
                "count": len(v),
                "size": sum(o["size"] for o in v),
                "types": list(set(o["type"] for o in v)),
                "sample": v[:5]  # First 5 objects
            }
            for k, v in shard_objects.items()
        }
    }
    
    with open('packfile_objects_sharded.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to packfile_objects_sharded.json")
    print()
    print("✅ All packfile objects sharded into 71 Monster shards!")
    print("🔮 Ready for Monster harmonic analysis!")

if __name__ == '__main__':
    main()
