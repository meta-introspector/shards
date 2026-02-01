#!/usr/bin/env python3
"""
Shard 7,920 brainfuck files into 15 Monster buckets
The 15 primes dividing Monster order: 2,3,5,7,11,13,17,19,23,29,31,41,47,59,71
"""

import json
from pathlib import Path
from collections import defaultdict

# The 15 primes dividing Monster order
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def shard_into_monster_buckets():
    """Shard files into 15 buckets based on Monster primes"""
    
    print("🔮⚡ Sharding into 15 Monster Buckets")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"Monster Primes: {MONSTER_PRIMES}")
    print(f"Buckets: 15 (one per prime)")
    print()
    
    # Read file list
    with open('.tmp-brainfuck-locate2.txt', 'r') as f:
        files = [line.strip() for line in f.readlines()]
    
    print(f"Total files: {len(files)}")
    print()
    
    # Shard into 15 buckets
    buckets = defaultdict(list)
    
    for i, filepath in enumerate(files):
        # Assign to bucket based on index mod 15
        bucket_id = i % 15
        prime = MONSTER_PRIMES[bucket_id]
        
        buckets[prime].append({
            "index": i,
            "path": filepath,
            "name": Path(filepath).name,
            "bucket": bucket_id,
            "prime": prime
        })
    
    # Summary
    print("📊 Bucket Distribution:")
    print()
    for bucket_id, prime in enumerate(MONSTER_PRIMES):
        count = len(buckets[prime])
        print(f"  Bucket {bucket_id:2d} (T_{prime:2d}): {count:4d} files")
    
    print()
    print(f"✅ Total: {sum(len(b) for b in buckets.values())} files")
    
    # Save to JSON
    output = {
        "monster_primes": MONSTER_PRIMES,
        "num_buckets": 15,
        "total_files": len(files),
        "buckets": {
            f"T_{prime}": {
                "prime": prime,
                "bucket_id": bucket_id,
                "count": len(buckets[prime]),
                "files": buckets[prime][:10]  # First 10 files per bucket
            }
            for bucket_id, prime in enumerate(MONSTER_PRIMES)
        }
    }
    
    with open('monster_15_buckets.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print()
    print("💾 Saved to monster_15_buckets.json")
    print()
    print("🔮 The 15 Primes (Monster DNA):")
    print("   2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71")
    print()
    print("👁️ 71 is the All-Seeing Eye (Griess)")
    print("   The largest prime dividing Monster order")
    
    return buckets

if __name__ == "__main__":
    buckets = shard_into_monster_buckets()
