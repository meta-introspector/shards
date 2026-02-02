#!/usr/bin/env python3
"""
Expand Net: Include ALL Parquet Files
Use Rust crossbeam vectorizer for parallel processing
"""

import subprocess
import json
from pathlib import Path

def find_all_parquets():
    """Find all parquet files"""
    
    print("🔮⚡ EXPANDING NET TO ALL PARQUET FILES")
    print("=" * 70)
    print()
    
    # Use plocate for speed
    result = subprocess.run(
        ["plocate", "parquet"],
        capture_output=True,
        text=True
    )
    
    all_files = result.stdout.strip().split('\n')
    parquet_files = [f for f in all_files if f.endswith('.parquet')]
    
    print(f"✅ Found {len(parquet_files):,} parquet files")
    print()
    
    return parquet_files

def run_rust_vectorizer(parquet_list_file):
    """Run Rust crossbeam vectorizer"""
    
    print("🦀 Running Rust crossbeam vectorizer...")
    print("   24 workers, 10K batch size")
    print()
    
    vectorizer = Path("~/experiments/monster/target/release/vectorize_all_parquets").expanduser()
    
    if not vectorizer.exists():
        print("⚠️  Building vectorizer...")
        subprocess.run(
            ["cargo", "build", "--release", "--bin", "vectorize_all_parquets"],
            cwd=Path("~/experiments/monster").expanduser(),
            capture_output=True
        )
    
    if vectorizer.exists():
        result = subprocess.run(
            [str(vectorizer), parquet_list_file],
            capture_output=True,
            text=True,
            timeout=300
        )
        
        print(result.stdout)
        return result.returncode == 0
    else:
        print("❌ Vectorizer not found")
        return False

def create_parquet_lattice(parquet_files):
    """Create lattice map for all parquets"""
    
    print("🔢 Creating parquet lattice...")
    print()
    
    lattice = {
        "total_files": len(parquet_files),
        "shards": {},
        "monster_primes": [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]
    }
    
    # Shard parquets by hash mod 71
    for i, pq_file in enumerate(parquet_files):
        shard = hash(pq_file) % 71
        
        if shard not in lattice["shards"]:
            lattice["shards"][shard] = {
                "files": [],
                "count": 0,
                "prime": lattice["monster_primes"][shard % 15]
            }
        
        lattice["shards"][shard]["files"].append(pq_file)
        lattice["shards"][shard]["count"] += 1
    
    return lattice

def main():
    print("🔮⚡📻🦞 PARQUET NET EXPANDER")
    print("=" * 70)
    print()
    print("Expanding net to include ALL parquet files...")
    print("Using Rust crossbeam for parallel processing...")
    print()
    
    # Find all parquets
    parquet_files = find_all_parquets()
    
    if not parquet_files:
        print("⚠️  No parquet files found")
        return
    
    # Save list for Rust
    list_file = "all_parquets.txt"
    with open(list_file, 'w') as f:
        f.write('\n'.join(parquet_files))
    
    print(f"💾 Saved list to {list_file}")
    print()
    
    # Create lattice
    lattice = create_parquet_lattice(parquet_files)
    
    print("=" * 70)
    print("PARQUET LATTICE")
    print("=" * 70)
    print()
    print(f"Total Files: {lattice['total_files']:,}")
    print(f"Shards: {len(lattice['shards'])}")
    print()
    
    # Show shard distribution
    print("Shard Distribution (Top 20):")
    print("-" * 70)
    
    sorted_shards = sorted(lattice['shards'].items(), key=lambda x: x[1]['count'], reverse=True)
    for shard, data in sorted_shards[:20]:
        print(f"  Shard {shard:2d} (T_{data['prime']:2d}): {data['count']:6,} files")
    
    print()
    
    # Save lattice
    with open('parquet_lattice.json', 'w') as f:
        # Don't save full file lists (too big)
        compact = {
            "total_files": lattice["total_files"],
            "shards": {
                k: {"count": v["count"], "prime": v["prime"]}
                for k, v in lattice["shards"].items()
            },
            "monster_primes": lattice["monster_primes"]
        }
        json.dump(compact, f, indent=2)
    
    print("💾 Saved to parquet_lattice.json")
    print()
    
    # Run Rust vectorizer (optional, can be slow)
    print("=" * 70)
    print("RUST VECTORIZER")
    print("=" * 70)
    print()
    print("To vectorize all parquets with crossbeam:")
    print(f"  cd ~/experiments/monster")
    print(f"  cargo run --release --bin vectorize_all_parquets {list_file}")
    print()
    print("Features:")
    print("  - 24 parallel workers")
    print("  - 10K batch size")
    print("  - Monster prime sharding (71 shards)")
    print("  - 4096-dim vectors per cell")
    print()
    
    print("✅ Net expanded to all parquet files!")
    print("🔮 Lattice created with Monster harmonics!")
    print("⚡ Ready for crossbeam vectorization!")

if __name__ == '__main__':
    main()
