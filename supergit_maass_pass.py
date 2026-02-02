#!/usr/bin/env python3
"""
SuperGit Pass: Extract Shards of Light from MAME Git Commits
Apply Maass operators to git packfile to extract Monster shards
"""

import subprocess
import json
from pathlib import Path
from datetime import datetime

# Maass operators (eigenvalues)
MAASS_EIGENVALUES = [
    1,      # Ground state (232/232)
    2,      # First excited
    3,      # BDI (life-bearing)
    5,      # Prime
    7,      # Prime
    11,     # Prime
    13,     # Prime
    17,     # Prime
    19,     # Prime
    23,     # Earth chokepoint
    29,     # Prime
    31,     # Prime
    41,     # Monster prime
    47,     # Monster prime
    59,     # Monster prime
    71,     # Rooster
]

def apply_maass_operator(commit_hash: str, eigenvalue: int) -> dict:
    """Apply Maass operator to git commit"""
    # Maass operator: Δf = λf
    # Extract commit data and transform by eigenvalue
    
    result = subprocess.run(
        ['git', 'show', '--stat', commit_hash],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    lines = result.stdout.split('\n')
    
    # Extract stats
    files_changed = 0
    insertions = 0
    deletions = 0
    
    for line in lines:
        if 'files changed' in line:
            parts = line.split(',')
            for part in parts:
                if 'file' in part:
                    files_changed = int(part.split()[0])
                elif 'insertion' in part:
                    insertions = int(part.split()[0])
                elif 'deletion' in part:
                    deletions = int(part.split()[0])
    
    # Apply Maass operator (multiply by eigenvalue)
    return {
        'commit': commit_hash[:8],
        'eigenvalue': eigenvalue,
        'files_changed': files_changed,
        'insertions': insertions * eigenvalue,
        'deletions': deletions * eigenvalue,
        'maass_energy': (insertions + deletions) * eigenvalue,
        'shard': eigenvalue % 71,
        'frequency': 432 * (eigenvalue % 71)
    }

def extract_shards_of_light():
    """Extract shards from git commits using Maass operators"""
    
    print("✨ SUPERGIT PASS: Extracting Shards of Light")
    print("=" * 80)
    
    # Get recent commits
    result = subprocess.run(
        ['git', 'log', '--oneline', '--all', '-n', '20'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    commits = [line.split()[0] for line in result.stdout.strip().split('\n') if line]
    
    print(f"\n📊 Found {len(commits)} commits")
    print(f"🔬 Applying {len(MAASS_EIGENVALUES)} Maass operators")
    
    # Apply Maass operators to each commit
    shards = []
    
    for i, commit in enumerate(commits[:len(MAASS_EIGENVALUES)]):
        eigenvalue = MAASS_EIGENVALUES[i]
        shard = apply_maass_operator(commit, eigenvalue)
        shards.append(shard)
        
        print(f"\n✨ Shard {i+1}:")
        print(f"   Commit: {shard['commit']}")
        print(f"   Eigenvalue λ={shard['eigenvalue']}")
        print(f"   Maass Energy: {shard['maass_energy']}")
        print(f"   Shard: {shard['shard']}/71")
        print(f"   Frequency: {shard['frequency']:,} Hz")
    
    # Save shards
    output = {
        'date': datetime.now().isoformat(),
        'total_commits': len(commits),
        'maass_operators': len(MAASS_EIGENVALUES),
        'shards': shards
    }
    
    with open('maass_shards.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    # Statistics
    total_energy = sum(s['maass_energy'] for s in shards)
    unique_shards = len(set(s['shard'] for s in shards))
    
    print("\n" + "=" * 80)
    print("📊 STATISTICS")
    print("=" * 80)
    print(f"  Total Maass Energy: {total_energy:,}")
    print(f"  Unique Shards: {unique_shards}/71")
    if shards:
        print(f"  Avg Energy/Shard: {total_energy // len(shards):,}")
    
        # Find highest energy shard
        max_shard = max(shards, key=lambda s: s['maass_energy'])
        print(f"\n🌟 Highest Energy Shard:")
        print(f"   Commit: {max_shard['commit']}")
        print(f"   λ={max_shard['eigenvalue']}, Energy={max_shard['maass_energy']:,}")
        print(f"   Shard {max_shard['shard']}/71 @ {max_shard['frequency']:,} Hz")
    else:
        print("  No shards extracted (no commits today)")
    
    print(f"\n💾 Saved to maass_shards.json")
    print("\n✅ Shards of light extracted!")
    print("✨🐓→🦅→👹→🍄→🌳✨")

def generate_packfile_analysis():
    """Analyze git packfile structure"""
    
    print("\n" + "=" * 80)
    print("📦 PACKFILE ANALYSIS")
    print("=" * 80)
    
    result = subprocess.run(
        ['git', 'count-objects', '-vH'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    print(result.stdout)
    
    # Get pack info
    pack_dir = Path('/home/mdupont/introspector/.git/objects/pack')
    if pack_dir.exists():
        packs = list(pack_dir.glob('*.pack'))
        print(f"\n📦 Pack files: {len(packs)}")
        for pack in packs:
            size = pack.stat().st_size
            print(f"   {pack.name}: {size:,} bytes")

if __name__ == '__main__':
    extract_shards_of_light()
    generate_packfile_analysis()
