#!/usr/bin/env python3
"""
Find duplicate code using Hecke resonance
Files with identical signatures = duplicates
"""

import json
from pathlib import Path
from collections import defaultdict

def find_duplicates():
    # Load previous results
    with open('cross_language_map.json') as f:
        data = json.load(f)
    
    print("🔍 FINDING DUPLICATE CODE VIA HECKE RESONANCE")
    print("=" * 70)
    print()
    
    # Group files by signature
    sig_groups = defaultdict(list)
    
    for shard_id, langs in data['shard_map'].items():
        for lang, files in langs.items():
            for file_path in files:
                # Use file path as key (simplified)
                sig_groups[file_path].append((shard_id, lang))
    
    # Find actual duplicates by checking file content
    print("📊 Scanning for duplicate files...")
    
    content_map = defaultdict(list)
    
    for shard_id, langs in data['shard_map'].items():
        for lang, files in langs.items():
            for file_path in files:
                try:
                    p = Path(file_path)
                    if p.exists() and p.stat().st_size < 100000:  # Skip large files
                        content = p.read_bytes()
                        content_hash = hash(content)
                        content_map[content_hash].append(file_path)
                except:
                    pass
    
    # Find duplicates
    duplicates = {k: v for k, v in content_map.items() if len(v) > 1}
    
    print(f"Found {len(duplicates)} groups of duplicate files")
    print()
    
    # Show top 20 duplicate groups
    print("=" * 70)
    print("🔄 TOP 20 DUPLICATE FILE GROUPS")
    print("=" * 70)
    print()
    
    sorted_dups = sorted(duplicates.items(), key=lambda x: len(x[1]), reverse=True)
    
    for i, (content_hash, files) in enumerate(sorted_dups[:20], 1):
        print(f"{i}. {len(files)} identical files:")
        for f in files[:5]:
            print(f"   • {f}")
        if len(files) > 5:
            print(f"   ... and {len(files) - 5} more")
        
        # Show file size
        try:
            size = Path(files[0]).stat().st_size
            print(f"   Size: {size:,} bytes")
        except:
            pass
        print()
    
    # Calculate waste
    total_waste = 0
    for content_hash, files in duplicates.items():
        if len(files) > 1:
            try:
                size = Path(files[0]).stat().st_size
                waste = size * (len(files) - 1)
                total_waste += waste
            except:
                pass
    
    print("=" * 70)
    print("📈 DUPLICATION STATISTICS")
    print("=" * 70)
    print()
    print(f"Total duplicate groups: {len(duplicates)}")
    print(f"Total duplicate files: {sum(len(v) for v in duplicates.values())}")
    print(f"Wasted space: {total_waste:,} bytes ({total_waste / 1024 / 1024:.1f} MB)")
    print()
    
    # Save results
    results = {
        'duplicate_groups': len(duplicates),
        'total_duplicates': sum(len(v) for v in duplicates.values()),
        'wasted_bytes': total_waste,
        'duplicates': [
            {
                'count': len(files),
                'files': files,
                'size': Path(files[0]).stat().st_size if Path(files[0]).exists() else 0
            }
            for _, files in sorted_dups[:100]
        ]
    }
    
    with open('duplicate_code.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("💾 Results saved to: duplicate_code.json")

if __name__ == "__main__":
    find_duplicates()
