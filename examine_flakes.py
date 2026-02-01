#!/usr/bin/env python3
"""
Examine and document all Nix flakes in introspector
"""

import json
import subprocess
from pathlib import Path
from collections import defaultdict

def analyze_flake(flake_path):
    """Analyze a single flake"""
    try:
        # Get flake metadata
        result = subprocess.run(
            ['nix', 'flake', 'metadata', '--json', str(flake_path.parent)],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        if result.returncode == 0:
            metadata = json.loads(result.stdout)
            return {
                'path': str(flake_path),
                'status': 'valid',
                'metadata': metadata
            }
        else:
            return {
                'path': str(flake_path),
                'status': 'error',
                'error': result.stderr
            }
    except Exception as e:
        return {
            'path': str(flake_path),
            'status': 'exception',
            'error': str(e)
        }

def categorize_flakes():
    """Categorize all flakes"""
    
    print("🔮⚡ Examining All Nix Flakes")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print()
    
    # Read flake list
    with open('/tmp/all_flakes.txt', 'r') as f:
        flakes = [Path(line.strip()) for line in f]
    
    print(f"Total flakes: {len(flakes)}")
    print()
    
    # Categorize by directory
    categories = defaultdict(list)
    
    for flake in flakes:
        parts = flake.parts
        
        if 'shard-' in str(flake):
            # Extract shard number
            for part in parts:
                if part.startswith('shard-'):
                    shard_num = part.split('-')[1]
                    categories[f'Shard {shard_num}'].append(flake)
                    break
        elif 'emoji-wasm' in str(flake):
            categories['Emoji WASM'].append(flake)
        elif 'moltboot' in str(flake):
            categories['Moltboot'].append(flake)
        elif 'lobster' in str(flake):
            categories['Lobster'].append(flake)
        elif 'bbs-8080' in str(flake):
            categories['BBS 8080'].append(flake)
        elif 'battle-royale' in str(flake):
            categories['Battle Royale'].append(flake)
        elif 'gemini' in str(flake):
            categories['Gemini'].append(flake)
        elif 'lmfdb' in str(flake):
            categories['LMFDB'].append(flake)
        else:
            categories['Other'].append(flake)
    
    # Print summary
    print("📊 Flake Categories:")
    print()
    
    for category in sorted(categories.keys()):
        count = len(categories[category])
        print(f"  {category}: {count} flake(s)")
    
    print()
    
    # Save categorization
    output = {
        'total': len(flakes),
        'categories': {
            cat: [str(f) for f in flakes]
            for cat, flakes in categories.items()
        }
    }
    
    with open('flake_inventory.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print("💾 Saved to flake_inventory.json")
    print()
    
    # Show sample from each category
    print("📋 Sample Flakes:")
    print()
    
    for category in sorted(categories.keys())[:10]:
        flakes_in_cat = categories[category]
        sample = flakes_in_cat[0]
        print(f"  {category}:")
        print(f"    {sample}")
        print()
    
    return categories

if __name__ == "__main__":
    categories = categorize_flakes()
