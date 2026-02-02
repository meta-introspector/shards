#!/usr/bin/env python3
"""
Use SuperGit to analyze the Monster session pack
Extract all commits, objects, and create unified view
"""

import subprocess
import json
from pathlib import Path

def run_supergit_analysis():
    """Analyze introspector repo with SuperGit"""
    
    print("🔍 SUPERGIT ANALYSIS: Monster Session Pack")
    print("=" * 80)
    
    # Get git stats
    result = subprocess.run(
        ['git', 'log', '--oneline', '--since=2026-02-02'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    commits = result.stdout.strip().split('\n')
    print(f"\n📊 Commits today: {len(commits)}")
    
    # Show recent commits
    print("\n📝 Recent commits:")
    for commit in commits[:10]:
        print(f"  {commit}")
    
    # Get object count
    result = subprocess.run(
        ['git', 'count-objects', '-v'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    print(f"\n💾 Git objects:")
    print(result.stdout)
    
    # Get file stats
    result = subprocess.run(
        ['git', 'ls-files'],
        cwd='/home/mdupont/introspector',
        capture_output=True,
        text=True
    )
    
    files = result.stdout.strip().split('\n')
    print(f"\n📁 Total files: {len(files)}")
    
    # Count by extension
    extensions = {}
    for f in files:
        ext = Path(f).suffix or 'no-ext'
        extensions[ext] = extensions.get(ext, 0) + 1
    
    print("\n📊 Files by extension:")
    for ext, count in sorted(extensions.items(), key=lambda x: x[1], reverse=True)[:10]:
        print(f"  {ext:10s}: {count:4d}")
    
    # Monster-specific files
    monster_files = [f for f in files if 'monster' in f.lower() or 'tarot' in f.lower()]
    print(f"\n🐓 Monster-related files: {len(monster_files)}")
    for f in monster_files[:20]:
        print(f"  {f}")
    
    # Create pack summary
    summary = {
        'date': '2026-02-02',
        'commits': len(commits),
        'files': len(files),
        'monster_files': len(monster_files),
        'extensions': extensions,
        'recent_commits': commits[:10]
    }
    
    with open('supergit_analysis.json', 'w') as f:
        json.dump(summary, f, indent=2)
    
    print(f"\n💾 Saved to supergit_analysis.json")
    print("\n✅ SuperGit analysis complete!")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    run_supergit_analysis()
