#!/usr/bin/env python3
"""
CICADA-71 Project Archaeology
Find all 10+ times we started implementing in Rust and Prolog
"""

import os
import json
from pathlib import Path
from typing import Dict, List, Tuple
from collections import defaultdict

def find_rust_projects() -> List[Dict]:
    """Find all Rust projects (Cargo.toml files)"""
    projects = []
    
    for cargo_file in Path('.').rglob('Cargo.toml'):
        try:
            with open(cargo_file, 'r') as f:
                content = f.read()
                
            # Extract package name
            name = None
            for line in content.split('\n'):
                if line.startswith('name ='):
                    name = line.split('=')[1].strip().strip('"')
                    break
            
            # Count Rust files
            project_dir = cargo_file.parent
            rust_files = list(project_dir.rglob('*.rs'))
            
            # Count lines
            total_lines = 0
            for rs_file in rust_files:
                try:
                    with open(rs_file, 'r') as f:
                        total_lines += len(f.readlines())
                except:
                    pass
            
            projects.append({
                'name': name or cargo_file.parent.name,
                'path': str(cargo_file.parent),
                'cargo_toml': str(cargo_file),
                'rust_files': len(rust_files),
                'lines': total_lines
            })
        except Exception as e:
            print(f"⚠️  Error reading {cargo_file}: {e}")
    
    return projects

def find_prolog_files() -> List[Dict]:
    """Find all Prolog files"""
    prolog_files = []
    
    for pl_file in Path('.').rglob('*.pl'):
        try:
            with open(pl_file, 'r') as f:
                lines = f.readlines()
            
            # Count predicates
            predicates = [l for l in lines if ':-' in l or l.strip().endswith('.')]
            
            prolog_files.append({
                'name': pl_file.name,
                'path': str(pl_file),
                'lines': len(lines),
                'predicates': len(predicates)
            })
        except Exception as e:
            print(f"⚠️  Error reading {pl_file}: {e}")
    
    return prolog_files

def categorize_projects(projects: List[Dict]) -> Dict[str, List[Dict]]:
    """Categorize projects by purpose"""
    categories = defaultdict(list)
    
    for proj in projects:
        name = proj['name'].lower()
        path = proj['path'].lower()
        
        if 'agent' in name or 'agent' in path:
            categories['AI Agents'].append(proj)
        elif 'paxos' in name or 'paxos' in path:
            categories['Consensus'].append(proj)
        elif 'plugin' in name or 'plugin' in path:
            categories['Plugins'].append(proj)
        elif 'wasm' in name or 'wasm' in path:
            categories['WASM'].append(proj)
        elif 'harbor' in name or 'harbor' in path:
            categories['P2P/Harbor'].append(proj)
        elif 'shard' in path:
            categories['Shards'].append(proj)
        else:
            categories['Other'].append(proj)
    
    return dict(categories)

def main():
    print("🔍 CICADA-71 Project Archaeology")
    print("=" * 60)
    print("Finding all Rust and Prolog implementations...")
    print()
    
    # Find Rust projects
    rust_projects = find_rust_projects()
    print(f"📦 Found {len(rust_projects)} Rust projects")
    
    # Find Prolog files
    prolog_files = find_prolog_files()
    print(f"🧠 Found {len(prolog_files)} Prolog files")
    print()
    
    # Categorize
    categories = categorize_projects(rust_projects)
    
    # Display by category
    print("📊 Rust Projects by Category:")
    print("=" * 60)
    
    for category, projects in sorted(categories.items()):
        print(f"\n{category} ({len(projects)} projects):")
        for proj in sorted(projects, key=lambda x: x['lines'], reverse=True):
            print(f"  • {proj['name']}")
            print(f"    Path: {proj['path']}")
            print(f"    Files: {proj['rust_files']}, Lines: {proj['lines']:,}")
    
    # Prolog files
    if prolog_files:
        print(f"\n🧠 Prolog Files ({len(prolog_files)}):")
        print("=" * 60)
        for pl in prolog_files:
            print(f"  • {pl['name']}")
            print(f"    Path: {pl['path']}")
            print(f"    Lines: {pl['lines']}, Predicates: {pl['predicates']}")
    
    # Statistics
    total_rust_files = sum(p['rust_files'] for p in rust_projects)
    total_rust_lines = sum(p['lines'] for p in rust_projects)
    total_prolog_lines = sum(p['lines'] for p in prolog_files)
    
    print()
    print("📈 Summary Statistics:")
    print("=" * 60)
    print(f"Total Rust projects: {len(rust_projects)}")
    print(f"Total Rust files: {total_rust_files:,}")
    print(f"Total Rust LOC: {total_rust_lines:,}")
    print(f"Total Prolog files: {len(prolog_files)}")
    print(f"Total Prolog LOC: {total_prolog_lines:,}")
    print(f"Combined LOC: {total_rust_lines + total_prolog_lines:,}")
    
    # Save results
    results = {
        'rust_projects': rust_projects,
        'prolog_files': prolog_files,
        'categories': {k: [p['name'] for p in v] for k, v in categories.items()},
        'statistics': {
            'rust_projects': len(rust_projects),
            'rust_files': total_rust_files,
            'rust_loc': total_rust_lines,
            'prolog_files': len(prolog_files),
            'prolog_loc': total_prolog_lines,
            'total_loc': total_rust_lines + total_prolog_lines
        }
    }
    
    with open('project_archaeology.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print()
    print("💾 Saved to project_archaeology.json")
    
    # Highlight the "10 times we started"
    print()
    print("🎯 The 10+ Times We Started:")
    print("=" * 60)
    
    starts = [
        ("agents/evaluate", "AI agent evaluation framework"),
        ("agents/leaderboard", "Paxos market leaderboard"),
        ("agents/paxos-node", "Paxos consensus node"),
        ("agents/invite-generator", "Framework invite generator"),
        ("wasm-bbs", "Browser-based Paxos BBS"),
        ("zos-server/plugins/j-invariant", "j-invariant Hecke-Maass plugin"),
        ("shard58/harbor", "P2P social network (Harbor)"),
        ("shard58/harbot", "Harbor bot library"),
        ("zos-server/src/plugin_tape", "Plugin tape system"),
        ("proofs/planetary_song.pl", "Planetary song Prolog proof"),
    ]
    
    for i, (path, desc) in enumerate(starts, 1):
        matching = [p for p in rust_projects if path in p['path']]
        if matching:
            proj = matching[0]
            print(f"{i:2d}. {desc}")
            print(f"    {proj['name']} - {proj['rust_files']} files, {proj['lines']:,} LOC")
        else:
            # Check Prolog
            matching_pl = [p for p in prolog_files if path in p['path']]
            if matching_pl:
                pl = matching_pl[0]
                print(f"{i:2d}. {desc}")
                print(f"    {pl['name']} - {pl['lines']} lines")

if __name__ == "__main__":
    main()
