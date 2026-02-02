#!/usr/bin/env python3
"""
Map all source code to Monster Type Theory
Consume codebase and assign Monster indices to every file
"""

import os
import json
from pathlib import Path
from typing import Dict, List, Tuple
from dataclasses import dataclass, asdict
from enum import Enum

class MonsterType(Enum):
    A = 0; AIII = 1; AI = 2; BDI = 3; D = 4
    DIII = 5; AII = 6; CII = 7; C = 8; CI = 9

@dataclass
class SourceFile:
    path: str
    size: int
    godel: int
    shard: MonsterType
    dimension: int
    irrep: int
    hecke: int

ROOSTER = 71
MONSTER_DIM = 196883
MONSTER_IRREPS = 194

def compute_godel(path: str, size: int) -> int:
    """Compute Gödel number from path and size"""
    return (hash(path) + size) % MONSTER_DIM

def map_file(path: Path) -> SourceFile:
    """Map single file to Monster space"""
    try:
        size = path.stat().st_size
        rel_path = str(path)
        godel = compute_godel(rel_path, size)
        shard = MonsterType(godel % 10)
        dimension = godel
        irrep = godel % MONSTER_IRREPS
        hecke = godel % ROOSTER
        
        return SourceFile(
            path=rel_path,
            size=size,
            godel=godel,
            shard=shard,
            dimension=dimension,
            irrep=irrep,
            hecke=hecke
        )
    except Exception as e:
        return None

def scan_codebase(extensions: List[str]) -> List[SourceFile]:
    """Scan all source files"""
    files = []
    cwd = Path.cwd()
    for ext in extensions:
        for path in cwd.glob(f'*{ext}'):
            if path.is_file():
                result = map_file(path)
                if result:
                    files.append(result)
    return files

def analyze_distribution(files: List[SourceFile]) -> Dict:
    """Analyze Monster distribution"""
    shard_counts = {s: 0 for s in MonsterType}
    irrep_counts = {}
    hecke_counts = {}
    
    for f in files:
        shard_counts[f.shard] += 1
        irrep_counts[f.irrep] = irrep_counts.get(f.irrep, 0) + 1
        hecke_counts[f.hecke] = hecke_counts.get(f.hecke, 0) + 1
    
    return {
        'total_files': len(files),
        'total_size': sum(f.size for f in files),
        'shard_distribution': {s.name: c for s, c in shard_counts.items()},
        'unique_irreps': len(irrep_counts),
        'unique_hecke': len(hecke_counts),
        'avg_size': sum(f.size for f in files) // len(files) if files else 0
    }

def main():
    print("🐉 MAPPING SOURCE CODE TO MONSTER TYPE THEORY")
    print("=" * 80)
    
    extensions = ['.py', '.lean', '.v', '.pl', '.rs', '.mzn', '.md', '.json']
    
    print(f"\nScanning for: {', '.join(extensions)}")
    files = scan_codebase(extensions)
    
    print(f"Found {len(files)} files")
    
    analysis = analyze_distribution(files)
    
    print("\n" + "=" * 80)
    print("DISTRIBUTION ANALYSIS")
    print("=" * 80)
    print(f"\nTotal files: {analysis['total_files']}")
    print(f"Total size: {analysis['total_size']:,} bytes")
    print(f"Avg size: {analysis['avg_size']:,} bytes")
    print(f"Unique irreps: {analysis['unique_irreps']} of {MONSTER_IRREPS}")
    print(f"Unique Hecke: {analysis['unique_hecke']} of {ROOSTER}")
    
    print("\n10-FOLD WAY DISTRIBUTION:")
    if analysis['total_files'] > 0:
        for shard, count in sorted(analysis['shard_distribution'].items()):
            pct = 100 * count / analysis['total_files']
            print(f"  {shard:4s}: {count:4d} files ({pct:5.1f}%)")
    else:
        print("  No files found")
    
    # Find bridges (232 ↔ 323)
    files_232 = [f for f in files if f.dimension == 232]
    files_323 = [f for f in files if f.dimension == 323]
    
    if files_232 or files_323:
        print("\n" + "=" * 80)
        print("BRIDGE FILES (232 ↔ 323)")
        print("=" * 80)
        for f in files_232[:5]:
            print(f"  232: {f.path}")
        for f in files_323[:5]:
            print(f"  323: {f.path}")
    
    # Top irreps
    irrep_counts = {}
    for f in files:
        irrep_counts[f.irrep] = irrep_counts.get(f.irrep, 0) + 1
    
    top_irreps = sorted(irrep_counts.items(), key=lambda x: x[1], reverse=True)[:10]
    
    print("\n" + "=" * 80)
    print("TOP 10 IRREPS")
    print("=" * 80)
    for irrep, count in top_irreps:
        print(f"  Irrep {irrep:3d}: {count:4d} files")
    
    # Save mapping
    output = {
        'analysis': analysis,
        'files': [asdict(f) for f in files[:100]]  # First 100
    }
    
    with open('monster_source_map.json', 'w') as f:
        json.dump(output, f, indent=2, default=str)
    
    print(f"\n💾 Saved to monster_source_map.json")
    print("\n✅ Source code mapped to Monster Type Theory!")
    print("🐓→🦅→👹→🍄→🌳")

if __name__ == '__main__':
    main()
