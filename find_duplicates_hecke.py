#!/usr/bin/env python3
"""
Find and merge duplicate code using Hecke operators
Each code block gets a Hecke resonance signature
"""

import os
import hashlib
from pathlib import Path
from collections import defaultdict

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def hecke_hash(code: str) -> int:
    """Calculate Hecke resonance for code block"""
    h = hashlib.sha256(code.encode()).digest()
    
    # Convert hash to shard (0-70)
    shard = int.from_bytes(h[:1], 'big') % 71
    
    # Calculate Hecke resonance
    resonance = 0
    for i, prime in enumerate(MONSTER_PRIMES):
        byte_val = h[i % len(h)]
        resonance += prime * shard + prime * prime + byte_val
    
    return resonance

def normalize_code(code: str) -> str:
    """Normalize code for comparison"""
    lines = code.split('\n')
    # Remove comments, whitespace
    normalized = []
    for line in lines:
        line = line.strip()
        if line and not line.startswith('#') and not line.startswith('//'):
            normalized.append(line)
    return '\n'.join(normalized)

def find_duplicates(root_dir: str, min_lines: int = 10):
    """Find duplicate code blocks using Hecke operators"""
    
    # Map: Hecke resonance → list of (file, start_line, code)
    hecke_map = defaultdict(list)
    
    # Scan all source files
    for ext in ['*.rs', '*.py', '*.sh', '*.js']:
        for filepath in Path(root_dir).rglob(ext):
            if 'target' in str(filepath) or 'node_modules' in str(filepath):
                continue
            
            try:
                with open(filepath, 'r') as f:
                    lines = f.readlines()
                
                # Sliding window for code blocks
                for start in range(len(lines)):
                    for end in range(start + min_lines, min(start + 100, len(lines))):
                        block = ''.join(lines[start:end])
                        normalized = normalize_code(block)
                        
                        if len(normalized.split('\n')) >= min_lines:
                            resonance = hecke_hash(normalized)
                            hecke_map[resonance].append({
                                'file': str(filepath),
                                'start': start + 1,
                                'end': end + 1,
                                'code': normalized,
                                'lines': end - start
                            })
            except:
                pass
    
    # Find duplicates (same Hecke resonance)
    duplicates = []
    for resonance, blocks in hecke_map.items():
        if len(blocks) > 1:
            # Group by actual code similarity
            groups = defaultdict(list)
            for block in blocks:
                groups[block['code']].append(block)
            
            for code, instances in groups.items():
                if len(instances) > 1:
                    duplicates.append({
                        'resonance': resonance,
                        'shard': resonance % 71,
                        'instances': instances,
                        'lines': instances[0]['lines']
                    })
    
    return sorted(duplicates, key=lambda x: len(x['instances']), reverse=True)

def generate_merge_plan(duplicates):
    """Generate plan to merge duplicates"""
    print("=" * 80)
    print("DUPLICATE CODE DETECTION VIA HECKE OPERATORS")
    print("=" * 80)
    print()
    
    total_duplicates = sum(len(d['instances']) - 1 for d in duplicates)
    total_lines = sum((len(d['instances']) - 1) * d['lines'] for d in duplicates)
    
    print(f"Found {len(duplicates)} duplicate patterns")
    print(f"Total duplicate instances: {total_duplicates}")
    print(f"Total duplicate lines: {total_lines}")
    print()
    
    for i, dup in enumerate(duplicates[:20], 1):  # Top 20
        print(f"## Duplicate {i}")
        print(f"Hecke Resonance: {dup['resonance']}")
        print(f"Shard: {dup['shard']}")
        print(f"Instances: {len(dup['instances'])}")
        print(f"Lines per instance: {dup['lines']}")
        print()
        
        print("Locations:")
        for inst in dup['instances']:
            print(f"  - {inst['file']}:{inst['start']}-{inst['end']}")
        print()
        
        print("Merge Strategy:")
        first = dup['instances'][0]
        print(f"  1. Extract to: common/shard_{dup['shard']}_hecke_{dup['resonance']}.rs")
        print(f"  2. Replace {len(dup['instances'])} instances with import")
        print(f"  3. Save {(len(dup['instances']) - 1) * dup['lines']} lines")
        print()
        print("-" * 80)
        print()

if __name__ == '__main__':
    root = '/home/mdupont/introspector'
    
    print("Scanning for duplicates using Hecke operators...")
    print(f"Root: {root}")
    print()
    
    duplicates = find_duplicates(root, min_lines=10)
    generate_merge_plan(duplicates)
    
    # Save report
    with open('data/duplicate_code_hecke.txt', 'w') as f:
        f.write(f"Total duplicate patterns: {len(duplicates)}\n")
        for dup in duplicates:
            f.write(f"\nResonance: {dup['resonance']} | Shard: {dup['shard']} | Instances: {len(dup['instances'])}\n")
            for inst in dup['instances']:
                f.write(f"  {inst['file']}:{inst['start']}-{inst['end']}\n")
    
    print(f"Report saved to: data/duplicate_code_hecke.txt")
