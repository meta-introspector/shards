#!/usr/bin/env python3
"""
Find files similar to STATELESS_ARCADE_ARCHITECTURE.md using Hecke resonance
With Monster group sharding: file mod 71, line mod 59, token mod 47
"""

import os
import hashlib
from pathlib import Path
from typing import List, Tuple, Dict
import json

# 15 Monster primes (Hecke operators)
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

# Crown primes for sharding
CROWN_PRIMES = [47, 59, 71]  # token, line, file

def hecke_hash(content: bytes, prime: int) -> int:
    """Apply Hecke operator (hash mod prime)"""
    h = hashlib.sha256(content).digest()
    return int.from_bytes(h[:8], 'big') % prime

def shard_file(file_path: Path) -> int:
    """Shard file by hash mod 71"""
    h = hashlib.sha256(str(file_path).encode()).digest()
    return int.from_bytes(h[:8], 'big') % 71

def shard_line(line: str, line_num: int) -> int:
    """Shard line by (line_num + hash) mod 59"""
    h = hashlib.sha256(line.encode()).digest()
    return (line_num + int.from_bytes(h[:8], 'big')) % 59

def shard_token(token: str) -> int:
    """Shard token by hash mod 47"""
    h = hashlib.sha256(token.encode()).digest()
    return int.from_bytes(h[:8], 'big') % 47

def hecke_signature_sharded(file_path: Path) -> Dict:
    """Compute 15-dimensional Hecke signature with sharding"""
    try:
        content = file_path.read_bytes()
        text = content.decode('utf-8', errors='ignore')
        lines = text.split('\n')
        
        # File-level signature (15 Hecke operators)
        file_sig = [hecke_hash(content, p) for p in MONSTER_PRIMES]
        
        # File shard (mod 71)
        file_shard = shard_file(file_path)
        
        # Line-level sharding (mod 59)
        line_shards = {}
        for i, line in enumerate(lines):
            if line.strip():
                ls = shard_line(line, i)
                if ls not in line_shards:
                    line_shards[ls] = []
                line_shards[ls].append(i)
        
        # Token-level sharding (mod 47)
        token_shards = {}
        tokens = text.split()
        for token in tokens:
            if len(token) > 2:  # Skip short tokens
                ts = shard_token(token)
                if ts not in token_shards:
                    token_shards[ts] = 0
                token_shards[ts] += 1
        
        return {
            'file_signature': file_sig,
            'file_shard': file_shard,
            'line_shards': line_shards,
            'token_shards': token_shards,
            'num_lines': len(lines),
            'num_tokens': len(tokens),
        }
    except Exception as e:
        return {
            'file_signature': [0] * 15,
            'file_shard': 0,
            'line_shards': {},
            'token_shards': {},
            'num_lines': 0,
            'num_tokens': 0,
        }

def hecke_resonance(sig1: List[int], sig2: List[int]) -> float:
    """Measure resonance between two Hecke signatures (0-1)"""
    matches = sum(1 for a, b in zip(sig1, sig2) if a == b)
    return matches / 15.0

def shard_overlap(shards1: Dict, shards2: Dict) -> float:
    """Measure overlap between shard distributions"""
    keys1 = set(shards1.keys())
    keys2 = set(shards2.keys())
    
    if not keys1 or not keys2:
        return 0.0
    
    intersection = keys1 & keys2
    union = keys1 | keys2
    
    return len(intersection) / len(union)

def compute_similarity(sig1: Dict, sig2: Dict) -> Dict[str, float]:
    """Compute multi-level similarity using Hecke resonance + sharding"""
    
    # File-level Hecke resonance
    file_resonance = hecke_resonance(sig1['file_signature'], sig2['file_signature'])
    
    # File shard match (same shard = 1.0, different = 0.0)
    file_shard_match = 1.0 if sig1['file_shard'] == sig2['file_shard'] else 0.0
    
    # Line shard overlap
    line_overlap = shard_overlap(sig1['line_shards'], sig2['line_shards'])
    
    # Token shard overlap
    token_overlap = shard_overlap(sig1['token_shards'], sig2['token_shards'])
    
    # Combined score (weighted)
    combined = (
        file_resonance * 0.4 +      # 40% file-level Hecke
        file_shard_match * 0.1 +     # 10% file shard
        line_overlap * 0.25 +        # 25% line shards
        token_overlap * 0.25         # 25% token shards
    )
    
    return {
        'file_resonance': file_resonance,
        'file_shard_match': file_shard_match,
        'line_overlap': line_overlap,
        'token_overlap': token_overlap,
        'combined': combined,
    }

def find_similar_files(target_file: str, threshold: float = 0.3) -> List[Tuple[str, Dict]]:
    """Find files similar to target using Hecke resonance + sharding"""
    
    target_path = Path(target_file)
    if not target_path.exists():
        print(f"❌ Target file not found: {target_file}")
        return []
    
    print(f"🔍 Computing Hecke signature for: {target_file}")
    target_sig = hecke_signature_sharded(target_path)
    print(f"   File signature: {target_sig['file_signature']}")
    print(f"   File shard: {target_sig['file_shard']}/71")
    print(f"   Line shards: {len(target_sig['line_shards'])}/59 used")
    print(f"   Token shards: {len(target_sig['token_shards'])}/47 used")
    print()
    
    # Find all markdown and text files
    print("📂 Scanning repository...")
    candidates = []
    
    for ext in ['*.md', '*.txt', '*.rs', '*.py', '*.sh', '*.json']:
        for f in Path('.').rglob(ext):
            if f.is_file() and f != target_path:
                # Skip large files and hidden dirs
                if f.stat().st_size > 1_000_000:
                    continue
                if any(part.startswith('.') for part in f.parts):
                    continue
                if 'target' in f.parts or 'node_modules' in f.parts:
                    continue
                
                candidates.append(f)
    
    print(f"   Found {len(candidates)} candidate files")
    print()
    
    # Compute similarities
    print("🎵 Computing Hecke resonance + sharding...")
    results = []
    
    for i, candidate in enumerate(candidates):
        if i % 100 == 0:
            print(f"   Progress: {i}/{len(candidates)}")
        
        cand_sig = hecke_signature_sharded(candidate)
        similarity = compute_similarity(target_sig, cand_sig)
        
        if similarity['combined'] >= threshold:
            results.append((str(candidate), similarity))
    
    # Sort by combined score
    results.sort(key=lambda x: x[1]['combined'], reverse=True)
    
    return results

def main():
    target = "STATELESS_ARCADE_ARCHITECTURE.md"
    
    print("🎮 HECKE RESONANCE + MONSTER SHARDING FILE FINDER")
    print("=" * 70)
    print()
    print(f"Target: {target}")
    print(f"Method: 15 Hecke operators + 3-level sharding")
    print(f"  • File shard: hash mod 71")
    print(f"  • Line shard: (line_num + hash) mod 59")
    print(f"  • Token shard: hash mod 47")
    print(f"Threshold: 0.3 (30% similarity)")
    print()
    print("=" * 70)
    print()
    
    results = find_similar_files(target, threshold=0.3)
    
    print()
    print("=" * 70)
    print(f"🏆 FOUND {len(results)} SIMILAR FILES")
    print("=" * 70)
    print()
    
    for i, (file_path, sim) in enumerate(results[:20], 1):
        print(f"{i}. {file_path}")
        print(f"   File resonance: {sim['file_resonance']:.3f} ({int(sim['file_resonance'] * 15)}/15 operators)")
        print(f"   File shard match: {sim['file_shard_match']:.3f}")
        print(f"   Line overlap: {sim['line_overlap']:.3f}")
        print(f"   Token overlap: {sim['token_overlap']:.3f}")
        print(f"   Combined score: {sim['combined']:.3f}")
        print()
    
    if len(results) > 20:
        print(f"... and {len(results) - 20} more files")
        print()
    
    # Save results
    with open("hecke_sharded_results.json", "w") as f:
        json.dump({
            'target': target,
            'method': 'Hecke resonance + Monster sharding (71/59/47)',
            'results': [
                {
                    'file': file_path,
                    'similarity': sim
                }
                for file_path, sim in results
            ]
        }, f, indent=2)
    
    print("💾 Results saved to: hecke_sharded_results.json")
    
    # Group by file shard
    print()
    print("=" * 70)
    print("📊 RESULTS BY FILE SHARD (mod 71)")
    print("=" * 70)
    print()
    
    # Re-compute target shard
    target_path = Path(target)
    target_shard = shard_file(target_path)
    print(f"Target file shard: {target_shard}/71")
    print()
    
    shard_groups = {}
    for file_path, sim in results[:50]:  # Top 50
        f = Path(file_path)
        fs = shard_file(f)
        if fs not in shard_groups:
            shard_groups[fs] = []
        shard_groups[fs].append((file_path, sim['combined']))
    
    for shard in sorted(shard_groups.keys()):
        files = shard_groups[shard]
        print(f"Shard {shard:2d}: {len(files)} files")
        for file_path, score in files[:3]:
            print(f"  • {file_path} ({score:.3f})")
        if len(files) > 3:
            print(f"  ... and {len(files) - 3} more")
        print()

if __name__ == "__main__":
    main()
