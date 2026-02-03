#!/usr/bin/env python3
"""
Find files similar to STATELESS_ARCADE_ARCHITECTURE.md using Hecke resonance
Uses 15 Hecke operators (Monster primes) to measure similarity
"""

import os
import hashlib
from pathlib import Path
from typing import List, Tuple

# 15 Monster primes (Hecke operators)
MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def hecke_hash(content: bytes, prime: int) -> int:
    """Apply Hecke operator (hash mod prime)"""
    h = hashlib.sha256(content).digest()
    return int.from_bytes(h[:8], 'big') % prime

def hecke_signature(file_path: Path) -> List[int]:
    """Compute 15-dimensional Hecke signature"""
    try:
        content = file_path.read_bytes()
        return [hecke_hash(content, p) for p in MONSTER_PRIMES]
    except:
        return [0] * 15

def hecke_resonance(sig1: List[int], sig2: List[int]) -> float:
    """Measure resonance between two Hecke signatures (0-1)"""
    matches = sum(1 for a, b in zip(sig1, sig2) if a == b)
    return matches / 15.0

def cosine_similarity(sig1: List[int], sig2: List[int]) -> float:
    """Cosine similarity of Hecke signatures"""
    import math
    
    dot = sum(a * b for a, b in zip(sig1, sig2))
    mag1 = math.sqrt(sum(a * a for a in sig1))
    mag2 = math.sqrt(sum(b * b for b in sig2))
    
    if mag1 == 0 or mag2 == 0:
        return 0.0
    
    return dot / (mag1 * mag2)

def find_similar_files(target_file: str, threshold: float = 0.3) -> List[Tuple[str, float, float]]:
    """Find files similar to target using Hecke resonance"""
    
    target_path = Path(target_file)
    if not target_path.exists():
        print(f"❌ Target file not found: {target_file}")
        return []
    
    print(f"🔍 Computing Hecke signature for: {target_file}")
    target_sig = hecke_signature(target_path)
    print(f"   Signature: {target_sig}")
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
    print("🎵 Computing Hecke resonance...")
    results = []
    
    for i, candidate in enumerate(candidates):
        if i % 100 == 0:
            print(f"   Progress: {i}/{len(candidates)}")
        
        cand_sig = hecke_signature(candidate)
        resonance = hecke_resonance(target_sig, cand_sig)
        cosine = cosine_similarity(target_sig, cand_sig)
        
        # Combined score
        score = (resonance + cosine) / 2.0
        
        if score >= threshold:
            results.append((str(candidate), resonance, cosine))
    
    # Sort by combined score
    results.sort(key=lambda x: (x[1] + x[2]) / 2.0, reverse=True)
    
    return results

def main():
    target = "STATELESS_ARCADE_ARCHITECTURE.md"
    
    print("🎮 HECKE RESONANCE FILE FINDER")
    print("=" * 70)
    print()
    print(f"Target: {target}")
    print(f"Method: 15 Hecke operators (Monster primes)")
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
    
    for i, (file_path, resonance, cosine) in enumerate(results[:20], 1):
        combined = (resonance + cosine) / 2.0
        print(f"{i}. {file_path}")
        print(f"   Hecke resonance: {resonance:.3f} ({int(resonance * 15)}/15 operators match)")
        print(f"   Cosine similarity: {cosine:.3f}")
        print(f"   Combined score: {combined:.3f}")
        print()
    
    if len(results) > 20:
        print(f"... and {len(results) - 20} more files")
        print()
    
    # Save results
    with open("hecke_resonance_results.txt", "w") as f:
        f.write(f"Hecke Resonance Results for: {target}\n")
        f.write("=" * 70 + "\n\n")
        
        for file_path, resonance, cosine in results:
            combined = (resonance + cosine) / 2.0
            f.write(f"{file_path}\n")
            f.write(f"  Resonance: {resonance:.3f}\n")
            f.write(f"  Cosine: {cosine:.3f}\n")
            f.write(f"  Combined: {combined:.3f}\n\n")
    
    print("💾 Results saved to: hecke_resonance_results.txt")

if __name__ == "__main__":
    main()
