#!/usr/bin/env python3
"""
Convert 7,920 Brainfuck tapes to Monster Harmonic
T₂ (Hecke operator for prime 2) - First sample
"""

import hashlib
import json
from pathlib import Path

# T₂ = Hecke operator for prime 2 (first prime)
T_2 = 2

def compute_monster_harmonic(bf_code: str, index: int) -> dict:
    """Compute Monster harmonic for brainfuck tape"""
    
    # Hash the code
    code_hash = hashlib.sha256(bf_code.encode()).hexdigest()
    
    # Shard assignment (mod 71)
    shard = index % 71
    
    # T₂ eigenvalue (Hecke operator for prime 2)
    t2_eigenvalue = (int(code_hash[:16], 16) % T_2) / T_2
    
    # Monster harmonic components
    harmonic = {
        "index": index,
        "shard": shard,
        "hecke_operator": f"T_{T_2}",
        "eigenvalue": t2_eigenvalue,
        "hash": code_hash,
        "length": len(bf_code),
        "mock_form": bf_code[:100],  # First 100 chars (mock)
        "shadow": code_hash[:32],     # Hash prefix (shadow)
    }
    
    return harmonic

def sample_t2_conversion():
    """Sample T₂ conversion on first 2 files"""
    
    print("🔮⚡ Monster Harmonic Conversion - T₂ Sample")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"Hecke Operator: T_{T_2} (prime 2)")
    print()
    
    # Read file list
    with open('.tmp-brainfuck-locate2.txt', 'r') as f:
        files = [line.strip() for line in f.readlines()]
    
    print(f"Total files: {len(files)}")
    print(f"Sampling: First {T_2} files (T₂)")
    print()
    
    harmonics = []
    
    for i in range(min(T_2, len(files))):
        filepath = files[i]
        
        try:
            with open(filepath, 'rb') as f:
                bf_code = f.read().decode('utf-8', errors='ignore')
        except:
            bf_code = f"# File {i}: {filepath}"
        
        harmonic = compute_monster_harmonic(bf_code, i)
        harmonics.append(harmonic)
        
        print(f"File {i}: {Path(filepath).name}")
        print(f"  Shard: {harmonic['shard']}")
        print(f"  T₂ Eigenvalue: {harmonic['eigenvalue']:.6f}")
        print(f"  Hash: {harmonic['hash'][:16]}...")
        print(f"  Length: {harmonic['length']} bytes")
        print()
    
    # Save T₂ sample
    output = {
        "hecke_operator": f"T_{T_2}",
        "prime": T_2,
        "sample_size": len(harmonics),
        "total_files": len(files),
        "harmonics": harmonics
    }
    
    with open('monster_harmonic_t2_sample.json', 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"✅ Saved T₂ sample to monster_harmonic_t2_sample.json")
    print()
    print("Next steps:")
    print("  T₃ (prime 3): Sample 3 files")
    print("  T₅ (prime 5): Sample 5 files")
    print("  ...")
    print("  T₇₁ (prime 71): Sample 71 files")
    print()
    print(f"Total harmonics: {len(files)} files → 71 shards")

if __name__ == "__main__":
    sample_t2_conversion()
