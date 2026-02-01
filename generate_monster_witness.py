#!/usr/bin/env python3
"""
Monster Harmonic zkSNARK Witness Generator
Generates witness from zkML data for Circom circuit
"""

import json
import hashlib
import sys
from pathlib import Path

# 71 Monster primes
MONSTER_PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353
]

def hash_to_field(data: bytes) -> int:
    """Convert hash to field element"""
    h = hashlib.sha256(data).digest()
    return int.from_bytes(h, 'big') % (2**254 - 1)  # BN254 scalar field

def generate_witness(zkwitness_path: str) -> dict:
    """Generate Circom witness from zkML witness"""
    
    # Load zkML witness
    with open(zkwitness_path) as f:
        witness = json.load(f)
    
    shard_id = witness['shard_id']
    
    # Load perf and ollama data
    shard_dir = Path(zkwitness_path).parent
    perf_path = shard_dir / f"zkperf-{shard_id}.data"
    ollama_path = shard_dir / f"ollama-{shard_id}.log"
    
    # Read data
    perf_data = perf_path.read_bytes() if perf_path.exists() else b""
    ollama_data = ollama_path.read_bytes() if ollama_path.exists() else b""
    
    # Compute hashes as field elements
    perf_hash = hash_to_field(perf_data)
    ollama_hash = hash_to_field(ollama_data)
    
    # Generate witness
    circom_witness = {
        "perf_hash": str(perf_hash),
        "ollama_hash": str(ollama_hash),
        "shard_id": str(shard_id),
        "primes": [str(p) for p in MONSTER_PRIMES]
    }
    
    return circom_witness

def main():
    if len(sys.argv) < 2:
        print("Usage: generate_monster_witness.py <zkwitness.json>")
        sys.exit(1)
    
    zkwitness_path = sys.argv[1]
    witness = generate_witness(zkwitness_path)
    
    # Output witness
    output_path = Path(zkwitness_path).parent / "monster_witness.json"
    with open(output_path, 'w') as f:
        json.dump(witness, f, indent=2)
    
    print(f"✅ Generated Monster Harmonic witness: {output_path}")
    print(f"   Shard: {witness['shard_id']}")
    print(f"   Perf hash: {witness['perf_hash'][:20]}...")
    print(f"   Ollama hash: {witness['ollama_hash'][:20]}...")
    print(f"   Primes: {len(witness['primes'])}")

if __name__ == "__main__":
    main()
