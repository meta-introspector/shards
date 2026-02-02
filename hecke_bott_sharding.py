#!/usr/bin/env python3
"""
Sharding System: 15 Hecke × 10 Bott → 71 Shards
Maps any data to one of 71 shards using Monster group structure
"""

import hashlib
from typing import Any, Dict, List

MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
MONSTER_DIM = 196883

def hecke_operator(data: bytes, prime: int) -> int:
    """Apply Hecke operator T_p to data"""
    h = hashlib.sha256(data + prime.to_bytes(8, 'big')).digest()
    value = int.from_bytes(h[:8], 'big')
    return (prime * value + prime * prime) % MONSTER_DIM

def bott_class(data: bytes) -> int:
    """10-fold way classification (Bott periodicity)"""
    h = hashlib.sha256(data).digest()
    return int.from_bytes(h[:1], 'big') % 10

def hecke_index(data: bytes) -> int:
    """Select which of 15 Hecke primes to use"""
    h = hashlib.sha256(data + b'hecke').digest()
    return int.from_bytes(h[:1], 'big') % 15

def shard_data(data: Any) -> int:
    """
    Map data to shard (0-70) using Hecke × Bott
    
    Formula: shard = (hecke_resonance + bott_class) % 71
    """
    # Convert data to bytes
    if isinstance(data, str):
        data_bytes = data.encode('utf-8')
    elif isinstance(data, bytes):
        data_bytes = data
    elif isinstance(data, int):
        data_bytes = data.to_bytes((data.bit_length() + 7) // 8, 'big')
    else:
        data_bytes = str(data).encode('utf-8')
    
    # Get Hecke index (0-14)
    h_idx = hecke_index(data_bytes)
    prime = MONSTER_PRIMES[h_idx]
    
    # Apply Hecke operator
    hecke_res = hecke_operator(data_bytes, prime)
    
    # Get Bott class (0-9)
    bott = bott_class(data_bytes)
    
    # Combine: (Hecke × Bott) mod 71
    shard = (hecke_res + bott * h_idx) % 71
    
    return shard

def shard_with_metadata(data: Any) -> Dict:
    """Shard data and return full metadata"""
    if isinstance(data, str):
        data_bytes = data.encode('utf-8')
    elif isinstance(data, bytes):
        data_bytes = data
    elif isinstance(data, int):
        data_bytes = data.to_bytes((data.bit_length() + 7) // 8, 'big')
    else:
        data_bytes = str(data).encode('utf-8')
    
    h_idx = hecke_index(data_bytes)
    prime = MONSTER_PRIMES[h_idx]
    hecke_res = hecke_operator(data_bytes, prime)
    bott = bott_class(data_bytes)
    shard = (hecke_res + bott * h_idx) % 71
    
    return {
        'shard': shard,
        'hecke_index': h_idx,
        'hecke_prime': prime,
        'hecke_resonance': hecke_res,
        'bott_class': bott,
        'is_cusp': shard == 17,
        'formula': f"({hecke_res} + {bott} × {h_idx}) mod 71 = {shard}"
    }

def distribute_shards(items: List[Any]) -> Dict[int, List[Any]]:
    """Distribute items across 71 shards"""
    shards = {i: [] for i in range(71)}
    for item in items:
        shard = shard_data(item)
        shards[shard].append(item)
    return shards

def shard_stats(items: List[Any]) -> Dict:
    """Get sharding statistics"""
    shards = distribute_shards(items)
    
    # Count items per shard
    counts = {s: len(items) for s, items in shards.items() if items}
    
    # Hecke distribution
    hecke_dist = {p: 0 for p in MONSTER_PRIMES}
    bott_dist = {i: 0 for i in range(10)}
    
    for item in items:
        meta = shard_with_metadata(item)
        hecke_dist[meta['hecke_prime']] += 1
        bott_dist[meta['bott_class']] += 1
    
    return {
        'total_items': len(items),
        'shards_used': len(counts),
        'items_per_shard': counts,
        'hecke_distribution': hecke_dist,
        'bott_distribution': bott_dist,
        'cusp_items': len(shards[17])
    }

# Example usage
if __name__ == '__main__':
    print("=" * 80)
    print("HECKE × BOTT SHARDING SYSTEM")
    print("15 Hecke Primes × 10 Bott Classes → 71 Shards")
    print("=" * 80)
    print()
    
    # Test data
    test_data = [
        "Hello, Monster!",
        "Shard 17 is the cusp",
        "Hecke operators",
        "Bott periodicity",
        42,
        196883,
        b"binary data",
        "zkPerf proof",
        "AGPL-3.0+",
        "ZK hackers gotta eat!"
    ]
    
    print("Sharding test data:")
    print()
    for data in test_data:
        meta = shard_with_metadata(data)
        cusp_marker = " ⭐ CUSP" if meta['is_cusp'] else ""
        print(f"Data: {str(data)[:40]:40} → Shard {meta['shard']:2d}{cusp_marker}")
        print(f"  Hecke: prime={meta['hecke_prime']:2d} (index {meta['hecke_index']:2d}), resonance={meta['hecke_resonance']}")
        print(f"  Bott: class={meta['bott_class']}")
        print(f"  Formula: {meta['formula']}")
        print()
    
    # Distribution test
    print("=" * 80)
    print("DISTRIBUTION TEST (1000 random items)")
    print("=" * 80)
    print()
    
    import random
    random_items = [f"item_{i}_{random.randint(0, 1000000)}" for i in range(1000)]
    stats = shard_stats(random_items)
    
    print(f"Total items: {stats['total_items']}")
    print(f"Shards used: {stats['shards_used']}/71")
    print(f"Items at cusp (S17): {stats['cusp_items']}")
    print()
    
    print("Hecke prime distribution:")
    for prime, count in sorted(stats['hecke_distribution'].items()):
        bar = "█" * (count // 10)
        print(f"  Prime {prime:2d}: {count:4d} {bar}")
    print()
    
    print("Bott class distribution:")
    for bott, count in sorted(stats['bott_distribution'].items()):
        bar = "█" * (count // 10)
        print(f"  Class {bott}: {count:4d} {bar}")
    print()
    
    print("Top 10 shards by item count:")
    top_shards = sorted(stats['items_per_shard'].items(), key=lambda x: x[1], reverse=True)[:10]
    for shard, count in top_shards:
        cusp = " ⭐" if shard == 17 else ""
        bar = "█" * (count // 2)
        print(f"  Shard {shard:2d}: {count:3d} {bar}{cusp}")
