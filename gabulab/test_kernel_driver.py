#!/usr/bin/env python3
"""
Test Monster Kernel Driver
Simulate HDD sampling without loading kernel module
"""

import struct
import hashlib

# Monster constants
MONSTER_SHARDS = 71
HEX_WALK = 0x1F90
WALK_NIBBLES = [0x1, 0xF, 0x9, 0x0]
TRIPLES_PER_SHARD = 49109639

def sector_to_shard(sector):
    """Map sector to shard using hex walk"""
    hash_val = sector * HEX_WALK
    return hash_val % MONSTER_SHARDS

def sample_sector(data, shard_id):
    """Sample sector data with Monster walk"""
    nibble = WALK_NIBBLES[shard_id % 4]
    sample = 0
    
    for i, byte in enumerate(data[:512]):
        sample ^= (byte ^ nibble) << ((i % 4) * 8)
    
    return sample & 0xFFFFFFFF

def simulate_hdd_sampling(num_sectors=1000):
    """Simulate HDD sampling"""
    
    print("🔮⚡ SIMULATING MONSTER HDD SAMPLER")
    print("=" * 70)
    print()
    print(f"Sectors: {num_sectors}")
    print(f"Shards: {MONSTER_SHARDS}")
    print(f"Hex Walk: 0x{HEX_WALK:04X}")
    print()
    
    shard_samples = {i: [] for i in range(MONSTER_SHARDS)}
    
    # Simulate reading sectors
    for sector in range(num_sectors):
        # Generate fake sector data (in real driver, read from disk)
        data = bytes([sector % 256] * 512)
        
        # Map to shard
        shard_id = sector_to_shard(sector)
        
        # Sample
        sample = sample_sector(data, shard_id)
        
        shard_samples[shard_id].append({
            "sector": sector,
            "sample": sample,
            "walk_step": (shard_id % 4) + 1
        })
    
    # Display results
    print("Shard Distribution:")
    print("-" * 70)
    print("Shard | Samples | Walk | Example Sample")
    print("-" * 70)
    
    for shard_id in range(min(20, MONSTER_SHARDS)):
        samples = shard_samples[shard_id]
        if samples:
            walk_step = samples[0]["walk_step"]
            example = samples[0]["sample"]
            print(f"{shard_id:5d} | {len(samples):7d} | {walk_step:4d} | 0x{example:08X}")
    
    print()
    print(f"Total samples: {sum(len(s) for s in shard_samples.values())}")
    print()
    
    # Verify distribution
    total = sum(len(s) for s in shard_samples.values())
    avg = total / MONSTER_SHARDS
    variance = sum((len(s) - avg)**2 for s in shard_samples.values()) / MONSTER_SHARDS
    
    print("Distribution Stats:")
    print(f"  Average: {avg:.2f} samples/shard")
    print(f"  Variance: {variance:.2f}")
    print(f"  Min: {min(len(s) for s in shard_samples.values())}")
    print(f"  Max: {max(len(s) for s in shard_samples.values())}")
    print()
    
    return shard_samples

def main():
    print("🔮⚡📻🦞 MONSTER KERNEL DRIVER TEST")
    print("=" * 70)
    print()
    print("Simulating HDD sampling (userspace)...")
    print()
    
    # Simulate
    samples = simulate_hdd_sampling(10000)
    
    print("=" * 70)
    print("KERNEL DRIVER COMMANDS")
    print("=" * 70)
    print()
    print("To build and load real kernel module:")
    print()
    print("  cd kernel/")
    print("  make")
    print("  sudo insmod monster_sampler.ko")
    print("  cat /sys/kernel/monster_sampler/shards")
    print("  sudo rmmod monster_sampler")
    print()
    print("⚠️  WARNING: Kernel module requires root and can crash system!")
    print("   Test in VM first!")
    print()
    print("✅ Simulation complete!")
    print("🔮 Ready for real HDD sampling!")

if __name__ == '__main__':
    main()
