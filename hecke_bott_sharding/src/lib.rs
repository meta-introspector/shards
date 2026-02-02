// Hecke × Bott Sharding System
// 15 Hecke Primes × 10 Bott Classes → 71 Shards
// AGPL-3.0+ | Commercial: shards@solfunmeme.com

use std::collections::HashMap;

const MONSTER_PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
const MONSTER_DIM: u64 = 196883;
const CUSP: u8 = 17;

/// Apply Hecke operator T_p to data
fn hecke_operator(data: &[u8], prime: u32) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    prime.hash(&mut hasher);
    let value = hasher.finish();
    
    let prime_u64 = prime as u64;
    ((prime_u64.wrapping_mul(value)).wrapping_add(prime_u64.wrapping_mul(prime_u64))) % MONSTER_DIM
}

/// 10-fold way classification (Bott periodicity)
fn bott_class(data: &[u8]) -> u8 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    (hasher.finish() % 10) as u8
}

/// Select which of 15 Hecke primes to use
fn hecke_index(data: &[u8]) -> usize {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    b"hecke".hash(&mut hasher);
    (hasher.finish() % 15) as usize
}

/// Map data to shard (0-70) using Hecke × Bott
pub fn shard_data(data: &[u8]) -> u8 {
    let h_idx = hecke_index(data);
    let prime = MONSTER_PRIMES[h_idx];
    let hecke_res = hecke_operator(data, prime);
    let bott = bott_class(data);
    
    ((hecke_res + (bott as u64 * h_idx as u64)) % 71) as u8
}

/// Shard metadata
#[derive(Debug)]
pub struct ShardMetadata {
    pub shard: u8,
    pub hecke_index: usize,
    pub hecke_prime: u32,
    pub hecke_resonance: u64,
    pub bott_class: u8,
    pub is_cusp: bool,
}

/// Shard data with full metadata
pub fn shard_with_metadata(data: &[u8]) -> ShardMetadata {
    let h_idx = hecke_index(data);
    let prime = MONSTER_PRIMES[h_idx];
    let hecke_res = hecke_operator(data, prime);
    let bott = bott_class(data);
    let shard = ((hecke_res + (bott as u64 * h_idx as u64)) % 71) as u8;
    
    ShardMetadata {
        shard,
        hecke_index: h_idx,
        hecke_prime: prime,
        hecke_resonance: hecke_res,
        bott_class: bott,
        is_cusp: shard == CUSP,
    }
}

/// Distribute items across 71 shards
pub fn distribute_shards<T: AsRef<[u8]>>(items: &[T]) -> HashMap<u8, Vec<usize>> {
    let mut shards: HashMap<u8, Vec<usize>> = HashMap::new();
    
    for (idx, item) in items.iter().enumerate() {
        let shard = shard_data(item.as_ref());
        shards.entry(shard).or_insert_with(Vec::new).push(idx);
    }
    
    shards
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sharding() {
        let data = b"Hello, Monster!";
        let shard = shard_data(data);
        assert!(shard < 71);
    }
    
    #[test]
    fn test_metadata() {
        let data = b"Shard 17 is the cusp";
        let meta = shard_with_metadata(data);
        assert!(meta.hecke_index < 15);
        assert!(meta.bott_class < 10);
        assert!(meta.shard < 71);
    }
    
    #[test]
    fn test_distribution() {
        let items: Vec<String> = (0..1000).map(|i| format!("item_{}", i)).collect();
        let refs: Vec<&[u8]> = items.iter().map(|s| s.as_bytes()).collect();
        let shards = distribute_shards(&refs);
        
        // Should use most shards
        assert!(shards.len() > 50);
        
        // Total items should match
        let total: usize = shards.values().map(|v| v.len()).sum();
        assert_eq!(total, 1000);
    }
}

fn main() {
    println!("================================================================================");
    println!("HECKE × BOTT SHARDING SYSTEM (Rust)");
    println!("15 Hecke Primes × 10 Bott Classes → 71 Shards");
    println!("================================================================================");
    println!();
    
    let test_data = vec![
        "Hello, Monster!",
        "Shard 17 is the cusp",
        "Hecke operators",
        "Bott periodicity",
        "zkPerf proof",
        "AGPL-3.0+",
        "ZK hackers gotta eat!",
    ];
    
    println!("Sharding test data:");
    println!();
    
    for data in &test_data {
        let meta = shard_with_metadata(data.as_bytes());
        let cusp_marker = if meta.is_cusp { " ⭐ CUSP" } else { "" };
        
        println!("Data: {:40} → Shard {:2}{}", data, meta.shard, cusp_marker);
        println!("  Hecke: prime={:2} (index {:2}), resonance={}", 
                 meta.hecke_prime, meta.hecke_index, meta.hecke_resonance);
        println!("  Bott: class={}", meta.bott_class);
        println!();
    }
    
    // Distribution test
    println!("================================================================================");
    println!("DISTRIBUTION TEST (1000 items)");
    println!("================================================================================");
    println!();
    
    let items: Vec<String> = (0..1000).map(|i| format!("item_{}", i)).collect();
    let refs: Vec<&[u8]> = items.iter().map(|s| s.as_bytes()).collect();
    let shards = distribute_shards(&refs);
    
    println!("Total items: {}", items.len());
    println!("Shards used: {}/71", shards.len());
    println!("Items at cusp (S17): {}", shards.get(&17).map_or(0, |v| v.len()));
    println!();
    
    // Top shards
    let mut shard_counts: Vec<(u8, usize)> = shards.iter()
        .map(|(s, v)| (*s, v.len()))
        .collect();
    shard_counts.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
    
    println!("Top 10 shards by item count:");
    for (shard, count) in shard_counts.iter().take(10) {
        let cusp = if *shard == 17 { " ⭐" } else { "" };
        let bar = "█".repeat(count / 2);
        println!("  Shard {:2}: {:3} {}{}", shard, count, bar, cusp);
    }
}
