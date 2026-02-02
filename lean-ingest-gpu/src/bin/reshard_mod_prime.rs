use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use anyhow::Result;

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Const {
    file: String,
    decl: String,
    shard: u8,
    name: String,
    line: usize,
}

const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

fn hash_mod_prime(s: &str, p: u64) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish() % p
}

fn main() -> Result<()> {
    let input_dir = "/home/mdupont/introspector/lean_const_shards";
    let output_dir = "/home/mdupont/introspector/lean_monster_mod_shards";
    
    println!("📖 Reading const shards...");
    
    let all_consts: Vec<(Const, u64)> = (0..71)
        .into_par_iter()
        .flat_map(|i| {
            let path = format!("{}/const_shard_{:02}.json", input_dir, i);
            let Ok(content) = fs::read_to_string(&path) else { return vec![] };
            let consts: Vec<Const> = serde_json::from_str(&content).unwrap_or_default();
            
            // Assign prime shard via mod p
            consts.into_iter().map(|c| {
                let hash = hash_mod_prime(&c.name, 71);
                let prime = MONSTER_PRIMES[(hash % 15) as usize];
                (c, prime)
            }).collect::<Vec<_>>()
        })
        .collect();
    
    println!("✅ Loaded {} consts", all_consts.len());
    println!("🔍 Resharding via mod p for 15 Monster primes...");
    
    fs::create_dir_all(output_dir)?;
    
    // Group by prime
    let mut prime_shards: Vec<Vec<Const>> = vec![Vec::new(); 15];
    for (c, prime) in all_consts {
        let idx = MONSTER_PRIMES.iter().position(|&p| p == prime).unwrap();
        prime_shards[idx].push(c);
    }
    
    // Save in parallel
    (0..15).into_par_iter().for_each(|i| {
        let prime = MONSTER_PRIMES[i];
        let shard_file = format!("{}/prime_mod_{:02}.json", output_dir, prime);
        if let Ok(f) = File::create(&shard_file) {
            let _ = serde_json::to_writer(f, &prime_shards[i]);
            println!("  Prime {:02} (mod): {} consts", prime, prime_shards[i].len());
        }
    });
    
    println!("\n💾 Saved to {}/", output_dir);
    Ok(())
}
