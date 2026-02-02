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

#[derive(Serialize, Deserialize, Debug)]
struct MonsterPrimeShard {
    prime: u64,
    consts: Vec<Const>,
}

const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

fn hash_to_prime(s: &str) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    MONSTER_PRIMES[(hasher.finish() % 15) as usize]
}

fn main() -> Result<()> {
    let input_dir = "/home/mdupont/introspector/lean_const_shards";
    let output_dir = "/home/mdupont/introspector/lean_monster_prime_shards";
    
    println!("📖 Reading const shards...");
    
    let all_consts: Vec<Const> = (0..71)
        .into_par_iter()
        .flat_map(|i| {
            let path = format!("{}/const_shard_{:02}.json", input_dir, i);
            let Ok(content) = fs::read_to_string(&path) else { return vec![] };
            serde_json::from_str::<Vec<Const>>(&content).unwrap_or_default()
        })
        .collect();
    
    println!("✅ Loaded {} consts", all_consts.len());
    println!("🔍 Sampling for 15 Monster primes...");
    
    fs::create_dir_all(output_dir)?;
    
    // Group by Monster prime
    let mut prime_shards: Vec<Vec<Const>> = vec![Vec::new(); 15];
    for c in all_consts {
        let prime = hash_to_prime(&c.name);
        let idx = MONSTER_PRIMES.iter().position(|&p| p == prime).unwrap();
        prime_shards[idx].push(c);
    }
    
    // Save each prime shard
    MONSTER_PRIMES.iter().enumerate().for_each(|(i, &prime)| {
        let shard = MonsterPrimeShard {
            prime,
            consts: prime_shards[i].clone(),
        };
        
        let shard_file = format!("{}/monster_prime_{:02}.json", output_dir, prime);
        if let Ok(f) = File::create(&shard_file) {
            let _ = serde_json::to_writer(f, &shard);
            println!("  Prime {:02}: {} consts", prime, shard.consts.len());
        }
    });
    
    println!("\n💾 Saved to {}/", output_dir);
    println!("🐓 Monster primes: {:?}", MONSTER_PRIMES);
    Ok(())
}
