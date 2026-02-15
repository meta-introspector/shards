mod fractran_meta_macro;

use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::env;
use fractran_meta_macro::{fractran_from_shards, FractranMemoryShard};

#[derive(Debug, Serialize, Deserialize)]
struct ShardedFile {
    path: String,
    shard_id: u64,
    fractran_pair: (u64, u64),
}

fn shard_string(s: &str, modulo: u64) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(s.as_bytes());
    let hash = hasher.finalize();
    let hash_num = u64::from_be_bytes([
        hash[0], hash[1], hash[2], hash[3],
        hash[4], hash[5], hash[6], hash[7],
    ]);
    hash_num % modulo
}

fn main() -> std::io::Result<()> {
    let input_file = env::var("INPUT_FILE").expect("INPUT_FILE not set");
    let output_file = env::var("OUTPUT_FILE").expect("OUTPUT_FILE not set");
    let shard_prime: u64 = env::var("SHARD_PRIME").expect("SHARD_PRIME not set").parse().unwrap();
    
    // Generate FRACTRAN program from 71 shards via macro
    let fractran_program = fractran_from_shards!(
        0 => 71, 1 => 59, 2 => 47, 3 => 41, 4 => 31, 5 => 29, 6 => 23, 7 => 19,
        8 => 17, 9 => 13, 10 => 11, 11 => 7, 12 => 5, 13 => 3, 14 => 2
    );
    
    println!("🔮 Generated FRACTRAN program with {} steps", fractran_program.len());
    
    let file = File::open(&input_file)?;
    let reader = BufReader::new(file);
    
    let mut shards = Vec::new();
    
    for line in reader.lines() {
        let path = line?;
        if !path.is_empty() {
            let shard_id = shard_string(&path, shard_prime);
            
            // Create memory shard
            let memory_shard = FractranMemoryShard {
                shard_id,
                prime_mod: shard_prime,
                data: path.as_bytes().to_vec(),
            };
            
            shards.push(ShardedFile {
                path: path.clone(),
                shard_id,
                fractran_pair: memory_shard.to_fractran_pair(),
            });
        }
    }
    
    println!("💾 Sharded {} files into {} shards", shards.len(), shard_prime);
    
    let json = serde_json::to_string_pretty(&shards)?;
    std::fs::write(&output_file, json)?;
    
    println!("✅ Saved to: {}", output_file);
    
    Ok(())
}
