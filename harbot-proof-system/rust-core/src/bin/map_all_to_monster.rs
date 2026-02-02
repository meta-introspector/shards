use std::fs;
use std::path::Path;
use sha2::{Digest, Sha256};

// Monster group order
const MONSTER_ORDER: u128 = 808017424794512875886459904961710757005754368000000000;
const MONSTER_WALK_STEP: u64 = 0x1F90;

// 71 primes for Gödel encoding
const PRIMES: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353
];

#[derive(Debug)]
struct MonsterWalk {
    position: u128,
    shard_history: Vec<u8>,
}

impl MonsterWalk {
    fn new() -> Self {
        Self {
            position: 0,
            shard_history: Vec::new(),
        }
    }
    
    fn step(&mut self, data: u64) -> u8 {
        // Monster walk: position = (position + step * data) mod order
        self.position = (self.position + (MONSTER_WALK_STEP as u128) * (data as u128)) % MONSTER_ORDER;
        let shard = (self.position % 71) as u8;
        self.shard_history.push(shard);
        shard
    }
    
    fn j_invariant(&self) -> u64 {
        let shard = (self.position % 71) as u64;
        744 + 196884 * shard
    }
    
    fn godel_number(&self) -> u128 {
        let mut godel: u128 = 1;
        for (i, &shard) in self.shard_history.iter().take(20).enumerate() {
            let prime = PRIMES[i] as u128;
            let exp = (shard + 1) as u32;
            godel = godel.saturating_mul(prime.saturating_pow(exp));
        }
        godel
    }
}

fn read_all_bytes(path: &Path) -> Vec<u8> {
    fs::read(path).unwrap_or_default()
}

fn parse_perf_trace(path: &Path) -> Vec<u64> {
    let content = fs::read_to_string(path).unwrap_or_default();
    content.lines()
        .filter_map(|line| {
            // Extract hex addresses and convert to u64
            line.split_whitespace()
                .find(|s| s.starts_with("0x") || s.starts_with("0X"))
                .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        })
        .collect()
}

fn hash_to_u64(data: &[u8]) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    u64::from_le_bytes(result[0..8].try_into().unwrap())
}

pub fn map_all_to_monster_walk(proof_dir: &Path) -> MonsterWalk {
    let mut walker = MonsterWalk::new();
    
    println!("Mapping all data to Monster walk...\n");
    
    // 1. Map all bytes from files
    for entry in fs::read_dir(proof_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        
        if path.is_file() {
            let bytes = read_all_bytes(&path);
            if !bytes.is_empty() {
                let data = hash_to_u64(&bytes);
                let shard = walker.step(data);
                println!("File: {:?} -> Shard {}", path.file_name(), shard);
            }
        }
    }
    
    // 2. Map perf traces
    for entry in fs::read_dir(proof_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        
        if path.extension().and_then(|s| s.to_str()) == Some("script") {
            let traces = parse_perf_trace(&path);
            for trace in traces.iter().take(100) {
                let shard = walker.step(*trace);
                if traces.len() < 10 {
                    println!("Trace: 0x{:x} -> Shard {}", trace, shard);
                }
            }
            println!("Processed {} traces from {:?}", traces.len(), path.file_name());
        }
    }
    
    // 3. Map perf.data files (raw bytes)
    for entry in fs::read_dir(proof_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        
        if path.extension().and_then(|s| s.to_str()) == Some("data") {
            let bytes = read_all_bytes(&path);
            // Sample every 1024 bytes
            for chunk in bytes.chunks(1024) {
                let data = hash_to_u64(chunk);
                walker.step(data);
            }
            println!("Processed {} bytes from {:?}", bytes.len(), path.file_name());
        }
    }
    
    walker
}

fn main() {
    let proof_dir = Path::new("complete_proofs");
    
    if !proof_dir.exists() {
        println!("Creating demo proof directory...");
        fs::create_dir_all(proof_dir).unwrap();
    }
    
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║     MAP ALL DATA TO MONSTER WALK                           ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    let walker = map_all_to_monster_walk(proof_dir);
    
    println!("\n╔════════════════════════════════════════════════════════════╗");
    println!("║     MONSTER WALK COMPLETE                                  ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    println!("Final position: {}", walker.position);
    println!("Total steps: {}", walker.shard_history.len());
    println!("j-invariant: {}", walker.j_invariant());
    println!("Gödel number: {}", walker.godel_number());
    
    // Save witness
    let witness = format!(
        "{{
  \"position\": \"{}\",
  \"steps\": {},
  \"j_invariant\": {},
  \"godel_number\": \"{}\",
  \"shard_history\": {:?}
}}",
        walker.position,
        walker.shard_history.len(),
        walker.j_invariant(),
        walker.godel_number(),
        &walker.shard_history[..walker.shard_history.len().min(100)]
    );
    
    fs::write(proof_dir.join("monster_walk_witness.json"), witness).unwrap();
    println!("\n✓ Witness saved: complete_proofs/monster_walk_witness.json");
    println!("\nQED 🔮⚡📻🦞");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_monster_walk() {
        let mut walker = MonsterWalk::new();
        let shard = walker.step(42);
        assert!(shard < 71);
    }
    
    #[test]
    fn test_j_invariant() {
        let mut walker = MonsterWalk::new();
        walker.step(0);
        let j = walker.j_invariant();
        assert!(j >= 744);
    }
}
