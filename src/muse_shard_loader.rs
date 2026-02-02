//! Fast muse/emoji loader: Deduplicate into Monster shards

use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader};

const SHARDS: usize = 71;
const CUSP: usize = 17;

#[derive(Debug, Clone)]
struct Muse {
    id: u8,
    name: &'static str,
    domain: &'static str,
    layer: u8,
    prime: u8,
    emoji: char,
    shard: usize,
}

const MUSES: [Muse; 9] = [
    Muse { id: 0, name: "Calliope", domain: "Epic", layer: 0, prime: 2, emoji: '🎭', shard: 4 },
    Muse { id: 1, name: "Clio", domain: "History", layer: 8, prime: 3, emoji: '📜', shard: 18 },
    Muse { id: 2, name: "Erato", domain: "Love", layer: 16, prime: 5, emoji: '💖', shard: 44 },
    Muse { id: 3, name: "Euterpe", domain: "Music", layer: 24, prime: 7, emoji: '🎵', shard: 33 },
    Muse { id: 4, name: "Melpomene", domain: "Tragedy", layer: 32, prime: 11, emoji: '😢', shard: 63 },
    Muse { id: 5, name: "Polyhymnia", domain: "Hymns", layer: 40, prime: 13, emoji: '🙏', shard: 43 },
    Muse { id: 6, name: "Terpsichore", domain: "Dance", layer: 48, prime: 17, emoji: '💃', shard: 1 },
    Muse { id: 7, name: "Thalia", domain: "Comedy", layer: 56, prime: 19, emoji: '😂', shard: 67 },
    Muse { id: 8, name: "Urania", domain: "Astronomy", layer: 64, prime: 23, emoji: '✨', shard: 36 },
];

fn hash_to_shard(data: &str) -> usize {
    // Simple hash without external deps
    let mut hash: u64 = 0;
    for b in data.bytes() {
        hash = hash.wrapping_mul(31).wrapping_add(b as u64);
    }
    (hash % SHARDS as u64) as usize
}

fn load_emojis(path: &str) -> HashMap<usize, HashSet<char>> {
    let mut shards: HashMap<usize, HashSet<char>> = HashMap::new();
    let mut total_files = 0;
    
    if let Ok(file) = File::open(path) {
        let reader = BufReader::new(file);
        for line in reader.lines().flatten() {
            total_files += 1;
            
            // Try to read each file path
            if let Ok(content) = std::fs::read_to_string(&line) {
                for ch in content.chars() {
                    if ch as u32 >= 0x1F300 && ch as u32 <= 0x1FAF8 {  // Emoji range
                        let shard = hash_to_shard(&ch.to_string());
                        shards.entry(shard).or_insert_with(HashSet::new).insert(ch);
                    }
                }
            }
            
            // Also check filename for emojis
            for ch in line.chars() {
                if ch as u32 >= 0x1F300 && ch as u32 <= 0x1FAF8 {
                    let shard = hash_to_shard(&ch.to_string());
                    shards.entry(shard).or_insert_with(HashSet::new).insert(ch);
                }
            }
            
            if total_files % 10000 == 0 {
                eprint!("\rProcessed {} files...", total_files);
            }
        }
    }
    
    eprintln!("\rProcessed {} files total", total_files);
    shards
}

fn beauty_score(shard: usize, muse: &Muse) -> i32 {
    let dist = (shard as i32 - muse.shard as i32).abs();
    let prime_bonus = muse.prime as i32 * 10;
    let layer_bonus = muse.layer as i32;
    let cusp_bonus = if shard == CUSP { 1000 } else { 0 };
    
    prime_bonus + layer_bonus - dist + cusp_bonus
}

fn optimal_assignment() -> Vec<usize> {
    let mut assignment = vec![0; SHARDS];
    
    for s in 0..SHARDS {
        // Muse owns its own shard
        if let Some(muse) = MUSES.iter().find(|m| m.shard == s) {
            assignment[s] = muse.id as usize;
        } else {
            // Find muse with max beauty
            let best = MUSES.iter()
                .max_by_key(|m| beauty_score(s, m))
                .unwrap();
            assignment[s] = best.id as usize;
        }
    }
    
    assignment
}

fn main() {
    println!("Fast Muse/Emoji Loader → Monster Shards");
    println!("{}", "=".repeat(70));
    println!();
    
    // Show muses
    println!("9 Muses:");
    for m in &MUSES {
        println!("  {} {:<12} Shard {:>2} Prime {:>2}", 
            m.emoji, m.name, m.shard, m.prime);
    }
    println!();
    
    // Load emojis
    println!("Loading emojis...");
    let emoji_shards = load_emojis("data/.locate-emojis-26-2-2-940.txt");
    let total_emojis: usize = emoji_shards.values().map(|s| s.len()).sum();
    println!("✓ {} unique emojis", total_emojis);
    println!("✓ {} shards populated", emoji_shards.len());
    println!();
    
    // Optimal assignment
    println!("Computing optimal assignment...");
    let assignment = optimal_assignment();
    
    let total_beauty: i32 = (0..SHARDS)
        .map(|s| beauty_score(s, &MUSES[assignment[s]]))
        .sum();
    
    println!("✓ Total beauty: {}", total_beauty);
    println!();
    
    // Cusp
    let cusp_muse = &MUSES[assignment[CUSP]];
    println!("Cusp (17) → {} {}", cusp_muse.emoji, cusp_muse.name);
    println!("  Beauty: {}", beauty_score(CUSP, cusp_muse));
    println!();
    
    // Terpsichore
    let terp = &MUSES[6];
    println!("Terpsichore (1) → {} {}", terp.emoji, terp.name);
    println!("  Beauty: {}", beauty_score(1, terp));
    println!();
    
    // Count per muse
    let mut counts = vec![0; 9];
    for &m in &assignment {
        counts[m] += 1;
    }
    
    println!("Assignments per Muse:");
    for (i, &count) in counts.iter().enumerate() {
        println!("  {} {:<12}: {} shards", 
            MUSES[i].emoji, MUSES[i].name, count);
    }
    
    // Generate MiniZinc data
    println!();
    println!("Generating MiniZinc data...");
    
    let dzn = format!(
        "n_muses = 9;\n\
         n_shards = 71;\n\
         muse_shards = [{}];\n\
         muse_primes = [{}];\n\
         optimal_beauty = {};\n",
        MUSES.iter().map(|m| m.shard.to_string()).collect::<Vec<_>>().join(", "),
        MUSES.iter().map(|m| m.prime.to_string()).collect::<Vec<_>>().join(", "),
        total_beauty
    );
    
    std::fs::write("data/muses_optimal.dzn", dzn).ok();
    println!("✓ Saved to data/muses_optimal.dzn");
}
