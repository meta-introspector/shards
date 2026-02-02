use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::collections::{HashMap, HashSet};
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
struct TopoArrow {
    from_prime: u64,
    to_prime: u64,
    from_topo: u8,
    to_topo: u8,
    from_emoji: String,
    to_emoji: String,
    shared_decls: usize,
    shared_files: usize,
    strength: f64,
}

const PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
const EMOJI: [&str; 10] = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"];

fn main() -> Result<()> {
    let input = "/home/mdupont/introspector/lean_monster_mod_shards";
    let output = "/home/mdupont/introspector/monster_topo_arrows.json";
    
    println!("📖 Loading shards...");
    
    let shards: Vec<(u64, HashSet<String>, HashSet<String>)> = PRIMES
        .iter()
        .filter_map(|&p| {
            let path = format!("{}/prime_mod_{:02}.json", input, p);
            let content = fs::read_to_string(&path).ok()?;
            let consts: Vec<Const> = serde_json::from_str(&content).ok()?;
            let decls: HashSet<String> = consts.iter().map(|c| format!("{}:{}", c.file, c.decl)).collect();
            let files: HashSet<String> = consts.iter().map(|c| c.file.clone()).collect();
            println!("  Prime {}: {} decls, {} files", p, decls.len(), files.len());
            Some((p, decls, files))
        })
        .collect();
    
    println!("✅ Loaded {} shards", shards.len());
    println!("🔍 Finding 10-fold arrows via shared declarations...");
    
    let mut arrows = Vec::new();
    
    for (i, (p1, d1, f1)) in shards.iter().enumerate() {
        for (p2, d2, f2) in &shards[i+1..] {
            let shared_decls = d1.intersection(d2).count();
            let shared_files = f1.intersection(f2).count();
            
            if shared_decls > 0 {
                let strength = shared_decls as f64 / d1.len().min(d2.len()) as f64;
                let t1 = (p1 % 10) as u8;
                let t2 = (p2 % 10) as u8;
                
                arrows.push(TopoArrow {
                    from_prime: *p1,
                    to_prime: *p2,
                    from_topo: t1,
                    to_topo: t2,
                    from_emoji: EMOJI[t1 as usize].to_string(),
                    to_emoji: EMOJI[t2 as usize].to_string(),
                    shared_decls,
                    shared_files,
                    strength,
                });
            }
        }
    }
    
    arrows.sort_by(|a, b| b.strength.partial_cmp(&a.strength).unwrap());
    
    println!("\n🎯 Found {} arrows", arrows.len());
    println!("\n🔝 Top 20 strongest:");
    for (i, a) in arrows.iter().take(20).enumerate() {
        println!("  {}. {} {} → {} {} | {:.4} | {}K decls, {}K files",
            i+1, a.from_prime, a.from_emoji, a.to_prime, a.to_emoji,
            a.strength, a.shared_decls / 1000, a.shared_files / 1000
        );
    }
    
    let mut topo_map: HashMap<(u8, u8), Vec<&TopoArrow>> = HashMap::new();
    for a in &arrows {
        topo_map.entry((a.from_topo, a.to_topo)).or_default().push(a);
    }
    
    println!("\n🌊 10-fold transitions:");
    let mut topo_vec: Vec<_> = topo_map.iter().collect();
    topo_vec.sort_by_key(|(_, v)| -(v.iter().map(|r| r.shared_decls).sum::<usize>() as i64));
    
    for ((t1, t2), rels) in topo_vec.iter().take(15) {
        let total_decls: usize = rels.iter().map(|r| r.shared_decls).sum();
        let total_strength: f64 = rels.iter().map(|r| r.strength).sum();
        println!("  {} → {}: {} arrows, {}K decls, Σ={:.2}",
            EMOJI[*t1 as usize], EMOJI[*t2 as usize], rels.len(), total_decls / 1000, total_strength
        );
    }
    
    serde_json::to_writer_pretty(File::create(output)?, &arrows)?;
    println!("\n💾 {}", output);
    Ok(())
}
