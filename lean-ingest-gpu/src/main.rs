use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use anyhow::Result;

#[derive(Serialize, Deserialize, Debug, Clone)]
struct LeanFile {
    path: String,
    shard: u8,
    lines: usize,
    theorem: bool,
    def: bool,
    inductive: bool,
}

fn hash_shard(path: &str) -> u8 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    path.hash(&mut hasher);
    (hasher.finish() % 71) as u8
}

fn analyze_file(path: &str) -> Option<LeanFile> {
    let content = fs::read_to_string(path).ok()?;
    Some(LeanFile {
        path: path.to_string(),
        shard: hash_shard(path),
        lines: content.lines().count(),
        theorem: content.contains("theorem"),
        def: content.contains("def"),
        inductive: content.contains("inductive"),
    })
}

fn main() -> Result<()> {
    let input = "/home/mdupont/introspector/.temp-find-lean.txt";
    let output_dir = "/home/mdupont/introspector/lean_shards";
    
    println!("📖 Reading paths...");
    let file = File::open(input)?;
    let paths: Vec<String> = BufReader::new(file)
        .lines()
        .filter_map(|l| l.ok())
        .filter(|l| l.ends_with(".lean"))
        .collect();
    
    println!("Found {} Lean files", paths.len());
    println!("🚀 Processing with Rayon (all CPUs)...");
    
    let results: Vec<LeanFile> = paths
        .par_iter()
        .filter_map(|p| analyze_file(p))
        .collect();
    
    println!("✅ Analyzed {} files", results.len());
    println!("📦 Distributing to 71 shards...");
    
    fs::create_dir_all(output_dir)?;
    
    let mut shards: Vec<Vec<LeanFile>> = (0..71).map(|_| Vec::new()).collect();
    for r in results {
        shards[r.shard as usize].push(r);
    }
    
    (0..71).into_par_iter().for_each(|i| {
        let shard_file = format!("{}/shard_{:02}.json", output_dir, i);
        if let Ok(f) = File::create(&shard_file) {
            let _ = serde_json::to_writer(f, &shards[i]);
            if !shards[i].is_empty() {
                println!("  Shard {:02}: {} files", i, shards[i].len());
            }
        }
    });
    
    println!("\n💾 Saved to {}/", output_dir);
    Ok(())
}
