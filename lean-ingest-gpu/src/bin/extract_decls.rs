use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use anyhow::Result;

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Decl {
    file: String,
    shard: u8,
    kind: String,
    name: String,
    line: usize,
    content: String,
}

fn hash_shard(s: &str) -> u8 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    (hasher.finish() % 71) as u8
}

fn extract_decls(path: &str) -> Vec<Decl> {
    let Ok(content) = fs::read_to_string(path) else { return vec![] };
    let mut decls = Vec::new();
    let mut current = String::new();
    let mut kind = String::new();
    let mut name = String::new();
    let mut start_line = 0;
    
    for (i, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();
        
        // Start of declaration
        if trimmed.starts_with("theorem ") || trimmed.starts_with("def ") || 
           trimmed.starts_with("inductive ") || trimmed.starts_with("structure ") ||
           trimmed.starts_with("class ") || trimmed.starts_with("instance ") {
            
            if !current.is_empty() {
                decls.push(Decl {
                    file: path.to_string(),
                    shard: hash_shard(&format!("{}:{}", path, name)),
                    kind: kind.clone(),
                    name: name.clone(),
                    line: start_line,
                    content: current.clone(),
                });
            }
            
            kind = trimmed.split_whitespace().next().unwrap_or("").to_string();
            name = trimmed.split_whitespace().nth(1).unwrap_or("").split(':').next().unwrap_or("").to_string();
            current = line.to_string() + "\n";
            start_line = i + 1;
        } else if !current.is_empty() {
            current.push_str(line);
            current.push('\n');
        }
    }
    
    if !current.is_empty() {
        decls.push(Decl {
            file: path.to_string(),
            shard: hash_shard(&format!("{}:{}", path, name)),
            kind,
            name,
            line: start_line,
            content: current,
        });
    }
    
    decls
}

fn main() -> Result<()> {
    let input = "/home/mdupont/introspector/.temp-find-lean.txt";
    let output_dir = "/home/mdupont/introspector/lean_decl_shards";
    
    println!("📖 Reading paths...");
    let file = File::open(input)?;
    let paths: Vec<String> = BufReader::new(file)
        .lines()
        .filter_map(|l| l.ok())
        .filter(|l| l.ends_with(".lean"))
        .collect();
    
    println!("Found {} Lean files", paths.len());
    println!("🔍 Extracting declarations with Rayon...");
    
    let all_decls: Vec<Decl> = paths
        .par_iter()
        .flat_map(|p| extract_decls(p))
        .collect();
    
    println!("✅ Extracted {} declarations", all_decls.len());
    println!("📦 Distributing to 71 shards...");
    
    fs::create_dir_all(output_dir)?;
    
    let mut shards: Vec<Vec<Decl>> = (0..71).map(|_| Vec::new()).collect();
    for d in all_decls {
        shards[d.shard as usize].push(d);
    }
    
    (0..71).into_par_iter().for_each(|i| {
        let shard_file = format!("{}/decl_shard_{:02}.json", output_dir, i);
        if let Ok(f) = File::create(&shard_file) {
            let _ = serde_json::to_writer(f, &shards[i]);
            if !shards[i].is_empty() {
                let theorems = shards[i].iter().filter(|d| d.kind == "theorem").count();
                let defs = shards[i].iter().filter(|d| d.kind == "def").count();
                println!("  Shard {:02}: {} decls ({} thm, {} def)", i, shards[i].len(), theorems, defs);
            }
        }
    });
    
    println!("\n💾 Saved to {}/", output_dir);
    Ok(())
}
