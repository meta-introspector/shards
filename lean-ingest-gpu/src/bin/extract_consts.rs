use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use anyhow::Result;
use regex::Regex;

#[derive(Serialize, Deserialize, Debug, Clone)]
struct Const {
    file: String,
    decl: String,
    shard: u8,
    name: String,
    line: usize,
}

fn hash_shard(s: &str) -> u8 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    (hasher.finish() % 71) as u8
}

fn extract_consts(file: &str, decl_name: &str, content: &str, start_line: usize) -> Vec<Const> {
    let mut consts = Vec::new();
    let re = Regex::new(r"\b([a-zA-Z_][a-zA-Z0-9_']*)\b").unwrap();
    
    for (i, line) in content.lines().enumerate() {
        for cap in re.captures_iter(line) {
            if let Some(name) = cap.get(1) {
                let n = name.as_str();
                if n.len() > 1 && !n.starts_with('_') {
                    consts.push(Const {
                        file: file.to_string(),
                        decl: decl_name.to_string(),
                        shard: hash_shard(&format!("{}:{}:{}", file, decl_name, n)),
                        name: n.to_string(),
                        line: start_line + i,
                    });
                }
            }
        }
    }
    consts
}

fn extract_decls_and_consts(path: &str) -> Vec<Const> {
    let Ok(content) = fs::read_to_string(path) else { return vec![] };
    let mut all_consts = Vec::new();
    let mut current = String::new();
    let mut name = String::new();
    let mut start_line = 0;
    
    for (i, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();
        
        if trimmed.starts_with("theorem ") || trimmed.starts_with("def ") || 
           trimmed.starts_with("inductive ") || trimmed.starts_with("structure ") ||
           trimmed.starts_with("class ") || trimmed.starts_with("instance ") {
            
            if !current.is_empty() {
                all_consts.extend(extract_consts(path, &name, &current, start_line));
            }
            
            name = trimmed.split_whitespace().nth(1).unwrap_or("").split(':').next().unwrap_or("").to_string();
            current = line.to_string() + "\n";
            start_line = i + 1;
        } else if !current.is_empty() {
            current.push_str(line);
            current.push('\n');
        }
    }
    
    if !current.is_empty() {
        all_consts.extend(extract_consts(path, &name, &current, start_line));
    }
    
    all_consts
}

fn main() -> Result<()> {
    let input = "/home/mdupont/introspector/.temp-find-lean.txt";
    let output_dir = "/home/mdupont/introspector/lean_const_shards";
    
    println!("📖 Reading paths...");
    let file = File::open(input)?;
    let paths: Vec<String> = BufReader::new(file)
        .lines()
        .filter_map(|l| l.ok())
        .filter(|l| l.ends_with(".lean"))
        .collect();
    
    println!("Found {} Lean files", paths.len());
    println!("🔍 Extracting consts with Rayon...");
    
    let all_consts: Vec<Const> = paths
        .par_iter()
        .flat_map(|p| extract_decls_and_consts(p))
        .collect();
    
    println!("✅ Extracted {} consts", all_consts.len());
    println!("📦 Distributing to 71 shards...");
    
    fs::create_dir_all(output_dir)?;
    
    let mut shards: Vec<Vec<Const>> = (0..71).map(|_| Vec::new()).collect();
    for c in all_consts {
        shards[c.shard as usize].push(c);
    }
    
    (0..71).into_par_iter().for_each(|i| {
        let shard_file = format!("{}/const_shard_{:02}.json", output_dir, i);
        if let Ok(f) = File::create(&shard_file) {
            let _ = serde_json::to_writer(f, &shards[i]);
            if !shards[i].is_empty() {
                println!("  Shard {:02}: {} consts", i, shards[i].len());
            }
        }
    });
    
    println!("\n💾 Saved to {}/", output_dir);
    Ok(())
}
