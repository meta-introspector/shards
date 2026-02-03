use std::collections::HashMap;
use std::path::Path;
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Arrow {
    pub from_shard: u8,
    pub to_shard: u8,
    pub weight: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ArrowGraph {
    pub arrows: Vec<Arrow>,
    pub total_arrows: usize,
    pub max_weight: usize,
}

pub fn build_arrow_graph(files: &[&Path]) -> ArrowGraph {
    let mut shard_map: HashMap<String, u8> = HashMap::new();
    let mut arrow_counts: HashMap<(u8, u8), usize> = HashMap::new();
    
    // First pass: map files to shards
    for file in files {
        if let Ok(content) = std::fs::read(file) {
            let mut hasher = Sha256::new();
            hasher.update(&content);
            let hash = hasher.finalize();
            let shard = (hash[0] as u64 % 71) as u8;
            
            shard_map.insert(file.to_string_lossy().to_string(), shard);
        }
    }
    
    // Second pass: extract imports and create arrows
    for file in files {
        if let Ok(content) = std::fs::read_to_string(file) {
            let from_shard = shard_map.get(&file.to_string_lossy().to_string()).copied().unwrap_or(0);
            
            // Parse imports
            for line in content.lines() {
                if line.starts_with("import ") {
                    let import = line.strip_prefix("import ").unwrap_or("").trim();
                    
                    // Find target file (simplified - just use hash of import name)
                    let mut hasher = Sha256::new();
                    hasher.update(import.as_bytes());
                    let hash = hasher.finalize();
                    let to_shard = (hash[0] as u64 % 71) as u8;
                    
                    if from_shard != to_shard {
                        *arrow_counts.entry((from_shard, to_shard)).or_insert(0) += 1;
                    }
                }
            }
        }
    }
    
    // Convert to arrow list
    let mut arrows: Vec<Arrow> = arrow_counts.iter()
        .map(|((from, to), weight)| Arrow {
            from_shard: *from,
            to_shard: *to,
            weight: *weight,
        })
        .collect();
    
    arrows.sort_by_key(|a| std::cmp::Reverse(a.weight));
    
    let total_arrows = arrows.len();
    let max_weight = arrows.first().map(|a| a.weight).unwrap_or(0);
    
    ArrowGraph {
        arrows,
        total_arrows,
        max_weight,
    }
}

pub fn print_arrow_graph(graph: &ArrowGraph) {
    println!("Arrow Graph:");
    println!("  Total arrows: {}", graph.total_arrows);
    println!("  Max weight: {}", graph.max_weight);
    println!("\nTop 20 arrows:");
    
    for arrow in graph.arrows.iter().take(20) {
        println!("  Shard {:2} → Shard {:2}: {} imports", 
                 arrow.from_shard, arrow.to_shard, arrow.weight);
    }
}
