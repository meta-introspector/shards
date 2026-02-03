use std::collections::HashMap;
use std::path::{Path, PathBuf};
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct LeanAnalysis {
    pub total_files: usize,
    pub shards_used: usize,
    pub top_shards: Vec<ShardInfo>,
    pub similar_pairs: Vec<SimilarPair>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ShardInfo {
    pub shard: u8,
    pub count: usize,
    pub files: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SimilarPair {
    pub file1: String,
    pub file2: String,
    pub shard: u8,
    pub similarity: f64,
}

pub fn analyze_all_lean(root: &Path) -> Result<LeanAnalysis, Box<dyn std::error::Error>> {
    let mut shard_map: HashMap<u8, Vec<PathBuf>> = HashMap::new();
    let mut total = 0;
    
    // Find all .lean files
    for entry in walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "lean"))
    {
        let path = entry.path();
        if let Ok(content) = std::fs::read(path) {
            let mut hasher = Sha256::new();
            hasher.update(&content);
            let hash = hasher.finalize();
            let shard = (hash[0] as u64 % 71) as u8;
            
            shard_map.entry(shard).or_insert_with(Vec::new).push(path.to_path_buf());
            total += 1;
        }
    }
    
    // Top 10 shards
    let mut top_shards: Vec<_> = shard_map.iter()
        .map(|(shard, files)| (*shard, files.len()))
        .collect();
    top_shards.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
    
    let top_shards: Vec<ShardInfo> = top_shards.iter()
        .take(10)
        .map(|(shard, count)| ShardInfo {
            shard: *shard,
            count: *count,
            files: shard_map[shard].iter()
                .take(5)
                .map(|p| p.to_string_lossy().to_string())
                .collect(),
        })
        .collect();
    
    // Find similar pairs (same shard)
    let mut similar_pairs = Vec::new();
    for (shard, files) in &shard_map {
        if files.len() >= 2 {
            for i in 0..files.len().min(3) {
                for j in (i+1)..files.len().min(3) {
                    similar_pairs.push(SimilarPair {
                        file1: files[i].to_string_lossy().to_string(),
                        file2: files[j].to_string_lossy().to_string(),
                        shard: *shard,
                        similarity: 1.0, // Same shard = high similarity
                    });
                }
            }
        }
    }
    
    Ok(LeanAnalysis {
        total_files: total,
        shards_used: shard_map.len(),
        top_shards,
        similar_pairs: similar_pairs.into_iter().take(20).collect(),
    })
}
