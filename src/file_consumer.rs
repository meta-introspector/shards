use serde::{Deserialize, Serialize};
use std::path::Path;
use std::process::Command;

#[derive(Debug, Serialize, Deserialize)]
pub struct FileReasoning {
    pub path: String,
    pub total_functions: usize,
    pub tower_height: u64,
    pub avg_complexity: f64,
    pub max_complexity: u64,
    pub shard: u8,
}

pub fn consume_file(path: &Path) -> Result<FileReasoning, Box<dyn std::error::Error>> {
    // Call Lean4 with FileConsumer
    let output = Command::new("lean")
        .arg("--plugin=FileConsumer")
        .arg(path)
        .output()?;
    
    let stdout = String::from_utf8_lossy(&output.stdout);
    
    // Parse output
    let mut total_functions = 0;
    let mut tower_height = 0;
    let mut avg_complexity = 0.0;
    let mut max_complexity = 0;
    
    for line in stdout.lines() {
        if line.contains("Functions:") {
            total_functions = line.split(':').nth(1)
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(0);
        } else if line.contains("Tower Height:") {
            tower_height = line.split(':').nth(1)
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(0);
        } else if line.contains("Avg Complexity:") {
            avg_complexity = line.split(':').nth(1)
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(0.0);
        } else if line.contains("Max Complexity:") {
            max_complexity = line.split(':').nth(1)
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(0);
        }
    }
    
    let shard = (tower_height % 71) as u8;
    
    Ok(FileReasoning {
        path: path.to_string_lossy().to_string(),
        total_functions,
        tower_height,
        avg_complexity,
        max_complexity,
        shard,
    })
}

pub fn reason_about_corpus(paths: &[&Path]) -> Vec<FileReasoning> {
    paths.iter()
        .filter_map(|p| consume_file(p).ok())
        .collect()
}
