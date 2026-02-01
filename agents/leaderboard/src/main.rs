// Leaderboard Generator in Rust
// agents/leaderboard/src/main.rs

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use anyhow::Result;

#[derive(Debug, Deserialize)]
struct EvalResult {
    framework: String,
    shard_id: u16,
    category: String,
    difficulty: u8,
    points: u64,
    success: bool,
    time_seconds: f64,
}

#[derive(Debug, Default)]
struct FrameworkScore {
    total_points: u64,
    shards_completed: u32,
    total_time: f64,
    total_attempts: u32,
    total_difficulty: u32,
}

impl FrameworkScore {
    fn success_rate(&self) -> f64 {
        if self.total_attempts == 0 {
            0.0
        } else {
            self.shards_completed as f64 / self.total_attempts as f64
        }
    }
    
    fn avg_time(&self) -> f64 {
        if self.shards_completed == 0 {
            0.0
        } else {
            self.total_time / self.shards_completed as f64
        }
    }
    
    fn avg_difficulty(&self) -> f64 {
        if self.shards_completed == 0 {
            0.0
        } else {
            self.total_difficulty as f64 / self.shards_completed as f64
        }
    }
}

fn load_results(dir: &str) -> Result<Vec<EvalResult>> {
    let mut results = Vec::new();
    
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        
        if path.extension().and_then(|s| s.to_str()) == Some("json") {
            let data = fs::read_to_string(&path)?;
            if let Ok(result) = serde_json::from_str::<EvalResult>(&data) {
                results.push(result);
            }
        }
    }
    
    Ok(results)
}

fn calculate_scores(results: &[EvalResult]) -> HashMap<String, FrameworkScore> {
    let mut scores: HashMap<String, FrameworkScore> = HashMap::new();
    
    for r in results {
        let score = scores.entry(r.framework.clone()).or_default();
        score.total_attempts += 1;
        
        if r.success {
            score.total_points += r.points;
            score.shards_completed += 1;
            score.total_time += r.time_seconds;
            score.total_difficulty += r.difficulty as u32;
        }
    }
    
    scores
}

fn generate_leaderboard(scores: &HashMap<String, FrameworkScore>) -> String {
    let mut sorted: Vec<_> = scores.iter().collect();
    sorted.sort_by(|a, b| b.1.total_points.cmp(&a.1.total_points));
    
    let mut md = String::from("# 71-Shard Challenge Leaderboard\n\n");
    md.push_str("## Overall Rankings\n\n");
    md.push_str("| Rank | Framework | Points | Shards | Success Rate | Avg Time | Avg Difficulty |\n");
    md.push_str("|------|-----------|--------|--------|--------------|----------|----------------|\n");
    
    for (rank, (fw, score)) in sorted.iter().enumerate() {
        md.push_str(&format!(
            "| {} | {} | {:,} | {} | {:.1}% | {:.2}s | {:.1}/10 |\n",
            rank + 1,
            fw,
            score.total_points,
            score.shards_completed,
            score.success_rate() * 100.0,
            score.avg_time(),
            score.avg_difficulty()
        ));
    }
    
    md
}

fn generate_category_breakdown(results: &[EvalResult]) -> String {
    let mut categories: HashMap<String, HashMap<String, u32>> = HashMap::new();
    
    for r in results {
        if r.success {
            categories
                .entry(r.category.clone())
                .or_default()
                .entry(r.framework.clone())
                .and_modify(|c| *c += 1)
                .or_insert(1);
        }
    }
    
    let mut md = String::from("\n## Performance by Category\n\n");
    
    for cat in ["Cryptography", "Encryption", "Prompt Injection", 
                "Multi-Agent", "Reverse Engineering", "Economic Security", "Meta-Challenge"] {
        if let Some(cat_data) = categories.get(cat) {
            md.push_str(&format!("\n### {}\n\n", cat));
            md.push_str("| Framework | Completed |\n");
            md.push_str("|-----------|----------|\n");
            
            let mut sorted: Vec<_> = cat_data.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            
            for (fw, count) in sorted {
                md.push_str(&format!("| {} | {} |\n", fw, count));
            }
        }
    }
    
    md
}

fn main() -> Result<()> {
    println!("📊 Generating leaderboard...");
    
    let results = load_results("results")?;
    println!("   Loaded {} results", results.len());
    
    let scores = calculate_scores(&results);
    
    let mut leaderboard = generate_leaderboard(&scores);
    leaderboard.push_str(&generate_category_breakdown(&results));
    
    fs::write("LEADERBOARD.md", &leaderboard)?;
    
    println!("✅ Leaderboard saved to LEADERBOARD.md");
    println!("\n{}", leaderboard);
    
    Ok(())
}
