use clap::{Parser, Subcommand};
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use std::process::Command;

mod vertex_ops;
use vertex_ops::VertexOp;

#[derive(Parser)]
#[command(name = "git71")]
#[command(about = "Git reimagined with 71-shard Monster algebra", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Shard all git objects by mod 71
    Shard,
    /// Show commit with vertex operator
    Show { hash: String },
    /// Log with 23-vertex algebra annotations
    Log { #[arg(short, long, default_value_t = 10)] count: usize },
    /// Commit with vertex operator tagging
    Commit { message: String },
}

#[derive(Debug, Serialize, Deserialize)]
struct GitObject {
    hash: String,
    shard: u8,
    vertex_op: String,
    emoji: String,
}

fn shard_hash(hash: &str) -> u8 {
    let mut hasher = Sha256::new();
    hasher.update(hash.as_bytes());
    let result = hasher.finalize();
    let hash_num = u64::from_be_bytes([
        result[0], result[1], result[2], result[3],
        result[4], result[5], result[6], result[7],
    ]);
    (hash_num % 71) as u8
}

fn hash_to_vertex(hash: &str) -> VertexOp {
    let shard = shard_hash(hash);
    VertexOp::from_prime(shard).unwrap_or(VertexOp::N)
}

fn hash_to_emoji(hash: &str) -> String {
    let shard = shard_hash(hash);
    let emojis = ["🔥", "❄️", "⚡", "💧", "🌊", "🌪️", "☀️", "🌙", 
                  "🧠", "💭", "🎯", "🔮", "✨", "🌌", "🎭", "🎨"];
    emojis[(shard % 16) as usize].to_string()
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Shard => {
            println!("🔮 git71: Sharding repository by mod 71");
            
            let output = Command::new("git")
                .args(&["rev-list", "--all", "--objects"])
                .output()
                .expect("Failed to execute git");
            
            let objects: Vec<GitObject> = String::from_utf8_lossy(&output.stdout)
                .lines()
                .filter(|line| !line.is_empty())
                .map(|line| {
                    let hash = line.split_whitespace().next().unwrap_or("");
                    let shard = shard_hash(hash);
                    let vertex_op = hash_to_vertex(hash);
                    
                    GitObject {
                        hash: hash.to_string(),
                        shard,
                        vertex_op: format!("{:?}", vertex_op),
                        emoji: hash_to_emoji(hash),
                    }
                })
                .collect();
            
            println!("📊 Total objects: {}", objects.len());
            println!("💾 Saving to git71_shards.json");
            
            std::fs::write(
                "git71_shards.json",
                serde_json::to_string_pretty(&objects).unwrap()
            ).unwrap();
        }
        
        Commands::Show { hash } => {
            let shard = shard_hash(&hash);
            let vertex_op = hash_to_vertex(&hash);
            let emoji = hash_to_emoji(&hash);
            
            println!("{} Shard: {} | Vertex: {:?}", emoji, shard, vertex_op);
            
            Command::new("git")
                .args(&["show", &hash])
                .status()
                .expect("Failed to execute git show");
        }
        
        Commands::Log { count } => {
            let output = Command::new("git")
                .args(&["log", &format!("-{}", count), "--oneline"])
                .output()
                .expect("Failed to execute git log");
            
            println!("🌌 git71 log (23-vertex algebra):\n");
            
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                let hash = line.split_whitespace().next().unwrap_or("");
                let emoji = hash_to_emoji(hash);
                let vertex_op = hash_to_vertex(hash);
                let shard = shard_hash(hash);
                
                println!("{} [{}] {:?} {}", emoji, shard, vertex_op, line);
            }
        }
        
        Commands::Commit { message } => {
            let output = Command::new("git")
                .args(&["commit", "-m", &message])
                .output()
                .expect("Failed to execute git commit");
            
            if output.status.success() {
                // Get the new commit hash
                let hash_output = Command::new("git")
                    .args(&["rev-parse", "HEAD"])
                    .output()
                    .expect("Failed to get commit hash");
                
                let hash = String::from_utf8_lossy(&hash_output.stdout).trim().to_string();
                let shard = shard_hash(&hash);
                let vertex_op = hash_to_vertex(&hash);
                let emoji = hash_to_emoji(&hash);
                
                println!("{} Committed to shard {} with vertex {:?}", emoji, shard, vertex_op);
                println!("Hash: {}", hash);
            }
        }
    }
}
