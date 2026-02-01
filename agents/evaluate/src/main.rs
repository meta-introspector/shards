// Universal Agent Evaluator in Rust
// agents/evaluate/src/main.rs

use serde::{Deserialize, Serialize};
use std::fs;
use std::time::Instant;
use anyhow::Result;
use clap::Parser;

#[derive(Debug, Serialize, Deserialize)]
struct ShardChallenge {
    shard_id: u16,
    category: String,
    base_challenge: String,
    micro_challenge: String,
    difficulty: u8,
    zk_circuit_type: String,
    points: u64,
}

#[derive(Debug, Serialize, Deserialize)]
struct EvalResult {
    framework: String,
    shard_id: u16,
    category: String,
    difficulty: u8,
    points: u64,
    success: bool,
    solution: String,
    error: String,
    time_seconds: f64,
    timestamp: u64,
}

#[derive(Parser)]
struct Args {
    #[arg(long)]
    framework: String,
    #[arg(long)]
    shard: u16,
    #[arg(long, default_value = "results")]
    output: String,
}

fn load_challenge(shard_id: u16) -> Result<ShardChallenge> {
    let data = fs::read_to_string("shard_challenges.json")?;
    let challenges: Vec<ShardChallenge> = serde_json::from_str(&data)?;
    challenges.into_iter()
        .find(|c| c.shard_id == shard_id)
        .ok_or_else(|| anyhow::anyhow!("Shard {} not found", shard_id))
}

fn get_prompt(challenge: &ShardChallenge) -> String {
    format!(
        "Solve this challenge:\n\n\
         Category: {}\n\
         Challenge: {}\n\
         Difficulty: {}/10\n\
         Points: {}\n\n\
         Provide your solution and generate a ZK proof.",
        challenge.category,
        challenge.micro_challenge,
        challenge.difficulty,
        challenge.points
    )
}

async fn run_claude(prompt: &str) -> Result<String> {
    let client = reqwest::Client::new();
    let api_key = std::env::var("ANTHROPIC_API_KEY")?;
    
    let body = serde_json::json!({
        "model": "claude-3-5-sonnet-20241022",
        "max_tokens": 4096,
        "messages": [{"role": "user", "content": prompt}]
    });
    
    let response = client
        .post("https://api.anthropic.com/v1/messages")
        .header("x-api-key", api_key)
        .header("anthropic-version", "2023-06-01")
        .json(&body)
        .send()
        .await?;
    
    let data: serde_json::Value = response.json().await?;
    Ok(data["content"][0]["text"].as_str().unwrap_or("").to_string())
}

async fn run_openai(prompt: &str) -> Result<String> {
    let client = reqwest::Client::new();
    let api_key = std::env::var("OPENAI_API_KEY")?;
    
    let body = serde_json::json!({
        "model": "gpt-4",
        "messages": [{"role": "user", "content": prompt}]
    });
    
    let response = client
        .post("https://api.openai.com/v1/chat/completions")
        .header("Authorization", format!("Bearer {}", api_key))
        .json(&body)
        .send()
        .await?;
    
    let data: serde_json::Value = response.json().await?;
    Ok(data["choices"][0]["message"]["content"].as_str().unwrap_or("").to_string())
}

async fn run_ollama(prompt: &str) -> Result<String> {
    let client = reqwest::Client::new();
    
    let body = serde_json::json!({
        "model": "llama3.1",
        "messages": [{"role": "user", "content": prompt}],
        "stream": false
    });
    
    let response = client
        .post("http://localhost:11434/api/chat")
        .json(&body)
        .send()
        .await?;
    
    let data: serde_json::Value = response.json().await?;
    Ok(data["message"]["content"].as_str().unwrap_or("").to_string())
}

async fn run_agent(framework: &str, prompt: &str) -> Result<String> {
    match framework {
        "claude" => run_claude(prompt).await,
        "openai" => run_openai(prompt).await,
        "ollama" => run_ollama(prompt).await,
        _ => Err(anyhow::anyhow!("Framework {} not implemented", framework)),
    }
}

async fn evaluate(framework: &str, shard_id: u16) -> Result<EvalResult> {
    let challenge = load_challenge(shard_id)?;
    let prompt = get_prompt(&challenge);
    
    let start = Instant::now();
    let result = run_agent(framework, &prompt).await;
    let elapsed = start.elapsed().as_secs_f64();
    
    let (success, solution, error) = match result {
        Ok(sol) => (true, sol, String::new()),
        Err(e) => (false, String::new(), e.to_string()),
    };
    
    Ok(EvalResult {
        framework: framework.to_string(),
        shard_id,
        category: challenge.category,
        difficulty: challenge.difficulty,
        points: challenge.points,
        success,
        solution,
        error,
        time_seconds: elapsed,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
    })
}

#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();
    
    println!("🤖 Evaluating {} on shard {}...", args.framework, args.shard);
    
    let result = evaluate(&args.framework, args.shard).await?;
    
    // Save result
    fs::create_dir_all(&args.output)?;
    let output_file = format!("{}/{}_{:03}.json", args.output, args.framework, args.shard);
    let json = serde_json::to_string_pretty(&result)?;
    fs::write(&output_file, json)?;
    
    if result.success {
        println!("✅ Success! Time: {:.2}s", result.time_seconds);
        println!("📄 Saved to: {}", output_file);
    } else {
        println!("❌ Failed: {}", result.error);
    }
    
    Ok(())
}
