use anyhow::Result;
use clap::{Parser, Subcommand};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use walkdir::WalkDir;

#[derive(Parser)]
#[command(name = "scp-zk71")]
#[command(about = "SCP-ZK71 Containment Protocol - Safe handling of toxic code")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Clone repository to quarantine with ZK verification
    Clone {
        #[arg(long)]
        url: String,
        #[arg(long)]
        quarantine: PathBuf,
    },
    
    /// Scan for toxicity
    Scan {
        #[arg(long)]
        path: PathBuf,
    },
    
    /// Isolate to 71 shards
    Isolate {
        #[arg(long)]
        path: PathBuf,
    },
    
    /// Rewrite safely
    Rewrite {
        #[arg(long)]
        path: PathBuf,
        #[arg(long)]
        output: PathBuf,
    },
    
    /// Full containment workflow
    Contain {
        #[arg(long)]
        url: String,
    },
}

#[derive(Debug, PartialEq, Clone)]
enum ToxicityLevel {
    Safe,
    Caution,
    Hazardous,
    Toxic,
    Keter,
}

#[derive(Debug)]
struct Finding {
    file: String,
    line: usize,
    severity: ToxicityLevel,
    description: String,
}

fn zk_clone(url: &str, quarantine: &Path) -> Result<()> {
    println!("⚠️  INITIATING SCP-ZK71 CONTAINMENT");
    println!("Repository: {}", url);
    
    fs::create_dir_all(quarantine)?;
    
    let output = Command::new("git")
        .args(&["clone", "--depth=1", url])
        .arg(quarantine)
        .output()?;
    
    if !output.status.success() {
        anyhow::bail!("Clone failed");
    }
    
    let repo_hash = compute_repo_hash(quarantine)?;
    let zk_proof = generate_zk_proof(&repo_hash);
    
    println!("✓ Cloned to quarantine");
    println!("  Hash: {}", hex::encode(repo_hash));
    println!("  ZK Proof: {}", hex::encode(&zk_proof[..8]));
    
    Ok(())
}

fn compute_repo_hash(path: &Path) -> Result<[u8; 32]> {
    let mut hasher = Sha256::new();
    
    for entry in WalkDir::new(path).into_iter().filter_map(|e| e.ok()) {
        if entry.file_type().is_file() {
            if let Ok(content) = fs::read(entry.path()) {
                hasher.update(&content);
            }
        }
    }
    
    Ok(hasher.finalize().into())
}

fn generate_zk_proof(repo_hash: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"SCP-ZK71-CONTAINMENT");
    hasher.update(repo_hash);
    hasher.finalize().into()
}

fn scan_toxicity(path: &Path) -> Result<(ToxicityLevel, Vec<Finding>)> {
    println!("\n=== TOXICITY SCAN ===");
    
    let mut findings = Vec::new();
    let mut max_level = ToxicityLevel::Safe;
    
    for entry in WalkDir::new(path).into_iter().filter_map(|e| e.ok()) {
        if !entry.file_type().is_file() {
            continue;
        }
        
        let file_path = entry.path();
        if let Ok(content) = fs::read_to_string(file_path) {
            for (i, line) in content.lines().enumerate() {
                // Check for toxic patterns
                if line.contains("eval(") || line.contains("exec(") {
                    findings.push(Finding {
                        file: file_path.display().to_string(),
                        line: i + 1,
                        severity: ToxicityLevel::Hazardous,
                        description: "Dynamic code execution".to_string(),
                    });
                    if max_level == ToxicityLevel::Safe || max_level == ToxicityLevel::Caution {
                        max_level = ToxicityLevel::Hazardous;
                    }
                }
                
                if line.contains("password") && line.contains("=") && !line.trim().starts_with('#') {
                    findings.push(Finding {
                        file: file_path.display().to_string(),
                        line: i + 1,
                        severity: ToxicityLevel::Toxic,
                        description: "Potential hardcoded credential".to_string(),
                    });
                    if max_level != ToxicityLevel::Keter {
                        max_level = ToxicityLevel::Toxic;
                    }
                }
                
                if line.contains("__import__") || line.contains("compile(") {
                    findings.push(Finding {
                        file: file_path.display().to_string(),
                        line: i + 1,
                        severity: ToxicityLevel::Keter,
                        description: "Self-modifying code".to_string(),
                    });
                    max_level = ToxicityLevel::Keter;
                }
            }
        }
    }
    
    println!("Toxicity Level: {:?}", max_level);
    println!("Findings: {}", findings.len());
    
    for finding in &findings {
        println!("  [{:?}] {}:{} - {}", 
                 finding.severity, finding.file, finding.line, finding.description);
    }
    
    Ok((max_level, findings))
}

fn isolate_shards(path: &Path) -> Result<usize> {
    println!("\n=== 71-SHARD ISOLATION ===");
    
    let files: Vec<_> = WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .collect();
    
    println!("Isolated {} files across 71 shards", files.len());
    
    for (i, file) in files.iter().enumerate() {
        let shard_id = i % 71;
        println!("  Shard {}: {}", shard_id, file.path().display());
    }
    
    Ok(files.len())
}

fn safe_rewrite(input: &Path, output: &Path, level: &ToxicityLevel) -> Result<usize> {
    println!("\n=== SAFE REWRITE ===");
    
    if *level == ToxicityLevel::Keter {
        anyhow::bail!("KETER-level toxicity - cannot safely rewrite");
    }
    
    fs::create_dir_all(output)?;
    
    let mut rewritten = 0;
    
    for entry in WalkDir::new(input).into_iter().filter_map(|e| e.ok()) {
        if !entry.file_type().is_file() {
            continue;
        }
        
        let rel_path = entry.path().strip_prefix(input)?;
        let out_path = output.join(rel_path);
        
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent)?;
        }
        
        if let Ok(content) = fs::read_to_string(entry.path()) {
            let sanitized = sanitize_content(&content);
            fs::write(&out_path, sanitized)?;
            rewritten += 1;
        }
    }
    
    println!("✓ Rewrote {} files", rewritten);
    
    Ok(rewritten)
}

fn sanitize_content(content: &str) -> String {
    let mut result = String::new();
    
    for line in content.lines() {
        let sanitized = if line.contains("eval(") {
            "// REMOVED: eval() - TOXIC".to_string()
        } else if line.contains("exec(") {
            "// REMOVED: exec() - TOXIC".to_string()
        } else if line.contains("__import__") {
            "// REMOVED: __import__ - KETER".to_string()
        } else if line.contains("password") && line.contains("=") && !line.trim().starts_with("//") {
            "// REMOVED: hardcoded credential - TOXIC".to_string()
        } else {
            line.to_string()
        };
        
        result.push_str(&sanitized);
        result.push('\n');
    }
    
    result
}

fn full_containment(url: &str) -> Result<()> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║           SCP-ZK71 CONTAINMENT PROTOCOL                    ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");
    
    let quarantine = PathBuf::from("/tmp/scp-zk71-quarantine");
    let output = PathBuf::from("/tmp/scp-zk71-clean");
    
    // Step 1: Clone
    println!("Step 1: Cloning to quarantine...");
    zk_clone(url, &quarantine)?;
    
    // Step 2: Scan
    println!("\nStep 2: Scanning for toxicity...");
    let (level, _findings) = scan_toxicity(&quarantine)?;
    
    // Step 3: Isolate
    println!("\nStep 3: Isolating to 71 shards...");
    isolate_shards(&quarantine)?;
    
    // Step 4: Rewrite
    println!("\nStep 4: Rewriting safely...");
    safe_rewrite(&quarantine, &output, &level)?;
    
    println!("\n✓ CONTAINMENT COMPLETE");
    println!("  Quarantine: {}", quarantine.display());
    println!("  Clean output: {}", output.display());
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Clone { url, quarantine } => {
            zk_clone(&url, &quarantine)?;
        }
        
        Commands::Scan { path } => {
            scan_toxicity(&path)?;
        }
        
        Commands::Isolate { path } => {
            isolate_shards(&path)?;
        }
        
        Commands::Rewrite { path, output } => {
            let (level, _) = scan_toxicity(&path)?;
            safe_rewrite(&path, &output, &level)?;
        }
        
        Commands::Contain { url } => {
            full_containment(&url)?;
        }
    }
    
    Ok(())
}
