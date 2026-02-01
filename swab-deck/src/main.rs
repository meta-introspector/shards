use anyhow::Result;
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use walkdir::WalkDir;
use num_complex::Complex64;

const PRIMES_71: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353,
];

#[derive(Parser)]
#[command(name = "swab-deck")]
#[command(about = "Hecke-Maass sharding for CICADA-71")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Step 1: Inventory all files
    Inventory,
    /// Step 2: Compute Hecke eigenvalues
    Hecke,
    /// Step 3: Apply Maass weights
    Maass,
    /// Step 4: Distribute to 71 shards
    Distribute,
    /// Step 5: Verify reconstruction
    Verify,
    /// Run all steps
    All,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileMetadata {
    path: String,
    size: u64,
    lines: usize,
    hash: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct HeckeEigenvalue {
    file: String,
    shard_id: u8,
    prime: u64,
    eigenvalue_re: f64,
    eigenvalue_im: f64,
    norm: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct MaassWeighted {
    #[serde(flatten)]
    hecke: HeckeEigenvalue,
    maass_weight: f64,
    weighted_norm: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct ShardInfo {
    shard_id: u8,
    prime: u64,
    file_count: usize,
    files: Vec<FileInfo>,
    total_weighted_norm: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileInfo {
    path: String,
    eigenvalue: f64,
    maass_weight: f64,
    weighted_norm: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct Manifest {
    version: String,
    total_files: usize,
    shards: Vec<ShardInfo>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Inventory => step1_inventory()?,
        Commands::Hecke => step2_hecke()?,
        Commands::Maass => step3_maass()?,
        Commands::Distribute => step4_distribute()?,
        Commands::Verify => step5_verify()?,
        Commands::All => {
            println!("╔════════════════════════════════════════════════════════════╗");
            println!("║           SWAB THE DECK - Hecke-Maass Sharding            ║");
            println!("╚════════════════════════════════════════════════════════════╝\n");
            
            step1_inventory()?;
            step2_hecke()?;
            step3_maass()?;
            step4_distribute()?;
            step5_verify()?;
            
            println!("\n╔════════════════════════════════════════════════════════════╗");
            println!("║                    DECK SWABBED ✓                         ║");
            println!("╚════════════════════════════════════════════════════════════╝");
        }
    }

    Ok(())
}

fn step1_inventory() -> Result<()> {
    println!("=== Step 1: Inventory All Files ===");

    let mut files = Vec::new();

    for entry in WalkDir::new(".")
        .into_iter()
        .filter_entry(|e| {
            let path = e.path().to_string_lossy();
            !path.contains("/.git/")
                && !path.contains("/target/")
                && !path.contains("/node_modules/")
                && !path.contains("/.kiro/")
        })
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
    {
        let path = entry.path();
        
        if let Ok(data) = fs::read(path) {
            let size = data.len() as u64;
            let lines = data.iter().filter(|&&b| b == b'\n').count();
            let hash = format!("{:x}", Sha256::digest(&data));

            files.push(FileMetadata {
                path: path.to_string_lossy().to_string(),
                size,
                lines,
                hash,
            });
        }
    }

    println!("Found {} files", files.len());

    fs::write(
        "file_metadata.json",
        serde_json::to_string_pretty(&files)?,
    )?;

    println!("Saved to file_metadata.json");
    Ok(())
}

fn step2_hecke() -> Result<()> {
    println!("\n=== Step 2: Compute Hecke Eigenvalues ===");

    let files: Vec<FileMetadata> = serde_json::from_str(&fs::read_to_string("file_metadata.json")?)?;

    let mut eigenvalues = Vec::new();

    for file in files {
        let hash_bytes = hex::decode(&file.hash)?;
        let shard_id = ((file.lines * 7 + file.size as usize * 3 + u64::from_be_bytes(hash_bytes[..8].try_into()?)) % 71) as u8;

        let re_bytes = u64::from_be_bytes(hash_bytes[0..8].try_into()?);
        let im_bytes = u64::from_be_bytes(hash_bytes[8..16].try_into()?);

        let re = (re_bytes % 10000) as f64 / 10000.0 * 2.0 - 1.0;
        let im = (im_bytes % 10000) as f64 / 10000.0 * 2.0 - 1.0;

        let p = PRIMES_71[shard_id as usize];
        let scale = 2.0 * (p as f64).sqrt();

        let norm = (re * re + im * im).sqrt() * scale;

        eigenvalues.push(HeckeEigenvalue {
            file: file.path.clone(),
            shard_id,
            prime: p,
            eigenvalue_re: re * scale,
            eigenvalue_im: im * scale,
            norm,
        });

        println!("File: {:50} → Shard {:2} (λ = {:.3})", 
                 file.path.chars().take(50).collect::<String>(), 
                 shard_id, 
                 norm);
    }

    fs::write(
        "hecke_eigenvalues.json",
        serde_json::to_string_pretty(&eigenvalues)?,
    )?;

    println!("\nComputed {} Hecke eigenvalues", eigenvalues.len());
    println!("Saved to hecke_eigenvalues.json");
    Ok(())
}

fn step3_maass() -> Result<()> {
    println!("\n=== Step 3: Apply Maass Weights ===");

    let eigenvalues: Vec<HeckeEigenvalue> = 
        serde_json::from_str(&fs::read_to_string("hecke_eigenvalues.json")?)?;

    let mut weighted = Vec::new();

    for eigen in eigenvalues {
        let n = eigen.shard_id as usize + 1;
        let weight = maass_weight(eigen.eigenvalue_im, n);
        let weighted_norm = eigen.norm * weight;

        weighted.push(MaassWeighted {
            hecke: eigen.clone(),
            maass_weight: weight,
            weighted_norm,
        });

        println!("Shard {:2}: λ = {:6.3}, K_ir = {:6.3}, weighted = {:6.3}",
                 eigen.shard_id, eigen.norm, weight, weighted_norm);
    }

    fs::write(
        "maass_weighted.json",
        serde_json::to_string_pretty(&weighted)?,
    )?;

    println!("\nApplied Maass weights to {} files", weighted.len());
    println!("Saved to maass_weighted.json");
    Ok(())
}

fn maass_weight(r: f64, n: usize) -> f64 {
    let arg = 2.0 * std::f64::consts::PI * n as f64;
    (-arg / (1.0 + r.abs())).exp()
}

fn step4_distribute() -> Result<()> {
    println!("\n=== Step 4: Distribute to 71 Shards ===");

    let weighted: Vec<MaassWeighted> = 
        serde_json::from_str(&fs::read_to_string("maass_weighted.json")?)?;

    let mut shards: HashMap<u8, Vec<MaassWeighted>> = HashMap::new();
    for w in weighted {
        shards.entry(w.hecke.shard_id).or_insert_with(Vec::new).push(w);
    }

    let mut manifest = Manifest {
        version: "1.0".to_string(),
        total_files: shards.values().map(|v| v.len()).sum(),
        shards: Vec::new(),
    };

    for shard_id in 0..71 {
        let files = shards.get(&shard_id).cloned().unwrap_or_default();
        let total_weighted_norm: f64 = files.iter().map(|f| f.weighted_norm).sum();

        let shard_info = ShardInfo {
            shard_id,
            prime: PRIMES_71[shard_id as usize],
            file_count: files.len(),
            files: files.iter().map(|f| FileInfo {
                path: f.hecke.file.clone(),
                eigenvalue: f.hecke.norm,
                maass_weight: f.maass_weight,
                weighted_norm: f.weighted_norm,
            }).collect(),
            total_weighted_norm,
        };

        println!("Shard {:2}: {:3} files, total weight = {:8.3}",
                 shard_id, files.len(), total_weighted_norm);

        manifest.shards.push(shard_info);
    }

    fs::write(
        "HECKE_MAASS_MANIFEST.json",
        serde_json::to_string_pretty(&manifest)?,
    )?;

    println!("\nDistributed {} files across 71 shards", manifest.total_files);
    println!("Saved to HECKE_MAASS_MANIFEST.json");

    let file_counts: Vec<usize> = manifest.shards.iter().map(|s| s.file_count).collect();
    println!("\nStatistics:");
    println!("  Min files per shard: {}", file_counts.iter().min().unwrap_or(&0));
    println!("  Max files per shard: {}", file_counts.iter().max().unwrap_or(&0));
    println!("  Avg files per shard: {:.1}", file_counts.iter().sum::<usize>() as f64 / 71.0);

    Ok(())
}

fn step5_verify() -> Result<()> {
    println!("\n=== Step 5: Verify Reconstruction ===");

    let manifest: Manifest = 
        serde_json::from_str(&fs::read_to_string("HECKE_MAASS_MANIFEST.json")?)?;

    let mut verified = 0;
    let mut errors = Vec::new();

    for shard in &manifest.shards {
        for file_info in &shard.files {
            if PathBuf::from(&file_info.path).exists() {
                verified += 1;
            } else {
                errors.push(format!("Shard {}: {} - File not found", shard.shard_id, file_info.path));
            }
        }
    }

    println!("\nVerified {}/{} files", verified, manifest.total_files);
    
    if !errors.is_empty() {
        println!("Errors: {}", errors.len());
        for err in errors.iter().take(10) {
            println!("  {}", err);
        }
    } else {
        println!("✓ All files verified");
    }

    // Verify distribution
    let file_counts: Vec<usize> = manifest.shards.iter().map(|s| s.file_count).collect();
    let avg = file_counts.iter().sum::<usize>() as f64 / 71.0;
    let variance: f64 = file_counts.iter()
        .map(|&c| (c as f64 - avg).powi(2))
        .sum::<f64>() / 71.0;

    println!("\nVerifying harmonic distribution...");
    println!("  Average files per shard: {:.1}", avg);
    println!("  Variance: {:.1}", variance);
    println!("  Distribution: {}", if variance < avg { "balanced" } else { "unbalanced" });

    if errors.is_empty() && variance < avg {
        println!("✓ Harmonic distribution: OK");
    }

    println!("\n{}", "=".repeat(60));
    println!("SWAB THE DECK COMPLETE");
    println!("{}", "=".repeat(60));
    println!("Total files: {}", manifest.total_files);
    println!("Shards: 71");
    println!("Status: {}", if errors.is_empty() { "PASS" } else { "FAIL" });

    Ok(())
}
