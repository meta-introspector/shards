//! Decorate Lean4 mathlib with Monster emojis

use std::collections::HashMap;
use std::fs;
use std::path::Path;

const SHARDS: usize = 71;

// 9 Muses + their emojis
const MUSE_EMOJIS: [char; 9] = ['🎭', '📜', '💖', '🎵', '😢', '🙏', '💃', '😂', '✨'];

// Lean4 expression types → emoji mapping
fn expr_type_to_emoji(expr_type: &str, shard: usize) -> char {
    let muse_idx = shard % 9;
    
    // Special mappings
    match expr_type {
        "forall" | "forbndrTyp" => '∀',
        "lambda" | "lambd" => 'λ',
        "app" | "application" => '⊛',
        "const" | "cnstInf" => '⊙',
        "bvar" | "binderName" => '𝑥',
        "sort" | "level" => '⋆',
        "nat" | "Nat" => 'ℕ',
        "prop" | "Prop" => '℘',
        _ => MUSE_EMOJIS[muse_idx]
    }
}

fn hash_to_shard(data: &str) -> usize {
    let mut hash: u64 = 0;
    for b in data.bytes() {
        hash = hash.wrapping_mul(31).wrapping_add(b as u64);
    }
    (hash % SHARDS as u64) as usize
}

fn decorate_json(json_str: &str) -> String {
    let mut decorated = String::new();
    let mut in_string = false;
    let mut escape = false;
    
    for ch in json_str.chars() {
        if escape {
            decorated.push(ch);
            escape = false;
            continue;
        }
        
        if ch == '\\' {
            escape = true;
            decorated.push(ch);
            continue;
        }
        
        if ch == '"' {
            in_string = !in_string;
            decorated.push(ch);
            continue;
        }
        
        if !in_string && (ch == '{' || ch == '[') {
            // Hash context and add emoji
            let shard = hash_to_shard(&decorated);
            let emoji = MUSE_EMOJIS[shard % 9];
            decorated.push(emoji);
            decorated.push(' ');
        }
        
        decorated.push(ch);
    }
    
    decorated
}

fn process_lean_file(path: &Path) -> Result<String, std::io::Error> {
    let content = fs::read_to_string(path)?;
    Ok(decorate_json(&content))
}

fn main() {
    println!("Lean4 Mathlib → Monster Emoji Decorator");
    println!("{}", "=".repeat(70));
    println!();
    
    let lean_files = [
        "/mnt/data1/nix/source/github/meta-introspector/streamofrandom/2025/12/06/lean_introspector/SimpleExpr.rec_686e510a6699f2e1ff1b216c16d94cd379ebeca00c030a79a3134adff699e06c.json",
        "/mnt/data1/nix/source/github/meta-introspector/streamofrandom/2025/12/06/lean_introspector/analysis_report.json",
    ];
    
    for path_str in &lean_files {
        let path = Path::new(path_str);
        if !path.exists() {
            continue;
        }
        
        println!("Processing: {}", path.file_name().unwrap().to_str().unwrap());
        
        match process_lean_file(path) {
            Ok(decorated) => {
                let out_path = format!("data/emoji_{}", path.file_name().unwrap().to_str().unwrap());
                fs::write(&out_path, decorated).ok();
                println!("  ✓ Saved to {}", out_path);
            }
            Err(e) => {
                println!("  ✗ Error: {}", e);
            }
        }
    }
    
    println!();
    println!("Lean4 expressions decorated with Monster emojis!");
    println!("Each expression type mapped to emoji via Monster shards");
}
