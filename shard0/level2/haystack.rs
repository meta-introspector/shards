use std::fs;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

const PRIMES_71: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353,
];

// j-invariant needle: key coefficients to search for
const J_NEEDLE: [&str; 5] = [
    "744",       // Constant term
    "196883",    // Monster dimension
    "196884",    // Monster dimension + 1
    "21493760",  // q^2 coefficient
    "j-invariant",
];

struct Match {
    tape: String,
    line: usize,
    text: String,
    coefficient: String,
}

fn search_tape(path: &Path) -> io::Result<Vec<Match>> {
    let file = fs::File::open(path)?;
    let reader = BufReader::new(file);
    let mut matches = Vec::new();
    
    let tape_name = path.file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("unknown")
        .to_string();
    
    for (line_num, line) in reader.lines().enumerate() {
        let line = line?;
        let line_lower = line.to_lowercase();
        
        for &needle in &J_NEEDLE {
            if line_lower.contains(&needle.to_lowercase()) {
                matches.push(Match {
                    tape: tape_name.clone(),
                    line: line_num + 1,
                    text: line.clone(),
                    coefficient: needle.to_string(),
                });
            }
        }
    }
    
    Ok(matches)
}

fn search_all_tapes(tape_dir: &str) -> io::Result<Vec<Match>> {
    let mut all_matches = Vec::new();
    
    for entry in fs::read_dir(tape_dir)? {
        let entry = entry?;
        let path = entry.path();
        
        if path.extension().and_then(|s| s.to_str()) == Some("dat") {
            match search_tape(&path) {
                Ok(mut matches) => all_matches.append(&mut matches),
                Err(e) => eprintln!("Error reading {:?}: {}", path, e),
            }
        }
    }
    
    Ok(all_matches)
}

fn main() -> io::Result<()> {
    println!("CICADA-71 Level 2: Find j-Invariant in Haystack");
    println!("================================================\n");
    
    println!("Searching for j-invariant coefficients in knowledge base tapes...\n");
    
    println!("Needles:");
    for needle in &J_NEEDLE {
        println!("  - {}", needle);
    }
    println!();
    
    let matches = search_all_tapes(".")?;
    
    if matches.is_empty() {
        println!("❌ No matches found!");
        println!("\nHint: j-invariant appears in:");
        println!("  - OEIS A000521 (j-invariant coefficients)");
        println!("  - LMFDB (modular forms database)");
        println!("  - Wikidata Q1139519 (Monstrous moonshine)");
        return Ok(());
    }
    
    println!("✅ Found {} matches!\n", matches.len());
    
    // Group by tape
    let mut by_tape: std::collections::HashMap<String, Vec<&Match>> = 
        std::collections::HashMap::new();
    
    for m in &matches {
        by_tape.entry(m.tape.clone()).or_insert_with(Vec::new).push(m);
    }
    
    for (tape, tape_matches) in by_tape.iter() {
        println!("📼 {} ({} matches)", tape, tape_matches.len());
        for m in tape_matches {
            println!("   Line {}: {} → \"{}\"", 
                m.line, 
                m.coefficient,
                m.text.chars().take(60).collect::<String>()
            );
        }
        println!();
    }
    
    // Calculate Gödel encoding of found coefficients
    println!("Gödel encoding of matches:");
    let mut godel: u128 = 1;
    for (i, m) in matches.iter().take(71).enumerate() {
        if let Ok(coeff) = m.coefficient.parse::<u64>() {
            let exp = coeff.min(10) as u32;
            godel = godel.saturating_mul(PRIMES_71[i].pow(exp) as u128);
        }
    }
    println!("  G = {}\n", godel);
    
    println!("Challenge complete! 🎉");
    println!("Next: Level 3 - Decode Moonshine from Monster group");
    
    Ok(())
}
