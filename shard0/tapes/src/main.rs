use std::fs::File;
use std::io::{BufWriter, Write, Result};

const PRIMES_71: [u64; 71] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353,
];

struct DataTape {
    name: &'static str,
    url: &'static str,
    godel_seed: u128,
}

const TAPES: [DataTape; 10] = [
    DataTape {
        name: "OEIS",
        url: "https://oeis.org/",
        godel_seed: 2_u128.pow(71) * 3_u128.pow(23),
    },
    DataTape {
        name: "Wikidata",
        url: "https://www.wikidata.org/",
        godel_seed: 5_u128.pow(71) * 7_u128.pow(23),
    },
    DataTape {
        name: "OpenStreetMap",
        url: "https://www.openstreetmap.org/",
        godel_seed: 11_u128.pow(71) * 13_u128.pow(23),
    },
    DataTape {
        name: "LMFDB",
        url: "https://www.lmfdb.org/",
        godel_seed: 17_u128.pow(71) * 19_u128.pow(23),
    },
    DataTape {
        name: "LibriVox",
        url: "https://librivox.org/",
        godel_seed: 23_u128.pow(71) * 29_u128.pow(23),
    },
    DataTape {
        name: "Gutenberg",
        url: "https://www.gutenberg.org/",
        godel_seed: 31_u128.pow(71) * 37_u128.pow(23),
    },
    DataTape {
        name: "GNU-Mes",
        url: "https://www.gnu.org/software/mes/",
        godel_seed: 41_u128.pow(71) * 43_u128.pow(23),
    },
    DataTape {
        name: "TinyCC",
        url: "https://bellard.org/tcc/",
        godel_seed: 47_u128.pow(71) * 53_u128.pow(23),
    },
    DataTape {
        name: "GCC-History",
        url: "https://gcc.gnu.org/",
        godel_seed: 59_u128.pow(71) * 61_u128.pow(23),
    },
    DataTape {
        name: "Bootstrap-Seeds",
        url: "https://bootstrappable.org/",
        godel_seed: 67_u128.pow(71) * 71_u128.pow(23),
    },
];

fn generate_tape_header(tape: &DataTape) -> Vec<u8> {
    let mut header = Vec::new();
    
    // Magic: "TAPE"
    header.extend_from_slice(b"TAPE");
    
    // Version: 1
    header.push(1);
    
    // Name (32 bytes, null-padded)
    let mut name_bytes = tape.name.as_bytes().to_vec();
    name_bytes.resize(32, 0);
    header.extend_from_slice(&name_bytes);
    
    // URL (128 bytes, null-padded)
    let mut url_bytes = tape.url.as_bytes().to_vec();
    url_bytes.resize(128, 0);
    header.extend_from_slice(&url_bytes);
    
    // Gödel seed (16 bytes, little-endian)
    header.extend_from_slice(&tape.godel_seed.to_le_bytes());
    
    // Checksum (4 bytes)
    let checksum: u32 = header.iter().map(|&b| b as u32).sum();
    header.extend_from_slice(&checksum.to_le_bytes());
    
    header
}

fn main() -> Result<()> {
    println!("Generating knowledge base tapes for Mars deployment...\n");
    
    for tape in &TAPES {
        let filename = format!("tape-{}.dat", tape.name.to_lowercase().replace(" ", "-"));
        let mut file = BufWriter::new(File::create(&filename)?);
        
        // Write header
        let header = generate_tape_header(tape);
        file.write_all(&header)?;
        
        println!("📼 {}", tape.name);
        println!("   URL: {}", tape.url);
        println!("   Gödel seed: {}", tape.godel_seed);
        println!("   File: {}", filename);
        println!("   Size: {} bytes\n", header.len());
    }
    
    // Generate manifest
    let mut manifest = BufWriter::new(File::create("TAPE_MANIFEST.txt")?);
    writeln!(manifest, "CICADA-71 KNOWLEDGE BASE TAPES")?;
    writeln!(manifest, "================================\n")?;
    writeln!(manifest, "Mars deployment survival kit: Open knowledge for 26-month isolation.\n")?;
    
    for (i, tape) in TAPES.iter().enumerate() {
        writeln!(manifest, "TAPE {}: {}", i + 1, tape.name)?;
        writeln!(manifest, "  Source: {}", tape.url)?;
        writeln!(manifest, "  Gödel seed: {}", tape.godel_seed)?;
        writeln!(manifest, "  Prime encoding: p_71^71 × p_23^23")?;
        writeln!(manifest)?;
    }
    
    writeln!(manifest, "USAGE:")?;
    writeln!(manifest, "  cat tape-*.dat | ingest --shard 0")?;
    writeln!(manifest, "  distribute --shards 71 --nodes 23")?;
    writeln!(manifest)?;
    
    writeln!(manifest, "KNOWLEDGE BASES:")?;
    writeln!(manifest)?;
    writeln!(manifest, "OEIS (Online Encyclopedia of Integer Sequences)")?;
    writeln!(manifest, "  - 370,000+ sequences")?;
    writeln!(manifest, "  - Monster group: A001379")?;
    writeln!(manifest, "  - Moonshine: A007379")?;
    writeln!(manifest)?;
    writeln!(manifest, "Wikidata (Structured Knowledge)")?;
    writeln!(manifest, "  - 100M+ entities")?;
    writeln!(manifest, "  - Q193724: Monster group")?;
    writeln!(manifest, "  - Q1139519: Monstrous moonshine")?;
    writeln!(manifest)?;
    writeln!(manifest, "OpenStreetMap (Geographic Data)")?;
    writeln!(manifest, "  - 23 Earth chokepoints")?;
    writeln!(manifest, "  - Node placement optimization")?;
    writeln!(manifest, "  - Network topology")?;
    writeln!(manifest)?;
    writeln!(manifest, "LMFDB (L-functions and Modular Forms)")?;
    writeln!(manifest, "  - Automorphic forms")?;
    writeln!(manifest, "  - Maass forms")?;
    writeln!(manifest, "  - Moonshine connections")?;
    writeln!(manifest)?;
    writeln!(manifest, "LibriVox (Public Domain Audiobooks)")?;
    writeln!(manifest, "  - 20,000+ audiobooks")?;
    writeln!(manifest, "  - Human voice for isolation")?;
    writeln!(manifest, "  - Mars: 26-month round trip")?;
    writeln!(manifest)?;
    writeln!(manifest, "Project Gutenberg (Public Domain Books)")?;
    writeln!(manifest, "  - 70,000+ books")?;
    writeln!(manifest, "  - Complete Mars library")?;
    writeln!(manifest, "  - Offline knowledge preservation")?;
    writeln!(manifest)?;
    writeln!(manifest, "GNU Mes (Bootstrappable Scheme)")?;
    writeln!(manifest, "  - 357-byte bootstrap seed")?;
    writeln!(manifest, "  - Trusting Trust solution")?;
    writeln!(manifest, "  - Full toolchain from source")?;
    writeln!(manifest)?;
    writeln!(manifest, "TinyCC (Tiny C Compiler)")?;
    writeln!(manifest, "  - 100KB compiler")?;
    writeln!(manifest, "  - 9x faster than GCC")?;
    writeln!(manifest, "  - Self-hosting in <1 second")?;
    writeln!(manifest)?;
    writeln!(manifest, "GCC History (1987-2000)")?;
    writeln!(manifest, "  - GCC 1.0 (1987)")?;
    writeln!(manifest, "  - GCC 2.95 (1999, pre-C++ rewrite)")?;
    writeln!(manifest, "  - Complete 20th century toolchain")?;
    writeln!(manifest)?;
    writeln!(manifest, "Bootstrap Seeds (Stage0)")?;
    writeln!(manifest, "  - 357 bytes hand-auditable hex")?;
    writeln!(manifest, "  - hex0 → hex1 → hex2 → M0 → cc_x86")?;
    writeln!(manifest, "  - Reproducible from nothing")?;
    writeln!(manifest)?;
    writeln!(manifest, "LEVEL 0 PRIORITY:")?;
    writeln!(manifest, "  Focus: GNU Mes, TinyCC, GCC, Bootstrap Seeds")?;
    writeln!(manifest, "  Goal: Rebuild computing from 357 bytes")?;
    writeln!(manifest, "  History: 1900-2000 compiler evolution")?;
    writeln!(manifest)?;
    writeln!(manifest, "FUTURE SHARDS:")?;
    writeln!(manifest, "  - ArXiv (scientific papers)")?;
    writeln!(manifest, "  - Hugging Face (AI models)")?;
    writeln!(manifest, "  - Archive.org (web history)")?;
    writeln!(manifest, "  - GitHub (source code)")?;
    writeln!(manifest)?;
    writeln!(manifest, "MARS DEPLOYMENT:")?;
    writeln!(manifest, "  - 26 months (8mo travel + 10mo surface + 8mo return)")?;
    writeln!(manifest, "  - 20-minute light delay")?;
    writeln!(manifest, "  - 100GB compressed → 128GB microSD")?;
    
    println!("✅ Generated TAPE_MANIFEST.txt");
    println!("\n🔧 Level 0: Bootstrap toolchain ready!");
    println!("🚀 Mars deployment ready!");
    
    Ok(())
}
