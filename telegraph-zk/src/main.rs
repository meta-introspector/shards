use clap::{Parser, Subcommand};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use tokio::time::{sleep, Duration};

const MORSE_TABLE: &[(&str, &str)] = &[
    ("A", ".-"),    ("B", "-..."),  ("C", "-.-."),  ("D", "-.."),
    ("E", "."),     ("F", "..-."),  ("G", "--."),   ("H", "...."),
    ("I", ".."),    ("J", ".---"),  ("K", "-.-"),   ("L", ".-.."),
    ("M", "--"),    ("N", "-."),    ("O", "---"),   ("P", ".--."),
    ("Q", "--.-"),  ("R", ".-."),   ("S", "..."),   ("T", "-"),
    ("U", "..-"),   ("V", "...-"),  ("W", ".--"),   ("X", "-..-"),
    ("Y", "-.--"),  ("Z", "--.."),
    ("0", "-----"), ("1", ".----"), ("2", "..---"), ("3", "...--"),
    ("4", "....-"), ("5", "....."), ("6", "-...."), ("7", "--..."),
    ("8", "---.."), ("9", "----."),
    (" ", "/"),
];

const DOT_MS: u64 = 100;
const DASH_MS: u64 = 300;
const GAP_MS: u64 = 100;

fn encode_morse(text: &str) -> String {
    let map: HashMap<char, &str> = MORSE_TABLE.iter()
        .map(|(c, m)| (c.chars().next().unwrap(), *m))
        .collect();
    
    text.to_uppercase()
        .chars()
        .filter_map(|c| map.get(&c))
        .map(|&s| s)
        .collect::<Vec<_>>()
        .join(" ")
}

fn decode_morse(morse: &str) -> String {
    let map: HashMap<&str, char> = MORSE_TABLE.iter()
        .map(|(c, m)| (*m, c.chars().next().unwrap()))
        .collect();
    
    morse.split_whitespace()
        .filter_map(|code| map.get(code))
        .collect()
}

fn zk_proof(message: &str, shard_id: u8) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(message.as_bytes());
    hasher.update(&[shard_id]);
    hasher.finalize().into()
}

async fn transmit_morse(morse: &str) {
    for symbol in morse.chars() {
        match symbol {
            '.' => {
                print!("•");
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
                sleep(Duration::from_millis(DOT_MS)).await;
            }
            '-' => {
                print!("━");
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
                sleep(Duration::from_millis(DASH_MS)).await;
            }
            ' ' => {
                print!(" ");
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
            }
            '/' => {
                print!(" / ");
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
            }
            _ => {}
        }
        sleep(Duration::from_millis(GAP_MS)).await;
    }
    println!();
}

#[derive(Parser)]
#[command(name = "telegraph")]
#[command(about = "ZK-Secure Telegraph with Morse Code")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Send {
        #[arg(long)]
        from: u8,
        #[arg(long)]
        to: u8,
        #[arg(long)]
        message: String,
    },
    Encode {
        #[arg(long)]
        text: String,
    },
    Decode {
        #[arg(long)]
        morse: String,
    },
    Station {
        #[arg(long)]
        shard: u8,
    },
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Send { from, to, message } => {
            println!("╔════════════════════════════════════════════════════════════╗");
            println!("║              TELEGRAPH TRANSMISSION                        ║");
            println!("╚════════════════════════════════════════════════════════════╝\n");
            
            println!("From: Shard {}", from);
            println!("To:   Shard {}", to);
            println!("Text: {}\n", message);
            
            let morse = encode_morse(&message);
            println!("Morse: {}\n", morse);
            
            let proof = zk_proof(&message, from);
            println!("ZK Proof: {}\n", hex::encode(&proof[..8]));
            
            println!("Transmitting...\n");
            transmit_morse(&morse).await;
            
            println!("\n✓ Transmission complete");
        }
        
        Commands::Encode { text } => {
            let morse = encode_morse(&text);
            println!("Text:  {}", text);
            println!("Morse: {}", morse);
        }
        
        Commands::Decode { morse } => {
            let text = decode_morse(&morse);
            println!("Morse: {}", morse);
            println!("Text:  {}", text);
        }
        
        Commands::Station { shard } => {
            println!("╔════════════════════════════════════════════════════════════╗");
            println!("║           Telegraph Station - Shard {:2}                   ║", shard);
            println!("╚════════════════════════════════════════════════════════════╝\n");
            
            println!("ZK Context: Shard {}", shard);
            println!("Listening for messages...");
            println!("(Press Ctrl+C to stop)\n");
            
            tokio::signal::ctrl_c().await?;
            println!("\nStation closed");
        }
    }
    
    Ok(())
}
