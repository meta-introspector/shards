// Unified Monster CLI - All tools in one binary
// AGPL-3.0+ | Commercial: shards@solfunmeme.com

use std::env;

mod perfect_pack;
mod magic_market;
mod emit_shards;
mod ast_tenfold;
mod meme_witness;
mod hecke_shard;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        print_help();
        return;
    }
    
    match args[1].as_str() {
        "pack" => perfect_pack::run(),
        "market" => magic_market::run(),
        "emit" => emit_shards::run(),
        "ast" => ast_tenfold::run(),
        "witness" => meme_witness::run(),
        "shard" => hecke_shard::run(&args[2..]),
        "help" | "-h" | "--help" => print_help(),
        _ => {
            println!("Unknown command: {}", args[1]);
            print_help();
        }
    }
}

fn print_help() {
    println!(r#"
🐯 MONSTER CLI - Unified Rust Tools 🐯

USAGE:
    monster <COMMAND> [ARGS]

COMMANDS:
    pack        Perfect pack - Order 71 games by Monster group
    market      Magic number market - Gödel number pricing
    emit        Emit 71 shards - Generate shard files
    ast         AST tenfold way - Bott periodicity classification
    witness     Meme witness - Real-time meme detection
    shard       Hecke-Bott sharding - Map data to shards
    help        Show this help message

EXAMPLES:
    monster pack
    monster market
    monster shard "Hello, Monster!"
    monster witness

LICENSE:
    AGPL-3.0+ (default) | MIT/Apache-2.0 (commercial)
    Contact: shards@solfunmeme.com
    ZK hackers gotta eat! 🍕
"#);
}
