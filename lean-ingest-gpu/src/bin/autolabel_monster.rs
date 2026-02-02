use serde::{Deserialize, Serialize};
use std::fs::{self, File};
use std::collections::HashMap;
use anyhow::Result;

#[derive(Serialize, Deserialize, Debug)]
struct TopoArrow {
    from_prime: u64,
    to_prime: u64,
    from_topo: u8,
    to_topo: u8,
    from_emoji: String,
    to_emoji: String,
    shared_decls: usize,
    shared_files: usize,
    strength: f64,
}

#[derive(Serialize, Deserialize, Debug)]
struct MonsterLabel {
    prime: u64,
    topo_class: u8,
    emoji: String,
    role: String,
    in_degree: usize,
    out_degree: usize,
    total_flow: usize,
    centrality: f64,
    is_bdi: bool,
    is_rooster: bool,
}

const PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
const EMOJI: [&str; 10] = ["🌀", "🔱", "⚛️", "🌳", "💎", "🌊", "🧬", "🔮", "⚡", "🌌"];

fn main() -> Result<()> {
    let arrows_file = "/home/mdupont/introspector/monster_topo_arrows.json";
    let output_file = "/home/mdupont/introspector/monster_autolabels.json";
    
    println!("📖 Loading arrows...");
    let content = fs::read_to_string(arrows_file)?;
    let arrows: Vec<TopoArrow> = serde_json::from_str(&content)?;
    
    println!("✅ Loaded {} arrows", arrows.len());
    println!("🏷️  Auto-labeling Monster primes...");
    
    // Compute metrics
    let mut in_deg: HashMap<u64, usize> = HashMap::new();
    let mut out_deg: HashMap<u64, usize> = HashMap::new();
    let mut flow: HashMap<u64, usize> = HashMap::new();
    
    for a in &arrows {
        *out_deg.entry(a.from_prime).or_default() += 1;
        *in_deg.entry(a.to_prime).or_default() += 1;
        *flow.entry(a.from_prime).or_default() += a.shared_decls;
        *flow.entry(a.to_prime).or_default() += a.shared_decls;
    }
    
    let max_flow = flow.values().max().copied().unwrap_or(1) as f64;
    
    let mut labels: Vec<MonsterLabel> = PRIMES
        .iter()
        .map(|&p| {
            let topo = (p % 10) as u8;
            let in_d = in_deg.get(&p).copied().unwrap_or(0);
            let out_d = out_deg.get(&p).copied().unwrap_or(0);
            let f = flow.get(&p).copied().unwrap_or(0);
            let centrality = f as f64 / max_flow;
            
            let is_bdi = topo == 3;
            let is_rooster = p == 71;
            
            let role = if is_rooster {
                "🐓 Rooster (Attractor)".to_string()
            } else if is_bdi {
                "🌳 Life Bearer (Hub)".to_string()
            } else if centrality > 0.8 {
                "⭐ Central Hub".to_string()
            } else if out_d > in_d + 3 {
                "📤 Source".to_string()
            } else if in_d > out_d + 3 {
                "📥 Sink".to_string()
            } else if out_d > 8 {
                "🔄 Distributor".to_string()
            } else {
                "🔗 Connector".to_string()
            };
            
            MonsterLabel {
                prime: p,
                topo_class: topo,
                emoji: EMOJI[topo as usize].to_string(),
                role,
                in_degree: in_d,
                out_degree: out_d,
                total_flow: f,
                centrality,
                is_bdi,
                is_rooster,
            }
        })
        .collect();
    
    labels.sort_by(|a, b| b.centrality.partial_cmp(&a.centrality).unwrap());
    
    println!("\n🏷️  Monster Prime Labels:\n");
    for (i, l) in labels.iter().enumerate() {
        println!("  {}. Prime {:2} {} | {} | in:{} out:{} flow:{}M cent:{:.2}",
            i+1, l.prime, l.emoji, l.role, l.in_degree, l.out_degree,
            l.total_flow / 1_000_000, l.centrality
        );
    }
    
    // Group by role
    let mut by_role: HashMap<String, Vec<&MonsterLabel>> = HashMap::new();
    for l in &labels {
        by_role.entry(l.role.clone()).or_default().push(l);
    }
    
    println!("\n📊 Roles:");
    for (role, primes) in by_role.iter() {
        let ps: Vec<u64> = primes.iter().map(|p| p.prime).collect();
        println!("  {}: {:?}", role, ps);
    }
    
    serde_json::to_writer_pretty(File::create(output_file)?, &labels)?;
    println!("\n💾 {}", output_file);
    Ok(())
}
