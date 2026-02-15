use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Serialize)]
struct PaxosWitness {
    node_id: u8,
    fren: String,
    shard: u8,
    timestamp: u64,
    signature: String,
    resonance_score: f64,
    quorum_vote: bool,
}

fn select_resonant_node(shard: u8) -> u8 {
    // Select from 23 Paxos nodes based on shard resonance
    // Node selection: (shard * 13) mod 23 for harmonic distribution
    ((shard as u16 * 13) % 23) as u8
}

fn compute_resonance(node: u8, shard: u8) -> f64 {
    // Resonance = cos(2π * node * shard / 71) for Monster harmonic
    let angle = 2.0 * std::f64::consts::PI * (node as f64) * (shard as f64) / 71.0;
    angle.cos().abs()
}

fn witness_fren(fren: &str, shard: u8) -> PaxosWitness {
    let node = select_resonant_node(shard);
    let resonance = compute_resonance(node, shard);
    
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    
    // Signature: hash(node || fren || shard || timestamp)
    let mut hasher = Sha256::new();
    hasher.update(&[node]);
    hasher.update(fren.as_bytes());
    hasher.update(&[shard]);
    hasher.update(&timestamp.to_le_bytes());
    let sig = format!("{:x}", hasher.finalize());
    
    PaxosWitness {
        node_id: node,
        fren: fren.to_string(),
        shard,
        timestamp,
        signature: sig[..16].to_string(),
        resonance_score: resonance,
        quorum_vote: resonance > 0.5, // Quorum if resonance > 0.5
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = fs::read_to_string("frens/nydiokar_moonshine.json")?;
    let data: serde_json::Value = serde_json::from_str(&input)?;
    
    let fren = data["fren"].as_str().unwrap();
    let shard = data["monster_encoding"]["shard"].as_u64().unwrap() as u8;
    
    let witness = witness_fren(fren, shard);
    
    println!("🔷 Paxos Witness (Node {}/23)", witness.node_id);
    println!("  FREN: {}", witness.fren);
    println!("  Shard: {}", witness.shard);
    println!("  Resonance: {:.3}", witness.resonance_score);
    println!("  Quorum: {}", if witness.quorum_vote { "✓" } else { "✗" });
    println!("  Signature: {}", witness.signature);
    
    let output = serde_json::to_string_pretty(&witness)?;
    fs::write(format!("witnesses/node{:02}_shard{:02}.json", witness.node_id, shard), output)?;
    
    Ok(())
}
