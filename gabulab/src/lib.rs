//! Gabulab: The Yeast of Thought and Mind
//! Extract Monster Harmonics from Promptbooks

pub mod topology;
pub mod harmonics;
pub mod promptbook;

#[cfg(target_arch = "wasm32")]
pub mod wasm;

use serde::{Deserialize, Serialize};

/// Monster primes (15 primes dividing Monster group order)
pub const MONSTER_PRIMES: [u64; 15] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71
];

/// j-invariant coefficient (Monster group)
pub const J_INVARIANT_COEFF: i64 = 196884;

/// Bott periodicity
pub const BOTT_PERIOD: u8 = 8;

/// Number of shards (CICADA-71)
pub const NUM_SHARDS: u8 = 71;

/// Monster Harmonic extracted from Promptbook
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonsterHarmonic {
    pub shard: u8,
    pub prime: u64,
    pub hecke_operator: String,
    pub j_invariant: i64,
    pub bott_period: u8,
    pub topology: Topology,
}

/// Topology extracted from Promptbook
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Topology {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub personas: Vec<Persona>,
}

/// Node in topology graph
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    pub node_type: NodeType,
    pub content: String,
}

/// Edge in topology graph
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub edge_type: EdgeType,
}

/// Node type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NodeType {
    Input,
    Output,
    Prompt,
    Persona,
}

/// Edge type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EdgeType {
    DataFlow,
    Control,
    Dependency,
}

/// Persona in Promptbook
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Persona {
    pub name: String,
    pub description: String,
    pub shard: u8,
}

impl MonsterHarmonic {
    /// Extract harmonics from Promptbook
    pub fn extract(book: &str) -> Result<Vec<Self>, String> {
        let topology = Topology::from_promptbook(book)?;
        let shards = topology.shard_mod_71();
        
        let harmonics = shards.into_iter()
            .enumerate()
            .map(|(i, topo)| {
                let shard = i as u8;
                let prime = MONSTER_PRIMES[shard as usize % MONSTER_PRIMES.len()];
                
                Self {
                    shard,
                    prime,
                    hecke_operator: format!("T_{}", prime),
                    j_invariant: Self::compute_j_invariant(shard),
                    bott_period: shard % BOTT_PERIOD,
                    topology: topo,
                }
            })
            .collect();
        
        Ok(harmonics)
    }
    
    /// Compute j-invariant mod 196884
    fn compute_j_invariant(shard: u8) -> i64 {
        // Simplified: hash shard to j-invariant space
        let base = (shard as i64 * 744) % J_INVARIANT_COEFF;
        base
    }
}

impl Topology {
    /// Parse Promptbook and extract topology
    pub fn from_promptbook(book: &str) -> Result<Self, String> {
        let mut nodes = Vec::new();
        let mut edges = Vec::new();
        let mut personas = Vec::new();
        
        let mut current_section = None;
        let mut node_id = 0;
        
        for line in book.lines() {
            let trimmed = line.trim();
            
            // Parse INPUT PARAMETER
            if trimmed.starts_with("- INPUT PARAMETER") {
                let param = trimmed.split('{').nth(1)
                    .and_then(|s| s.split('}').next())
                    .unwrap_or("unknown");
                
                nodes.push(Node {
                    id: format!("input_{}", node_id),
                    node_type: NodeType::Input,
                    content: param.to_string(),
                });
                node_id += 1;
            }
            
            // Parse OUTPUT PARAMETER
            if trimmed.starts_with("- OUTPUT PARAMETER") {
                let param = trimmed.split('{').nth(1)
                    .and_then(|s| s.split('}').next())
                    .unwrap_or("unknown");
                
                nodes.push(Node {
                    id: format!("output_{}", node_id),
                    node_type: NodeType::Output,
                    content: param.to_string(),
                });
                node_id += 1;
            }
            
            // Parse PERSONA
            if trimmed.starts_with("- PERSONA") {
                let desc = trimmed.strip_prefix("- PERSONA").unwrap_or("").trim();
                let name = desc.split(',').next().unwrap_or("Unknown");
                
                personas.push(Persona {
                    name: name.to_string(),
                    description: desc.to_string(),
                    shard: (personas.len() % NUM_SHARDS as usize) as u8,
                });
                
                nodes.push(Node {
                    id: format!("persona_{}", node_id),
                    node_type: NodeType::Persona,
                    content: name.to_string(),
                });
                node_id += 1;
            }
            
            // Parse section headers
            if trimmed.starts_with("##") {
                current_section = Some(trimmed.to_string());
                
                nodes.push(Node {
                    id: format!("section_{}", node_id),
                    node_type: NodeType::Prompt,
                    content: trimmed.to_string(),
                });
                node_id += 1;
            }
        }
        
        // Create edges (simplified: sequential flow)
        for i in 0..nodes.len().saturating_sub(1) {
            edges.push(Edge {
                from: nodes[i].id.clone(),
                to: nodes[i + 1].id.clone(),
                edge_type: EdgeType::DataFlow,
            });
        }
        
        Ok(Self { nodes, edges, personas })
    }
    
    /// Shard topology into 71 pieces
    pub fn shard_mod_71(&self) -> Vec<Self> {
        let mut shards = vec![Self::empty(); NUM_SHARDS as usize];
        
        for (i, node) in self.nodes.iter().enumerate() {
            let shard_idx = i % NUM_SHARDS as usize;
            shards[shard_idx].nodes.push(node.clone());
        }
        
        for (i, edge) in self.edges.iter().enumerate() {
            let shard_idx = i % NUM_SHARDS as usize;
            shards[shard_idx].edges.push(edge.clone());
        }
        
        for (i, persona) in self.personas.iter().enumerate() {
            let shard_idx = i % NUM_SHARDS as usize;
            shards[shard_idx].personas.push(persona.clone());
        }
        
        shards
    }
    
    fn empty() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            personas: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_extract_harmonics() {
        let book = r#"
# Test Book
- INPUT PARAMETER {input}
- OUTPUT PARAMETER {output}

## Section 1
- PERSONA Alice, expert
        "#;
        
        let harmonics = MonsterHarmonic::extract(book).unwrap();
        assert!(!harmonics.is_empty());
    }
}
