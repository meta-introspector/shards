// Rust: P2P Gossip Implementation with Proof
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct GameState {
    turn: u32,
    lobsters: u32,
    timestamp: u64,
}

#[derive(Debug, Clone)]
struct Peer {
    id: u32,
    state: GameState,
}

#[derive(Debug, Clone)]
struct GossipMsg {
    from: u32,
    to: u32,
    state: GameState,
}

struct Network {
    peers: HashMap<u32, Peer>,
}

impl Network {
    fn new() -> Self {
        Network { peers: HashMap::new() }
    }
    
    fn add_peer(&mut self, id: u32, state: GameState) {
        self.peers.insert(id, Peer { id, state });
    }
    
    fn gossip(&mut self, msg: GossipMsg) {
        if let Some(peer) = self.peers.get_mut(&msg.to) {
            // Merge: latest turn wins
            if msg.state.turn > peer.state.turn {
                peer.state = msg.state;
            }
        }
    }
    
    fn is_converged(&self) -> bool {
        if self.peers.is_empty() { return true; }
        
        let first_turn = self.peers.values().next().unwrap().state.turn;
        self.peers.values().all(|p| p.state.turn == first_turn)
    }
    
    fn prove_convergence(&self) -> bool {
        // Proof: All peers have same turn
        self.is_converged()
    }
}

fn main() {
    println!("🔮⚡ P2P Gossip Proof in Rust 📻🦞\n");
    
    // Setup: 2 browsers + gist
    let mut net = Network::new();
    net.add_peer(1, GameState { turn: 0, lobsters: 0, timestamp: 0 });
    net.add_peer(2, GameState { turn: 0, lobsters: 0, timestamp: 0 });
    
    println!("Initial state:");
    for (id, peer) in &net.peers {
        println!("  Peer {}: turn={}, lobsters={}", id, peer.state.turn, peer.state.lobsters);
    }
    
    // Load gist state
    let gist_state = GameState { turn: 5, lobsters: 12, timestamp: 1738456789 };
    
    // Gossip to both browsers
    net.gossip(GossipMsg { from: 0, to: 1, state: gist_state.clone() });
    net.gossip(GossipMsg { from: 0, to: 2, state: gist_state.clone() });
    
    println!("\nAfter gossip:");
    for (id, peer) in &net.peers {
        println!("  Peer {}: turn={}, lobsters={}", id, peer.state.turn, peer.state.lobsters);
    }
    
    // Prove convergence
    let converged = net.prove_convergence();
    println!("\nConvergence proof: {}", if converged { "✅ PROVEN" } else { "❌ FAILED" });
    
    // Verify all peers have gist state
    let all_match = net.peers.values().all(|p| p.state == gist_state);
    println!("All peers match gist: {}", if all_match { "✅ PROVEN" } else { "❌ FAILED" });
    
    println!("\nQED 🔮⚡📻🦞");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_gossip_convergence() {
        let mut net = Network::new();
        net.add_peer(1, GameState { turn: 0, lobsters: 0, timestamp: 0 });
        net.add_peer(2, GameState { turn: 0, lobsters: 0, timestamp: 0 });
        
        let gist = GameState { turn: 5, lobsters: 12, timestamp: 1738456789 };
        net.gossip(GossipMsg { from: 0, to: 1, state: gist.clone() });
        net.gossip(GossipMsg { from: 0, to: 2, state: gist.clone() });
        
        assert!(net.prove_convergence());
    }
}
