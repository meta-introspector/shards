// TradeWars MCTS AI-Life Integration
// Integrates MCTS meme sampler with TradeWars door game

use std::sync::{Arc, Mutex};

mod mcts_ailife_meme_sampler;
use mcts_ailife_meme_sampler::*;

/// TradeWars AI player using MCTS
pub struct TradeWarsAI {
    sampler: MCTSAILifeSampler,
    player_id: String,
    strategy: Arc<Mutex<Vec<f32>>>,
}

impl TradeWarsAI {
    pub fn new(player_id: String) -> Self {
        let sampler = MCTSAILifeSampler::new();
        sampler.initialize_population(71); // 71 memes for 71 shards
        
        TradeWarsAI {
            sampler,
            player_id,
            strategy: Arc::new(Mutex::new(vec![0.0; 71])),
        }
    }
    
    /// Evolve strategy using MCTS
    pub fn evolve_strategy(&self, generations: u32) -> Result<(), String> {
        println!("🧬 {} evolving strategy...", self.player_id);
        self.sampler.run_ailife(generations)?;
        
        // Extract best meme as strategy
        let pop = self.sampler.population.lock().unwrap();
        if let Some(best) = pop.iter().max_by(|a, b| a.fitness.partial_cmp(&b.fitness).unwrap()) {
            let mut strat = self.strategy.lock().unwrap();
            *strat = best.genes.clone();
            println!("✅ Best fitness: {:.4}", best.fitness);
        }
        
        Ok(())
    }
    
    /// Make move based on evolved strategy
    pub fn make_move(&self, shard: usize) -> f32 {
        let strat = self.strategy.lock().unwrap();
        if shard < strat.len() {
            strat[shard]
        } else {
            0.0
        }
    }
    
    /// Evaluate game state
    pub fn evaluate_state(&self, lobsters: u32, turn: u32) -> f32 {
        (lobsters as f32) / (turn as f32 + 1.0)
    }
}

fn main() {
    println!("🔮⚡ TradeWars MCTS AI-Life 📻🦞\n");
    
    // Create AI players
    let ai1 = TradeWarsAI::new("peer-boat-ai-01".to_string());
    let ai2 = TradeWarsAI::new("peer-boat-ai-02".to_string());
    
    // Evolve strategies
    println!("Evolving AI strategies...\n");
    ai1.evolve_strategy(10).unwrap();
    ai2.evolve_strategy(10).unwrap();
    
    // Simulate game
    println!("\nSimulating TradeWars match...\n");
    for turn in 1..=5 {
        println!("Turn {}:", turn);
        
        let move1 = ai1.make_move(turn % 71);
        let move2 = ai2.make_move(turn % 71);
        
        println!("  AI1 move: {:.4}", move1);
        println!("  AI2 move: {:.4}", move2);
        
        let score1 = ai1.evaluate_state(turn * 2, turn);
        let score2 = ai2.evaluate_state(turn * 3, turn);
        
        println!("  AI1 score: {:.4}", score1);
        println!("  AI2 score: {:.4}", score2);
        println!();
    }
    
    println!("QED 🔮⚡📻🦞");
}
