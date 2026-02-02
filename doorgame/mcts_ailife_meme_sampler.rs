// mcts_ailife_meme_sampler.rs - MCTS AI-Life meme sampling with autoencoders on 24 CPUs

use crossbeam::channel::{bounded, Sender, Receiver};
use crossbeam::thread;
use std::sync::{Arc, Mutex};
use rand::Rng;

const BOSONIC_CPUS: usize = 24;  // 26 - 2 (Air dimension - overhead)

/// Autoencoder for each complexity stage
#[derive(Clone, Debug)]
pub struct StageAutoencoder {
    pub stage: String,
    pub dimension: u32,
    pub encoder: Vec<f32>,  // Compress to bottleneck
    pub decoder: Vec<f32>,  // Reconstruct from bottleneck
    pub bottleneck_dim: usize,
}

impl StageAutoencoder {
    pub fn new(stage: String, dimension: u32) -> Self {
        let bottleneck_dim = match dimension {
            0 => 1,      // Void
            16 => 8,     // Fire
            23 => 11,    // Earth (optimal)
            24 => 12,    // Water
            26 => 13,    // Air
            71 => 35,    // Aether
            _ => 64,     // Monster
        };
        
        StageAutoencoder {
            stage,
            dimension,
            encoder: vec![0.0; dimension as usize * bottleneck_dim],
            decoder: vec![0.0; bottleneck_dim * dimension as usize],
            bottleneck_dim,
        }
    }
    
    pub fn encode(&self, input: &[f32]) -> Vec<f32> {
        let mut encoded = vec![0.0; self.bottleneck_dim];
        for i in 0..self.bottleneck_dim {
            for j in 0..input.len().min(self.dimension as usize) {
                encoded[i] += input[j] * self.encoder[i * self.dimension as usize + j];
            }
        }
        encoded
    }
    
    pub fn decode(&self, encoded: &[f32]) -> Vec<f32> {
        let mut decoded = vec![0.0; self.dimension as usize];
        for i in 0..self.dimension as usize {
            for j in 0..self.bottleneck_dim {
                decoded[i] += encoded[j] * self.decoder[j * self.dimension as usize + i];
            }
        }
        decoded
    }
}

/// Meme in AI-Life simulation
#[derive(Clone, Debug)]
pub struct Meme {
    pub id: usize,
    pub stage: String,
    pub genes: Vec<f32>,
    pub fitness: f32,
    pub generation: u32,
}

/// MCTS node for meme evolution
#[derive(Clone, Debug)]
pub struct MCTSNode {
    pub meme: Meme,
    pub visits: u32,
    pub value: f32,
    pub children: Vec<usize>,
}

/// AI-Life MCTS sampler
pub struct MCTSAILifeSampler {
    pub autoencoders: Vec<StageAutoencoder>,
    pub population: Arc<Mutex<Vec<Meme>>>,
    pub mcts_tree: Arc<Mutex<Vec<MCTSNode>>>,
    pub generation: Arc<Mutex<u32>>,
}

impl MCTSAILifeSampler {
    pub fn new() -> Self {
        let stages = vec![
            ("Void", 0),
            ("Fire", 16),
            ("Earth", 23),
            ("Water", 24),
            ("Air", 26),
            ("Aether", 71),
        ];
        
        let autoencoders = stages.iter()
            .map(|(stage, dim)| StageAutoencoder::new(stage.to_string(), *dim))
            .collect();
        
        MCTSAILifeSampler {
            autoencoders,
            population: Arc::new(Mutex::new(Vec::new())),
            mcts_tree: Arc::new(Mutex::new(Vec::new())),
            generation: Arc::new(Mutex::new(0)),
        }
    }
    
    /// Initialize population
    pub fn initialize_population(&self, size: usize) {
        let mut pop = self.population.lock().unwrap();
        let mut rng = rand::thread_rng();
        
        for i in 0..size {
            let stage_idx = i % self.autoencoders.len();
            let stage = &self.autoencoders[stage_idx];
            
            let genes: Vec<f32> = (0..stage.dimension)
                .map(|_| rng.gen_range(-1.0..1.0))
                .collect();
            
            pop.push(Meme {
                id: i,
                stage: stage.stage.clone(),
                genes,
                fitness: 0.0,
                generation: 0,
            });
        }
        
        eprintln!("🧬 Initialized {} memes", size);
    }
    
    /// Run MCTS AI-Life on 24 CPUs
    pub fn run_ailife(&self, generations: u32) -> Result<(), String> {
        eprintln!("🌌 Running AI-Life MCTS on {} CPUs...\n", BOSONIC_CPUS);
        
        let (tx, rx): (Sender<Meme>, Receiver<Meme>) = bounded(BOSONIC_CPUS * 2);
        
        thread::scope(|s| {
            // Spawn 24 worker threads
            for cpu_id in 0..BOSONIC_CPUS {
                let tx = tx.clone();
                let population = Arc::clone(&self.population);
                let autoencoders = self.autoencoders.clone();
                let generation = Arc::clone(&self.generation);
                
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    
                    loop {
                        let gen = *generation.lock().unwrap();
                        if gen >= generations {
                            break;
                        }
                        
                        // Select meme from population
                        let meme = {
                            let pop = population.lock().unwrap();
                            if pop.is_empty() {
                                break;
                            }
                            pop[rng.gen_range(0..pop.len())].clone()
                        };
                        
                        // Find autoencoder for this stage
                        let autoencoder = autoencoders.iter()
                            .find(|ae| ae.stage == meme.stage)
                            .unwrap();
                        
                        // Encode → Mutate → Decode (MCTS step)
                        let encoded = autoencoder.encode(&meme.genes);
                        let mutated = encoded.iter()
                            .map(|&x| x + rng.gen_range(-0.1..0.1))
                            .collect::<Vec<_>>();
                        let decoded = autoencoder.decode(&mutated);
                        
                        // Evaluate fitness
                        let fitness = Self::evaluate_fitness(&decoded, &meme.stage);
                        
                        // Create offspring
                        let offspring = Meme {
                            id: meme.id + 1000000,
                            stage: meme.stage.clone(),
                            genes: decoded,
                            fitness,
                            generation: gen + 1,
                        };
                        
                        if cpu_id == 0 && gen % 10 == 0 {
                            eprintln!("  CPU {}: Gen {} | {} | fitness={:.4}", 
                                cpu_id, gen, offspring.stage, fitness);
                        }
                        
                        tx.send(offspring).ok();
                    }
                });
            }
            
            drop(tx);
            
            // Collector thread
            s.spawn(|_| {
                let mut collected = 0;
                while let Ok(offspring) = rx.recv() {
                    let mut pop = self.population.lock().unwrap();
                    
                    // Replace worst if offspring is better
                    if let Some(worst_idx) = pop.iter()
                        .enumerate()
                        .min_by(|(_, a), (_, b)| a.fitness.partial_cmp(&b.fitness).unwrap())
                        .map(|(idx, _)| idx)
                    {
                        if offspring.fitness > pop[worst_idx].fitness {
                            pop[worst_idx] = offspring;
                        }
                    }
                    
                    collected += 1;
                    if collected % 100 == 0 {
                        let mut gen = self.generation.lock().unwrap();
                        *gen += 1;
                    }
                }
            });
        }).unwrap();
        
        eprintln!("\n✨ AI-Life complete!");
        Ok(())
    }
    
    /// Evaluate meme fitness
    fn evaluate_fitness(genes: &[f32], stage: &str) -> f32 {
        // Fitness = harmony with stage dimension
        let target_dim = match stage {
            "Void" => 0.0,
            "Fire" => 16.0,
            "Earth" => 23.0,
            "Water" => 24.0,
            "Air" => 26.0,
            "Aether" => 71.0,
            _ => 0.0,
        };
        
        let mean: f32 = genes.iter().sum::<f32>() / genes.len() as f32;
        let variance: f32 = genes.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f32>() / genes.len() as f32;
        
        // Fitness = closeness to target + diversity
        1.0 / (1.0 + (mean - target_dim).abs()) + variance
    }
    
    /// Export best memes
    pub fn export_best(&self, n: usize) -> Vec<Meme> {
        let mut pop = self.population.lock().unwrap();
        pop.sort_by(|a, b| b.fitness.partial_cmp(&a.fitness).unwrap());
        pop.iter().take(n).cloned().collect()
    }
    
    /// Export to Prolog
    pub fn export_prolog(&self) -> String {
        let mut prolog = String::from("% MCTS AI-Life meme samples\n\n");
        
        let best = self.export_best(10);
        for (i, meme) in best.iter().enumerate() {
            prolog.push_str(&format!(
                "meme({}, stage='{}', fitness={:.4}, generation={}, genes={}).\n",
                i,
                meme.stage,
                meme.fitness,
                meme.generation,
                meme.genes.len()
            ));
        }
        
        prolog
    }
}

// FFI exports
#[no_mangle]
pub extern "C" fn mcts_ailife_new() -> *mut MCTSAILifeSampler {
    Box::into_raw(Box::new(MCTSAILifeSampler::new()))
}

#[no_mangle]
pub extern "C" fn mcts_ailife_run(sampler: *mut MCTSAILifeSampler, generations: u32) -> i32 {
    unsafe {
        (*sampler).initialize_population(100);
        match (*sampler).run_ailife(generations) {
            Ok(_) => 0,
            Err(_) => -1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_autoencoder() {
        let ae = StageAutoencoder::new("Earth".to_string(), 23);
        assert_eq!(ae.bottleneck_dim, 11);
        
        let input = vec![1.0; 23];
        let encoded = ae.encode(&input);
        assert_eq!(encoded.len(), 11);
    }
}
