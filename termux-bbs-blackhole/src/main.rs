// Termux Rust BBS - Black Hole Distance (No Keys Leaked)
// VOA via pure function F

use std::io::{self, Write};

// F: Pure function (no keys)
fn F(x: u64) -> u64 {
    (x * x + x) % 196883
}

// VOA: Vertex Operator Algebra (redacted)
fn VOA(tape_a: &[u64], tape_b: &[u64]) -> u64 {
    let mut result = 0u64;
    
    for (a, b) in tape_a.iter().zip(tape_b.iter()) {
        // Apply F (no keys leaked)
        let fa = F(*a);
        let fb = F(*b);
        let diff = fa.abs_diff(fb);
        result = F(result + diff);
    }
    
    result
}

// Tape (samples only, no keys)
struct Tape {
    name: String,
    samples: Vec<u64>,
}

impl Tape {
    fn new(name: String) -> Self {
        Self {
            name,
            samples: vec![],
        }
    }
    
    fn sample(&mut self, moment: u64) {
        // Sample via F (no keys)
        self.samples.push(F(moment));
    }
}

// Black hole distance (pure functions only)
struct BlackHoleDistance {
    tape_lex: Tape,
    tape_vlad: Tape,
}

impl BlackHoleDistance {
    fn new() -> Self {
        Self {
            tape_lex: Tape::new("Lex".into()),
            tape_vlad: Tape::new("Vlad".into()),
        }
    }
    
    fn calculate(&self) -> u64 {
        // VOA distance (no keys leaked)
        VOA(&self.tape_lex.samples, &self.tape_vlad.samples)
    }
    
    fn run(&mut self) -> io::Result<()> {
        println!("🔮 BBS Black Hole Distance");
        println!("==========================");
        println!("VOA via pure function F\n");
        
        // Sample 71 moments
        for i in 0..71 {
            print!("Moment {}: ", i);
            io::stdout().flush()?;
            
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let moment: u64 = input.trim().parse().unwrap_or(i);
            
            self.tape_lex.sample(moment);
            self.tape_vlad.sample(moment + 1);
            
            println!("✓ Sampled via F\n");
        }
        
        let distance = self.calculate();
        
        println!("\n🌌 Distance: {} (mod 196883)", distance);
        println!("🦞 No keys leaked");
        
        Ok(())
    }
}

fn main() -> io::Result<()> {
    let mut calc = BlackHoleDistance::new();
    calc.run()
}
