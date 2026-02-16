// Monster-Ripgrep with FRACTRAN Filter
// Chariot Card Door Game + ASCII Cinema + RRDB Galois Towers

use std::fs;
use std::io::{self, Write};
use std::time::Instant;

// FRACTRAN filter
fn fractran_filter(byte: u8, state: u64) -> u64 {
    let fractions = [
        (71, 2), (59, 3), (47, 5), (23, 7), (17, 11),
    ];
    
    let mut s = state;
    for (num, den) in fractions {
        if s % den == 0 {
            s = (s * num / den) % 196883;
            break;
        }
    }
    s
}

// RRDB: Round-Robin Database (Galois tower)
struct RRDB {
    towers: Vec<GaloisTower>,
}

impl RRDB {
    fn new() -> Self {
        // 71 Galois towers (0-70)
        let towers = (0..71).map(|i| GaloisTower::new(i)).collect();
        Self { towers }
    }
    
    fn compress(&mut self, data: &[u64]) {
        // Distribute data across 71 towers
        for (i, &value) in data.iter().enumerate() {
            let tower_id = i % 71;
            self.towers[tower_id].add(value);
        }
    }
    
    fn size(&self) -> usize {
        self.towers.iter().map(|t| t.size()).sum()
    }
}

// Galois hyper tower
struct GaloisTower {
    id: u8,
    field: String,  // GF(2^(id+1))
    data: Vec<u64>,
    compressed: Vec<u64>,
}

impl GaloisTower {
    fn new(id: u8) -> Self {
        Self {
            id,
            field: format!("GF(2^{})", id + 1),
            data: vec![],
            compressed: vec![],
        }
    }
    
    fn add(&mut self, value: u64) {
        self.data.push(value);
        
        // Compress: Keep only mod (id+1)
        if self.data.len() % 10 == 0 {
            self.compress_layer();
        }
    }
    
    fn compress_layer(&mut self) {
        // Smaller and smaller: Average last 10 values
        if self.data.len() >= 10 {
            let sum: u64 = self.data.iter().rev().take(10).sum();
            let avg = sum / 10;
            self.compressed.push(avg % 196883);
        }
    }
    
    fn size(&self) -> usize {
        self.data.len() + self.compressed.len()
    }
}

// ASCII Cinema recorder
struct ASCIICinema {
    frames: Vec<String>,
    start_time: Instant,
}

impl ASCIICinema {
    fn new() -> Self {
        Self {
            frames: vec![],
            start_time: Instant::now(),
        }
    }
    
    fn record_frame(&mut self, content: &str) {
        let timestamp = self.start_time.elapsed().as_secs_f64();
        let frame = format!("[{:.2}s] {}", timestamp, content);
        self.frames.push(frame);
    }
    
    fn save(&self, path: &str) -> io::Result<()> {
        let content = self.frames.join("\n");
        fs::write(path, content)?;
        Ok(())
    }
}

// Chariot Door Game with recording
struct ChariotDoorGame {
    state: u64,
    rrdb: RRDB,
    cinema: ASCIICinema,
}

impl ChariotDoorGame {
    fn new() -> Self {
        Self {
            state: 0,
            rrdb: RRDB::new(),
            cinema: ASCIICinema::new(),
        }
    }
    
    fn run(&mut self) -> io::Result<()> {
        self.cinema.record_frame("🎴 THE CHARIOT - Door Game VII");
        println!("🎴 THE CHARIOT - Door Game VII");
        println!("================================");
        
        self.cinema.record_frame("📁 Reading Frankfurt files...");
        println!("📁 Reading Frankfurt files...");
        
        // Read and FRACTRAN filter
        let content = fs::read("data/frankfurt.txt")?;
        let mut samples = vec![];
        
        for byte in content {
            self.state = fractran_filter(byte, self.state);
            samples.push(self.state);
            
            // Record progress
            if samples.len() % 100 == 0 {
                let msg = format!("🔄 Processed {} bytes, state={}", samples.len(), self.state);
                self.cinema.record_frame(&msg);
                print!("\r{}", msg);
                io::stdout().flush()?;
            }
        }
        println!();
        
        // Compress into RRDB
        self.cinema.record_frame("🗜️ Compressing into 71 Galois towers...");
        println!("🗜️ Compressing into 71 Galois towers...");
        
        let original_size = samples.len();
        self.rrdb.compress(&samples);
        let compressed_size = self.rrdb.size();
        
        let msg = format!("✅ Compressed: {} → {} bytes", original_size, compressed_size);
        self.cinema.record_frame(&msg);
        println!("{}", msg);
        
        // Chariot reading
        self.cinema.record_frame("🎴 CHARIOT: Victory via FRACTRAN");
        println!("\n🎴 CHARIOT CARD READING:");
        println!("  Direction: Forward");
        println!("  Control: Via FRACTRAN");
        println!("  Compression: {}%", (compressed_size * 100) / original_size);
        println!("  Galois Towers: 71");
        
        // Save recording
        self.cinema.save("recordings/chariot_session.txt")?;
        println!("\n🎬 ASCII Cinema saved to recordings/chariot_session.txt");
        
        Ok(())
    }
}

fn main() -> io::Result<()> {
    fs::create_dir_all("recordings")?;
    let mut game = ChariotDoorGame::new();
    game.run()
}
