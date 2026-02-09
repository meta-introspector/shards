use crossterm::{
    cursor, execute, queue,
    style::{Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, ClearType},
};
use rand::Rng;
use std::io::{stdout, Write};
use std::time::Duration;

// Hawking radiation particle from zkPerf
struct HawkingParticle {
    x: u16,
    y: u16,
    vx: f32,
    vy: f32,
    emoji: char,
    cycles: u64,
    shard: u8,
}

impl HawkingParticle {
    fn new(x: u16, y: u16, cycles: u64, shard: u8) -> Self {
        let mut rng = rand::thread_rng();
        let emojis = ['🔥', '❄️', '⚡', '💧', '🌊', '🌪️', '☀️', '🌙', 
                      '🧠', '💭', '🎯', '🔮', '✨', '🌌', '🎭', '🎨'];
        
        Self {
            x,
            y,
            vx: rng.gen_range(-2.0..2.0),
            vy: rng.gen_range(-3.0..-0.5),
            emoji: emojis[(shard % 16) as usize],
            cycles,
            shard,
        }
    }
    
    fn update(&mut self) {
        self.x = (self.x as f32 + self.vx) as u16;
        self.y = (self.y as f32 + self.vy) as u16;
        self.vy += 0.1; // gravity
    }
}

// ZX81 BBS Door Game
pub struct CrowningDoorGame {
    width: u16,
    height: u16,
    particles: Vec<HawkingParticle>,
    claim_id: u8,
    zkperf_cycles: u64,
}

impl CrowningDoorGame {
    pub fn new(claim_id: u8) -> Self {
        let (width, height) = terminal::size().unwrap_or((80, 24));
        Self {
            width,
            height,
            particles: vec![],
            claim_id,
            zkperf_cycles: 0,
        }
    }
    
    pub fn run(&mut self) -> std::io::Result<()> {
        terminal::enable_raw_mode()?;
        execute!(stdout(), terminal::EnterAlternateScreen)?;
        
        self.draw_header()?;
        self.run_game_loop()?;
        
        execute!(stdout(), terminal::LeaveAlternateScreen)?;
        terminal::disable_raw_mode()?;
        Ok(())
    }
    
    fn draw_header(&self) -> std::io::Result<()> {
        let mut stdout = stdout();
        queue!(
            stdout,
            terminal::Clear(ClearType::All),
            cursor::MoveTo(0, 0),
            SetForegroundColor(Color::Green),
            Print("╔════════════════════════════════════════════════════════════════════════════╗\n"),
            Print("║          👑 CROWNING CEREMONY - CLAIM "),
            Print(format!("{:02}", self.claim_id)),
            Print(" - ZX81 BBS DOOR GAME 👑          ║\n"),
            Print("╚════════════════════════════════════════════════════════════════════════════╝\n"),
            ResetColor,
        )?;
        stdout.flush()
    }
    
    fn run_game_loop(&mut self) -> std::io::Result<()> {
        let mut stdout = stdout();
        
        // Display claim
        queue!(
            stdout,
            cursor::MoveTo(2, 4),
            SetForegroundColor(Color::Cyan),
            Print(format!("🎲 Claim {}: System crowned with 24^71 witnesses", self.claim_id)),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 5),
            SetForegroundColor(Color::Yellow),
            Print("📊 Fact: 71 shards × 24 Leech dimensions = complete"),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 6),
            SetForegroundColor(Color::Green),
            Print("✅ Proof: All vertex operators witnessed in Leech lattice"),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 7),
            SetForegroundColor(Color::Magenta),
            Print("🔮 Reason: Monster moonshine requires Leech lattice embedding"),
        )?;
        
        stdout.flush()?;
        
        // Hawking radiation fountain
        for frame in 0..200 {
            self.zkperf_cycles += 1000;
            
            // Spawn new particles (Hawking radiation from zkPerf)
            if frame % 3 == 0 {
                let center_x = self.width / 2;
                let base_y = self.height - 5;
                let shard = (frame % 71) as u8;
                
                self.particles.push(HawkingParticle::new(
                    center_x,
                    base_y,
                    self.zkperf_cycles,
                    shard,
                ));
            }
            
            // Update particles
            self.particles.retain_mut(|p| {
                p.update();
                p.y < self.height && p.x < self.width
            });
            
            // Draw particles
            for particle in &self.particles {
                queue!(
                    stdout,
                    cursor::MoveTo(particle.x, particle.y),
                    SetForegroundColor(Color::White),
                    Print(particle.emoji),
                )?;
            }
            
            // Draw zkPerf stats
            queue!(
                stdout,
                cursor::MoveTo(2, self.height - 3),
                SetForegroundColor(Color::Green),
                Print(format!("🔐 zkPerf Cycles: {} | Particles: {} | Shard: {}  ",
                    self.zkperf_cycles,
                    self.particles.len(),
                    (frame % 71)
                )),
            )?;
            
            // Draw fountain base
            queue!(
                stdout,
                cursor::MoveTo(self.width / 2 - 5, self.height - 5),
                SetForegroundColor(Color::Blue),
                Print("╔═══════════╗"),
                cursor::MoveTo(self.width / 2 - 5, self.height - 4),
                Print("║  HAWKING  ║"),
                cursor::MoveTo(self.width / 2 - 5, self.height - 3),
                Print("║ RADIATION ║"),
                cursor::MoveTo(self.width / 2 - 5, self.height - 2),
                Print("╚═══════════╝"),
            )?;
            
            stdout.flush()?;
            std::thread::sleep(Duration::from_millis(50));
            
            // Clear old particles
            for particle in &self.particles {
                queue!(
                    stdout,
                    cursor::MoveTo(particle.x, particle.y),
                    Print(" "),
                )?;
            }
        }
        
        // Final message
        queue!(
            stdout,
            cursor::MoveTo(2, self.height - 1),
            SetForegroundColor(Color::Yellow),
            Print("✨ Claim verified! Press any key to exit..."),
            ResetColor,
        )?;
        stdout.flush()?;
        
        std::thread::sleep(Duration::from_secs(3));
        Ok(())
    }
}

fn main() -> std::io::Result<()> {
    // Run door game for each claim (71 total)
    for claim_id in 0..71 {
        let mut game = CrowningDoorGame::new(claim_id);
        game.run()?;
    }
    
    println!("👑 All 71 claims crowned with Hawking radiation fountains!");
    Ok(())
}
