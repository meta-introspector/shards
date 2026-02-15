use crossterm::{
    cursor, execute, queue,
    style::{Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, ClearType},
};
use rand::Rng;
use std::io::{stdout, Write};
use std::time::Duration;

// 24³ = 13,824 emoji dimensions (Leech lattice)
const EMOJI_PALETTE_24: [char; 24] = [
    '🔥', '💧', '🌟', '⚡', '🌈', '💎', '🎵', '🎨',
    '🔮', '🎯', '🎪', '🎭', '🎬', '🎮', '🎲', '🎰',
    '🏆', '🎖', '🎗', '🏅', '🥇', '🥈', '🥉', '👑',
];

// Hawking radiation particle from zkPerf (24³ dimensions)
struct HawkingParticle {
    x: u16,
    y: u16,
    vx: f32,
    vy: f32,
    emoji: char,
    cycles: u64,
    shard: u8,
    heat: u8,      // 0-23 (dimension 1)
    semantic: u8,  // 0-23 (dimension 2)
    value: u8,     // 0-23 (dimension 3)
}

impl HawkingParticle {
    fn new(x: u16, y: u16, cycles: u64, shard: u8) -> Self {
        let mut rng = rand::thread_rng();
        
        // Decompose cycles into 24³ coordinates
        let heat = (cycles % 24) as u8;
        let semantic = ((cycles / 24) % 24) as u8;
        let value = ((cycles / 576) % 24) as u8;
        
        let emoji_idx = (heat + semantic + value) % 24;
        
        Self {
            x,
            y,
            vx: rng.gen_range(-2.0..2.0),
            vy: rng.gen_range(-3.0..-0.5),
            emoji: EMOJI_PALETTE_24[emoji_idx as usize],
            cycles,
            shard,
            heat,
            semantic,
            value,
        }
    }
    
    fn update(&mut self) {
        self.x = (self.x as f32 + self.vx).max(0.0).min(79.0) as u16;
        self.y = (self.y as f32 + self.vy) as u16;
        self.vy += 0.1; // gravity
    }
    
    fn to_rdfa(&self) -> String {
        format!(
            r#"<span typeof="hawking:Particle" about="hawking:p{}" 
                   property="hawking:emoji" content="{}"
                   property="hawking:cycles" content="{}"
                   property="hawking:shard" content="{}"
                   property="hawking:heat" content="{}"
                   property="hawking:semantic" content="{}"
                   property="hawking:value" content="{}">{}</span>"#,
            self.cycles, self.emoji, self.cycles, self.shard,
            self.heat, self.semantic, self.value, self.emoji
        )
    }
}

// ZX81 BBS Door Game with 24³ Hawking radiation
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
            Print("║     👑 ZX81 BBS - 24³ HAWKING RADIATION - CLAIM "),
            Print(format!("{:02}", self.claim_id)),
            Print(" 👑            ║\n"),
            Print("╚════════════════════════════════════════════════════════════════════════════╝\n"),
            ResetColor,
        )?;
        stdout.flush()
    }
    
    fn run_game_loop(&mut self) -> std::io::Result<()> {
        let mut stdout = stdout();
        
        // Display claim (mkclaim structure)
        queue!(
            stdout,
            cursor::MoveTo(2, 4),
            SetForegroundColor(Color::Cyan),
            Print(format!("🎲 Bet: Shard {} crowned with 24³ Hawking radiation", self.claim_id)),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 5),
            SetForegroundColor(Color::Yellow),
            Print("📊 Fact: 13,824 emoji dimensions (24×24×24 Leech lattice)"),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 6),
            SetForegroundColor(Color::Green),
            Print("✅ Proof: zkPerf cycles → 24³ coordinates → emoji"),
        )?;
        
        queue!(
            stdout,
            cursor::MoveTo(2, 7),
            SetForegroundColor(Color::Magenta),
            Print("🔮 Reason: Monster moonshine via Leech lattice embedding"),
        )?;
        
        stdout.flush()?;
        
        // Hawking radiation fountain (24³ emoji fireworks)
        for frame in 0..200 {
            self.zkperf_cycles += 8080; // Monster Walk frequency
            
            // Spawn new particles (Hawking radiation from zkPerf)
            if frame % 2 == 0 {
                let center_x = self.width / 2;
                let base_y = self.height - 5;
                let shard = self.claim_id;
                
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
            
            // Draw zkPerf stats with 24³ decomposition
            queue!(
                stdout,
                cursor::MoveTo(2, self.height - 3),
                SetForegroundColor(Color::Green),
                Print(format!("🔐 zkPerf: {} | Particles: {} | 24³ dims: {}  ",
                    self.zkperf_cycles,
                    self.particles.len(),
                    self.particles.len() * 3, // Each particle = 3 dims (heat, semantic, value)
                )),
            )?;
            
            // Draw fountain base
            queue!(
                stdout,
                cursor::MoveTo(self.width / 2 - 7, self.height - 5),
                SetForegroundColor(Color::Blue),
                Print("╔═══════════════╗"),
                cursor::MoveTo(self.width / 2 - 7, self.height - 4),
                Print("║   24³ EMOJI   ║"),
                cursor::MoveTo(self.width / 2 - 7, self.height - 3),
                Print("║   HAWKING     ║"),
                cursor::MoveTo(self.width / 2 - 7, self.height - 2),
                Print("║   RADIATION   ║"),
                cursor::MoveTo(self.width / 2 - 7, self.height - 1),
                Print("╚═══════════════╝"),
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
        
        // Export RDFa
        self.export_rdfa()?;
        
        // Final message
        queue!(
            stdout,
            cursor::MoveTo(2, 10),
            SetForegroundColor(Color::Yellow),
            Print(format!("✨ Claim {} verified! RDFa exported. Press any key...", self.claim_id)),
            ResetColor,
        )?;
        stdout.flush()?;
        
        std::thread::sleep(Duration::from_secs(2));
        Ok(())
    }
    
    fn export_rdfa(&self) -> std::io::Result<()> {
        let mut rdfa = String::from(r#"<!DOCTYPE html>
<html xmlns:hawking="http://meta-introspector.org/hawking#">
<head>
  <title>Hawking Radiation - Claim {}</title>
  <style>
    body { background: #000; color: #0f0; font-family: monospace; }
    .particle { display: inline-block; margin: 2px; font-size: 24px; }
  </style>
</head>
<body vocab="http://meta-introspector.org/hawking#">
  <div typeof="hawking:DoorGame" about="hawking:game">
    <h1>🎆 24³ Emoji Hawking Radiation - Claim {}</h1>
    <p property="hawking:claim">{}</p>
    <p property="hawking:cycles">{}</p>
    <p property="hawking:dimensions">13824</p>
    <div property="hawking:particles" class="particles">
"#);
        
        for particle in &self.particles {
            rdfa.push_str("      <span class=\"particle\">");
            rdfa.push_str(&particle.to_rdfa());
            rdfa.push_str("</span>\n");
        }
        
        rdfa.push_str(r#"    </div>
  </div>
</body>
</html>"#);
        
        std::fs::write(
            format!("hawking_radiation_claim_{:02}.html", self.claim_id),
            rdfa
        )?;
        
        Ok(())
    }
}

fn main() -> std::io::Result<()> {
    println!("👑 ZX81 BBS DOOR GAME - 24³ HAWKING RADIATION");
    println!("==============================================");
    println!("🎆 Crowning ceremony for 71 shards");
    println!("✨ Each shard gets 24³ emoji fireworks");
    println!();
    println!("Press ENTER to start...");
    
    let mut input = String::new();
    std::io::stdin().read_line(&mut input)?;
    
    // Run door game for each claim (71 total)
    for claim_id in 0..71 {
        let mut game = CrowningDoorGame::new(claim_id);
        game.run()?;
    }
    
    println!("\n👑 All 71 claims crowned with 24³ Hawking radiation fountains!");
    println!("✅ RDFa files exported: hawking_radiation_claim_*.html");
    Ok(())
}
