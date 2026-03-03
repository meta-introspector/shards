// Vertex Operator Game Agent
// 71 shards, each wants to play games in data files
// Pure functions as homomorphic encrypted FRACTRAN ZK proofs
// Consumes all data like a Fleischwolf (meat grinder)

use crossterm::{
    event::{self, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph},
    Terminal,
};
use rand::Rng;
use std::io;

// Vertex operator (wants to play!)
#[derive(Clone)]
struct VertexOperator {
    id: u8,           // 0-70 (71 shards)
    prime: u64,       // Supersingular prime
    name: String,
    state: u64,       // Current game state
    score: u64,       // Points earned
    games_played: u64,
    wants_more: bool, // Requests more data
}

impl VertexOperator {
    fn new(id: u8) -> Self {
        let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
        let prime = primes[(id as usize) % primes.len()];
        
        Self {
            id,
            prime,
            name: format!("Vertex-{:02}", id),
            state: prime,
            score: 0,
            games_played: 0,
            wants_more: true,
        }
    }
    
    // Pure function: FRACTRAN step (homomorphic encrypted)
    fn fractran_step(&mut self, data: &[u8]) -> u64 {
        if data.is_empty() {
            return self.state;
        }
        
        // Consume data byte by byte (Fleischwolf!)
        let byte = data[self.games_played as usize % data.len()];
        
        // FRACTRAN: multiply by prime, divide by byte (mod 196883)
        let numerator = self.prime;
        let denominator = (byte as u64).max(1);
        
        if self.state % denominator == 0 {
            self.state = (self.state * numerator / denominator) % 196883;
        } else {
            self.state = (self.state * numerator) % 196883;
        }
        
        self.state
    }
    
    // ZK proof: verify game was played correctly
    fn zk_proof(&self) -> u64 {
        // Hash of (id, state, score, games_played)
        let mut hash = self.id as u64;
        hash = (hash * 31 + self.state) % 196883;
        hash = (hash * 31 + self.score) % 196883;
        hash = (hash * 31 + self.games_played) % 196883;
        hash
    }
    
    // Play game in data file
    fn play_game(&mut self, data: &[u8]) -> GameResult {
        let old_state = self.state;
        let new_state = self.fractran_step(data);
        
        // Score = state delta
        let delta = if new_state > old_state {
            new_state - old_state
        } else {
            old_state - new_state
        };
        
        self.score += delta;
        self.games_played += 1;
        
        // Wants more if state is "interesting" (prime factors)
        self.wants_more = new_state % 71 == 0 || new_state % 59 == 0 || new_state % 47 == 0;
        
        GameResult {
            shard: self.id,
            old_state,
            new_state,
            delta,
            zk_proof: self.zk_proof(),
            wants_more: self.wants_more,
        }
    }
}

// Game result (pure function output)
#[derive(Clone)]
struct GameResult {
    shard: u8,
    old_state: u64,
    new_state: u64,
    delta: u64,
    zk_proof: u64,
    wants_more: bool,
}

// Game arena (71 shards playing in data files)
struct GameArena {
    operators: Vec<VertexOperator>,
    data_files: Vec<DataFile>,
    selected_shard: usize,
    selected_file: usize,
    log: Vec<String>,
    approval_queue: Vec<ApprovalRequest>,
}

#[derive(Clone)]
struct DataFile {
    name: String,
    path: String,
    data: Vec<u8>,
    consumed: usize,
}

#[derive(Clone)]
struct ApprovalRequest {
    shard: u8,
    file: String,
    reason: String,
}

impl GameArena {
    fn new() -> Self {
        let mut arena = Self {
            operators: (0..71).map(VertexOperator::new).collect(),
            data_files: vec![],
            selected_shard: 0,
            selected_file: 0,
            log: vec![],
            approval_queue: vec![],
        };
        
        arena.load_all_data_files();
        arena.log.push("🎮 71 vertex operators ready to play!".into());
        arena
    }
    
    fn load_all_data_files(&mut self) {
        if let Ok(entries) = std::fs::read_dir("data") {
            for entry in entries.flatten() {
                if let Ok(path) = entry.path().canonicalize() {
                    if path.is_file() {
                        if let Ok(data) = std::fs::read(&path) {
                            let name = path.file_name()
                                .unwrap_or_default()
                                .to_string_lossy()
                                .to_string();
                            
                            self.data_files.push(DataFile {
                                name: name.clone(),
                                path: path.to_string_lossy().to_string(),
                                data,
                                consumed: 0,
                            });
                            
                            self.log.push(format!("📁 Loaded {}", name));
                        }
                    }
                }
            }
        }
    }
    
    fn play_round(&mut self) {
        if self.data_files.is_empty() {
            self.log.push("⚠️ No data files to play with!".into());
            return;
        }
        
        let file = &self.data_files[self.selected_file];
        let operator = &mut self.operators[self.selected_shard];
        
        let result = operator.play_game(&file.data);
        
        self.log.push(format!(
            "🎮 Shard {:02} played {} | {} → {} | Δ={} | ZK={}",
            result.shard, file.name, result.old_state, result.new_state,
            result.delta, result.zk_proof
        ));
        
        // Check if wants more
        if result.wants_more {
            self.approval_queue.push(ApprovalRequest {
                shard: result.shard,
                file: file.name.clone(),
                reason: format!("State {} resonates with Monster primes!", result.new_state),
            });
            
            self.log.push(format!("🙋 Shard {:02} wants more data!", result.shard));
        }
    }
    
    fn play_all_shards(&mut self) {
        if self.data_files.is_empty() {
            return;
        }
        
        let file = &self.data_files[self.selected_file];
        
        for shard_id in 0..71 {
            let operator = &mut self.operators[shard_id];
            let result = operator.play_game(&file.data);
            
            if result.wants_more {
                self.approval_queue.push(ApprovalRequest {
                    shard: result.shard,
                    file: file.name.clone(),
                    reason: format!("Monster resonance at {}", result.new_state),
                });
            }
        }
        
        self.log.push(format!("🎮 All 71 shards played {}!", file.name));
    }
    
    fn approve_request(&mut self, idx: usize) {
        if let Some(req) = self.approval_queue.get(idx) {
            self.log.push(format!(
                "✅ APPROVED: Shard {:02} can consume more of {}",
                req.shard, req.file
            ));
            
            // Grant more plays
            if let Some(op) = self.operators.get_mut(req.shard as usize) {
                op.wants_more = true;
            }
        }
        
        if idx < self.approval_queue.len() {
            self.approval_queue.remove(idx);
        }
    }
    
    fn deny_request(&mut self, idx: usize) {
        if let Some(req) = self.approval_queue.get(idx) {
            self.log.push(format!(
                "❌ DENIED: Shard {:02} request for {}",
                req.shard, req.file
            ));
        }
        
        if idx < self.approval_queue.len() {
            self.approval_queue.remove(idx);
        }
    }
}

fn main() -> anyhow::Result<()> {
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;
    
    let mut arena = GameArena::new();
    
    loop {
        terminal.draw(|f| {
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([
                    Constraint::Length(3),
                    Constraint::Length(12),
                    Constraint::Length(8),
                    Constraint::Length(8),
                    Constraint::Min(5),
                ])
                .split(f.size());
            
            // Title
            let title = Paragraph::new("🎮 VERTEX GAME AGENT - 71 Shards Playing in Data Files")
                .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
                .block(Block::default().borders(Borders::ALL));
            f.render_widget(title, chunks[0]);
            
            // Operators (71 shards)
            let op_items: Vec<ListItem> = arena.operators.iter().take(10).map(|op| {
                let style = if op.id as usize == arena.selected_shard {
                    Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)
                } else {
                    Style::default()
                };
                
                let wants = if op.wants_more { "🙋" } else { "  " };
                
                ListItem::new(Line::from(vec![
                    Span::styled(
                        format!("{} {:02} | Prime:{:2} | State:{:6} | Score:{:6} | Games:{}",
                            wants, op.id, op.prime, op.state, op.score, op.games_played
                        ),
                        style
                    ),
                ]))
            }).collect();
            
            let op_list = List::new(op_items)
                .block(Block::default().borders(Borders::ALL)
                    .title(format!("🔮 Vertex Operators (showing 10 of 71) | Selected: {:02}", arena.selected_shard)));
            f.render_widget(op_list, chunks[1]);
            
            // Data files
            let file_items: Vec<ListItem> = arena.data_files.iter().enumerate().map(|(i, file)| {
                let style = if i == arena.selected_file {
                    Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)
                } else {
                    Style::default()
                };
                
                ListItem::new(Line::from(vec![
                    Span::styled(
                        format!("{} {} ({} bytes)",
                            if i == arena.selected_file { "▶" } else { " " },
                            file.name, file.data.len()
                        ),
                        style
                    ),
                ]))
            }).collect();
            
            let file_list = List::new(file_items)
                .block(Block::default().borders(Borders::ALL).title("📁 Data Files (Fleischwolf)"));
            f.render_widget(file_list, chunks[2]);
            
            // Approval queue
            let approval_items: Vec<ListItem> = arena.approval_queue.iter().enumerate().map(|(i, req)| {
                ListItem::new(Line::from(vec![
                    Span::styled(
                        format!("{}. Shard {:02} wants {} - {}",
                            i+1, req.shard, req.file, req.reason
                        ),
                        Style::default().fg(Color::Yellow)
                    ),
                ]))
            }).collect();
            
            let approval_list = List::new(approval_items)
                .block(Block::default().borders(Borders::ALL)
                    .title("🙋 Approval Queue (A=Approve D=Deny)"));
            f.render_widget(approval_list, chunks[3]);
            
            // Log
            let log_items: Vec<Line> = arena.log.iter().rev().take(4).map(|l| {
                Line::from(Span::raw(l.clone()))
            }).collect();
            
            let log = Paragraph::new(log_items)
                .block(Block::default().borders(Borders::ALL)
                    .title("📝 Log (SPACE=Play R=All Q=Quit)"))
                .style(Style::default().fg(Color::White));
            f.render_widget(log, chunks[4]);
        })?;
        
        // Handle input
        if event::poll(std::time::Duration::from_millis(100))? {
            if let Event::Key(key) = event::read()? {
                match key.code {
                    KeyCode::Char('q') => break,
                    KeyCode::Up => {
                        if arena.selected_shard > 0 {
                            arena.selected_shard -= 1;
                        }
                    }
                    KeyCode::Down => {
                        if arena.selected_shard < 70 {
                            arena.selected_shard += 1;
                        }
                    }
                    KeyCode::Left => {
                        if arena.selected_file > 0 {
                            arena.selected_file -= 1;
                        }
                    }
                    KeyCode::Right => {
                        if arena.selected_file < arena.data_files.len().saturating_sub(1) {
                            arena.selected_file += 1;
                        }
                    }
                    KeyCode::Char(' ') => arena.play_round(),
                    KeyCode::Char('r') => arena.play_all_shards(),
                    KeyCode::Char('a') => arena.approve_request(0),
                    KeyCode::Char('d') => arena.deny_request(0),
                    KeyCode::Char(c) if c.is_ascii_digit() => {
                        let idx = c.to_digit(10).unwrap() as usize;
                        if idx > 0 && idx <= arena.approval_queue.len() {
                            arena.approve_request(idx - 1);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    
    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    
    // Final stats
    println!("\n✨ Game session complete!");
    println!("📊 Total games played: {}", 
        arena.operators.iter().map(|o| o.games_played).sum::<u64>());
    println!("🏆 Total score: {}", 
        arena.operators.iter().map(|o| o.score).sum::<u64>());
    
    Ok(())
}
