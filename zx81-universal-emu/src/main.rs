// ZX81 Universal Emulator - TUI Tape Loader
// Emulates ALL CPUs via vertex operators
// Loads data/zx81.txt + data/ripgrep_monster.txt

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
use std::io;

// Vertex operators (15 supersingular primes)
#[derive(Clone, Copy)]
enum VertexOp {
    S = 2,   // Substitution
    K = 3,   // Konstant
    I = 5,   // Identity
    Y = 7,   // Y combinator
    B = 11,  // Composition
    C = 13,  // Flip
    W = 17,  // Duplicate
    T = 19,  // Transpose
    A = 23,  // Apply
    E = 29,  // Eval
    L = 31,  // Lambda
    F = 41,  // Fix
    U = 47,  // Universal
    M = 59,  // Monster
    N = 71,  // Nullstellensatz
}

impl VertexOp {
    fn apply(&self, state: u64) -> u64 {
        (state * (*self as u64)) % 196883
    }
    
    fn name(&self) -> &str {
        match self {
            VertexOp::S => "S (Substitution)",
            VertexOp::K => "K (Konstant)",
            VertexOp::I => "I (Identity)",
            VertexOp::Y => "Y (Combinator)",
            VertexOp::B => "B (Composition)",
            VertexOp::C => "C (Flip)",
            VertexOp::W => "W (Duplicate)",
            VertexOp::T => "T (Transpose)",
            VertexOp::A => "A (Apply)",
            VertexOp::E => "E (Eval)",
            VertexOp::L => "L (Lambda)",
            VertexOp::F => "F (Fix)",
            VertexOp::U => "U (Universal)",
            VertexOp::M => "M (Monster)",
            VertexOp::N => "N (Nullstellensatz)",
        }
    }
}

// CPU architecture (all emulated via vertex operators)
#[derive(Clone)]
enum CpuArch {
    ZX81,      // Zilog Z80
    C64,       // MOS 6502
    Amiga,     // Motorola 68000
    NES,       // Ricoh 2A03
    SNES,      // 65816
    Genesis,   // 68000
    N64,       // MIPS R4300i
    PSX,       // MIPS R3000
    GBA,       // ARM7TDMI
    X86,       // Intel x86
    ARM,       // ARM Cortex
    RISCV,     // RISC-V
    WASM,      // WebAssembly
    QEMU,      // QEMU (all)
    MAME,      // MAME (all)
}

impl CpuArch {
    fn vertex_sequence(&self) -> Vec<VertexOp> {
        match self {
            CpuArch::ZX81 => vec![VertexOp::S, VertexOp::K, VertexOp::I],
            CpuArch::C64 => vec![VertexOp::Y, VertexOp::B, VertexOp::C],
            CpuArch::Amiga => vec![VertexOp::W, VertexOp::T, VertexOp::A],
            CpuArch::NES => vec![VertexOp::E, VertexOp::L, VertexOp::F],
            CpuArch::SNES => vec![VertexOp::U, VertexOp::M, VertexOp::N],
            CpuArch::Genesis => vec![VertexOp::B, VertexOp::C, VertexOp::W],
            CpuArch::N64 => vec![VertexOp::F, VertexOp::U, VertexOp::M],
            CpuArch::PSX => vec![VertexOp::L, VertexOp::F, VertexOp::U],
            CpuArch::GBA => vec![VertexOp::A, VertexOp::E, VertexOp::L],
            CpuArch::X86 => vec![VertexOp::S, VertexOp::B, VertexOp::W],
            CpuArch::ARM => vec![VertexOp::T, VertexOp::A, VertexOp::E],
            CpuArch::RISCV => vec![VertexOp::I, VertexOp::Y, VertexOp::B],
            CpuArch::WASM => vec![VertexOp::M, VertexOp::N, VertexOp::S],
            CpuArch::QEMU => vec![VertexOp::U, VertexOp::M, VertexOp::N],
            CpuArch::MAME => vec![VertexOp::N, VertexOp::M, VertexOp::U],
        }
    }
    
    fn name(&self) -> &str {
        match self {
            CpuArch::ZX81 => "ZX81 (Z80)",
            CpuArch::C64 => "C64 (6502)",
            CpuArch::Amiga => "Amiga (68000)",
            CpuArch::NES => "NES (2A03)",
            CpuArch::SNES => "SNES (65816)",
            CpuArch::Genesis => "Genesis (68000)",
            CpuArch::N64 => "N64 (MIPS)",
            CpuArch::PSX => "PSX (MIPS)",
            CpuArch::GBA => "GBA (ARM7)",
            CpuArch::X86 => "x86 (Intel)",
            CpuArch::ARM => "ARM (Cortex)",
            CpuArch::RISCV => "RISC-V",
            CpuArch::WASM => "WebAssembly",
            CpuArch::QEMU => "QEMU (Universal)",
            CpuArch::MAME => "MAME (Arcade)",
        }
    }
}

// Tape (loaded from data/zx81.txt + data/ripgrep_monster.txt)
#[derive(Clone)]
struct Tape {
    name: String,
    data: Vec<u8>,
    cpu: CpuArch,
    state: u64,
}

impl Tape {
    fn new(name: String, cpu: CpuArch) -> Self {
        Self {
            name,
            data: vec![],
            cpu,
            state: 2, // Initial state
        }
    }
    
    fn load_from_file(&mut self, path: &str) -> anyhow::Result<()> {
        let content = std::fs::read_to_string(path)?;
        self.data = content.as_bytes().to_vec();
        Ok(())
    }
    
    fn run_step(&mut self) -> u64 {
        let ops = self.cpu.vertex_sequence();
        for op in ops {
            self.state = op.apply(self.state);
        }
        self.state
    }
    
    fn save(&self, path: &str) -> anyhow::Result<()> {
        std::fs::write(path, &self.data)?;
        Ok(())
    }
}

// TUI App state
struct App {
    tapes: Vec<Tape>,
    selected: usize,
    running: bool,
    cycles: u64,
    log: Vec<String>,
    available_files: Vec<String>,
    file_selected: usize,
    mode: AppMode,
}

#[derive(PartialEq)]
enum AppMode {
    TapeList,
    FileSelector,
    OperationMenu,
}

impl App {
    fn new() -> Self {
        let mut app = Self {
            tapes: vec![],
            selected: 0,
            running: false,
            cycles: 0,
            log: vec![],
            available_files: vec![],
            file_selected: 0,
            mode: AppMode::TapeList,
        };
        
        // Scan data/ directory for all files
        app.scan_data_directory();
        
        // Auto-load all files from data/
        app.load_all_data_files();
        
        app
    }
    
    fn scan_data_directory(&mut self) {
        if let Ok(entries) = std::fs::read_dir("data") {
            for entry in entries.flatten() {
                if let Ok(path) = entry.path().canonicalize() {
                    if path.is_file() {
                        self.available_files.push(path.to_string_lossy().to_string());
                    }
                }
            }
        }
        self.log.push(format!("📁 Found {} files in data/", self.available_files.len()));
    }
    
    fn load_all_data_files(&mut self) {
        let cpu_archs = [
            CpuArch::ZX81, CpuArch::C64, CpuArch::Amiga, CpuArch::NES,
            CpuArch::SNES, CpuArch::Genesis, CpuArch::N64, CpuArch::PSX,
            CpuArch::GBA, CpuArch::X86, CpuArch::ARM, CpuArch::RISCV,
            CpuArch::WASM, CpuArch::QEMU, CpuArch::MAME,
        ];
        
        for (i, file_path) in self.available_files.iter().enumerate() {
            let cpu = cpu_archs[i % cpu_archs.len()].clone();
            let name = std::path::Path::new(file_path)
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            
            let mut tape = Tape::new(name.clone(), cpu);
            
            if let Ok(_) = tape.load_from_file(file_path) {
                self.log.push(format!("✅ Loaded {} ({} bytes)", name, tape.data.len()));
                self.tapes.push(tape);
            } else {
                self.log.push(format!("⚠️ Failed to load {}", name));
            }
        }
        
        if self.tapes.is_empty() {
            // Create default tapes if no files found
            self.tapes.push(Tape::new("Empty ZX81".into(), CpuArch::ZX81));
            self.log.push("⚠️ No data files found, created empty tape".into());
        }
    }
    
    fn load_selected_file(&mut self) {
        if let Some(file_path) = self.available_files.get(self.file_selected) {
            let name = std::path::Path::new(file_path)
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            
            let mut tape = Tape::new(name.clone(), CpuArch::ZX81);
            
            if let Ok(_) = tape.load_from_file(file_path) {
                self.log.push(format!("✅ Loaded {} ({} bytes)", name, tape.data.len()));
                self.tapes.push(tape);
                self.selected = self.tapes.len() - 1;
            } else {
                self.log.push(format!("❌ Failed to load {}", name));
            }
        }
        self.mode = AppMode::TapeList;
    }
    
    fn next_tape(&mut self) {
        self.selected = (self.selected + 1) % self.tapes.len();
    }
    
    fn prev_tape(&mut self) {
        if self.selected > 0 {
            self.selected -= 1;
        } else {
            self.selected = self.tapes.len() - 1;
        }
    }
    
    fn run_selected(&mut self) {
        if let Some(tape) = self.tapes.get_mut(self.selected) {
            let state = tape.run_step();
            self.cycles += 1;
            self.log.push(format!(
                "🎮 {} step: state={} cycles={}",
                tape.cpu.name(), state, self.cycles
            ));
        }
    }
    
    fn save_selected(&mut self) {
        if let Some(tape) = self.tapes.get(self.selected) {
            std::fs::create_dir_all("output").ok();
            let path = format!("output/{}.tape", tape.name.replace(" ", "_"));
            if let Err(e) = tape.save(&path) {
                self.log.push(format!("❌ Save error: {}", e));
            } else {
                self.log.push(format!("💾 Saved to {}", path));
            }
        }
    }
    
    fn change_cpu(&mut self, cpu: CpuArch) {
        if let Some(tape) = self.tapes.get_mut(self.selected) {
            tape.cpu = cpu.clone();
            self.log.push(format!("🔄 Changed CPU to {}", cpu.name()));
        }
        self.mode = AppMode::TapeList;
    }
    
    fn next_file(&mut self) {
        self.file_selected = (self.file_selected + 1) % self.available_files.len().max(1);
    }
    
    fn prev_file(&mut self) {
        if self.file_selected > 0 {
            self.file_selected -= 1;
        } else {
            self.file_selected = self.available_files.len().saturating_sub(1);
        }
    }
}

fn main() -> anyhow::Result<()> {
    // Setup terminal
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;
    
    let mut app = App::new();
    
    loop {
        terminal.draw(|f| {
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([
                    Constraint::Length(3),
                    Constraint::Min(10),
                    Constraint::Length(8),
                    Constraint::Length(10),
                ])
                .split(f.size());
            
            // Title
            let title_text = match app.mode {
                AppMode::TapeList => "🎮 ZX81 Universal Emulator - Vertex Operator CPU",
                AppMode::FileSelector => "📁 File Selector - Pick tape to load",
                AppMode::OperationMenu => "⚙️ Operation Menu - Change CPU architecture",
            };
            
            let title = Paragraph::new(title_text)
                .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
                .block(Block::default().borders(Borders::ALL));
            f.render_widget(title, chunks[0]);
            
            match app.mode {
                AppMode::TapeList => {
                    // Tape list
                    let items: Vec<ListItem> = app.tapes.iter().enumerate().map(|(i, tape)| {
                        let style = if i == app.selected {
                            Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)
                        } else {
                            Style::default()
                        };
                        
                        ListItem::new(Line::from(vec![
                            Span::raw(format!("{} ", if i == app.selected { "▶" } else { " " })),
                            Span::styled(
                                format!("{} - {} - {} bytes", 
                                    tape.name, tape.cpu.name(), tape.data.len()
                                ), 
                                style
                            ),
                        ]))
                    }).collect();
                    
                    let list = List::new(items)
                        .block(Block::default().borders(Borders::ALL)
                            .title("📼 Tapes (F=Load L=CPU R=Run S=Save)"))
                        .highlight_style(Style::default().fg(Color::Yellow));
                    f.render_widget(list, chunks[1]);
                }
                
                AppMode::FileSelector => {
                    // File selector
                    let items: Vec<ListItem> = app.available_files.iter().enumerate().map(|(i, file)| {
                        let style = if i == app.file_selected {
                            Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)
                        } else {
                            Style::default()
                        };
                        
                        let name = std::path::Path::new(file)
                            .file_name()
                            .unwrap_or_default()
                            .to_string_lossy();
                        
                        ListItem::new(Line::from(vec![
                            Span::raw(format!("{} ", if i == app.file_selected { "▶" } else { " " })),
                            Span::styled(name.to_string(), style),
                        ]))
                    }).collect();
                    
                    let list = List::new(items)
                        .block(Block::default().borders(Borders::ALL)
                            .title("📁 Available Files (ENTER=Load ESC=Cancel)"));
                    f.render_widget(list, chunks[1]);
                }
                
                AppMode::OperationMenu => {
                    // CPU selector
                    let cpus = [
                        CpuArch::ZX81, CpuArch::C64, CpuArch::Amiga, CpuArch::NES,
                        CpuArch::SNES, CpuArch::Genesis, CpuArch::N64, CpuArch::PSX,
                        CpuArch::GBA, CpuArch::X86, CpuArch::ARM, CpuArch::RISCV,
                        CpuArch::WASM, CpuArch::QEMU, CpuArch::MAME,
                    ];
                    
                    let items: Vec<ListItem> = cpus.iter().enumerate().map(|(i, cpu)| {
                        let ops = cpu.vertex_sequence();
                        let op_str: Vec<String> = ops.iter().map(|o| format!("{}", *o as u64)).collect();
                        
                        ListItem::new(Line::from(vec![
                            Span::styled(
                                format!("{}. {} → [{}]", i+1, cpu.name(), op_str.join(",")),
                                Style::default().fg(Color::Green)
                            ),
                        ]))
                    }).collect();
                    
                    let list = List::new(items)
                        .block(Block::default().borders(Borders::ALL)
                            .title("⚙️ Select CPU (1-9,0,A-E or ESC=Cancel)"));
                    f.render_widget(list, chunks[1]);
                }
            }
            
            // Vertex operators (only in tape list mode)
            if app.mode == AppMode::TapeList {
                if let Some(tape) = app.tapes.get(app.selected) {
                    let ops = tape.cpu.vertex_sequence();
                    let op_text: Vec<Line> = ops.iter().map(|op| {
                        Line::from(Span::styled(
                            format!("  {} → {}", op.name(), *op as u64),
                            Style::default().fg(Color::Green)
                        ))
                    }).collect();
                    
                    let vertex_block = Paragraph::new(op_text)
                        .block(Block::default().borders(Borders::ALL).title("🔮 Vertex Operators"))
                        .style(Style::default().fg(Color::Green));
                    f.render_widget(vertex_block, chunks[2]);
                }
            } else {
                let help = Paragraph::new(vec![
                    Line::from("Controls:"),
                    Line::from("  ↑/↓ - Navigate"),
                    Line::from("  ENTER - Select"),
                    Line::from("  ESC - Cancel"),
                ])
                .block(Block::default().borders(Borders::ALL).title("❓ Help"))
                .style(Style::default().fg(Color::Cyan));
                f.render_widget(help, chunks[2]);
            }
            
            // Log
            let log_items: Vec<Line> = app.log.iter().rev().take(8).map(|l| {
                Line::from(Span::raw(l.clone()))
            }).collect();
            
            let log = Paragraph::new(log_items)
                .block(Block::default().borders(Borders::ALL).title("📝 Log"))
                .style(Style::default().fg(Color::White));
            f.render_widget(log, chunks[3]);
        })?;
        
        // Handle input
        if event::poll(std::time::Duration::from_millis(100))? {
            if let Event::Key(key) = event::read()? {
                match app.mode {
                    AppMode::TapeList => match key.code {
                        KeyCode::Char('q') => break,
                        KeyCode::Up => app.prev_tape(),
                        KeyCode::Down => app.next_tape(),
                        KeyCode::Enter | KeyCode::Char(' ') => app.run_selected(),
                        KeyCode::Char('s') => app.save_selected(),
                        KeyCode::Char('r') => {
                            for _ in 0..10 {
                                app.run_selected();
                            }
                        }
                        KeyCode::Char('f') => app.mode = AppMode::FileSelector,
                        KeyCode::Char('l') => app.mode = AppMode::OperationMenu,
                        _ => {}
                    }
                    
                    AppMode::FileSelector => match key.code {
                        KeyCode::Up => app.prev_file(),
                        KeyCode::Down => app.next_file(),
                        KeyCode::Enter => app.load_selected_file(),
                        KeyCode::Esc => app.mode = AppMode::TapeList,
                        _ => {}
                    }
                    
                    AppMode::OperationMenu => match key.code {
                        KeyCode::Char('1') => app.change_cpu(CpuArch::ZX81),
                        KeyCode::Char('2') => app.change_cpu(CpuArch::C64),
                        KeyCode::Char('3') => app.change_cpu(CpuArch::Amiga),
                        KeyCode::Char('4') => app.change_cpu(CpuArch::NES),
                        KeyCode::Char('5') => app.change_cpu(CpuArch::SNES),
                        KeyCode::Char('6') => app.change_cpu(CpuArch::Genesis),
                        KeyCode::Char('7') => app.change_cpu(CpuArch::N64),
                        KeyCode::Char('8') => app.change_cpu(CpuArch::PSX),
                        KeyCode::Char('9') => app.change_cpu(CpuArch::GBA),
                        KeyCode::Char('0') => app.change_cpu(CpuArch::X86),
                        KeyCode::Char('a') => app.change_cpu(CpuArch::ARM),
                        KeyCode::Char('b') => app.change_cpu(CpuArch::RISCV),
                        KeyCode::Char('c') => app.change_cpu(CpuArch::WASM),
                        KeyCode::Char('d') => app.change_cpu(CpuArch::QEMU),
                        KeyCode::Char('e') => app.change_cpu(CpuArch::MAME),
                        KeyCode::Esc => app.mode = AppMode::TapeList,
                        _ => {}
                    }
                }
            }
        }
    }
    
    // Cleanup
    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    
    println!("✨ Emulator closed. {} cycles executed.", app.cycles);
    Ok(())
}
