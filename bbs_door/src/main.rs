// Monster Arcade BBS Door
// Copyright (C) 2026 Meta-Introspector
// 
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published
// by the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//
// Commercial licenses (MIT/Apache-2.0) available: shards@solfunmeme.com
// ZK hackers gotta eat! 🍕

use crossterm::{
    cursor, execute, queue, style::{Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, Clear, ClearType}, event::{self, Event, KeyCode}
};
use std::io::{stdout, Write};

const WIDTH: usize = 150;
const EMOJIS: [&str; 71] = [
    "🎯", "🎮", "🎲", "🎰", "🎪", "🎨", "🎭", "🎬", "🎤", "🎧",
    "🎼", "🎹", "🎺", "🎻", "🎸", "🥁", "🎷", "🎵", "🎶", "🎙️",
    "🔮", "🔭", "🔬", "🔨", "🔧", "🔩", "⚙️", "🔗", "⛓️", "🧲",
    "🧪", "🧬", "🧫", "🧯", "🧰", "🧱", "🧲", "🧳", "🧴", "🧵",
    "🧶", "🧷", "🧸", "🧹", "🧺", "🧻", "🧼", "🧽", "🧾", "🧿",
    "🌀", "🌁", "🌂", "🌃", "🌄", "🌅", "🌆", "🌇", "🌈", "🌉",
    "🌊", "🌋", "🌌", "🌍", "🌎", "🌏", "🌐", "🌑", "🌒", "🌓", "🌔"
];

const NAMES: [&str; 71] = [
    "Pixel Hunt", "Maze Run", "Block Drop", "Spin Win", "Ring Toss",
    "Color Match", "Shape Shift", "Light Show", "Beat Box", "Sound Wave",
    "Note Chase", "Key Press", "Horn Blast", "String Pull", "Chord Strike",
    "Drum Roll", "Sax Solo", "Melody Mix", "Rhythm Flow", "Voice Echo",
    "Crystal Ball", "Star Gaze", "Cell View", "Hammer Time", "Wrench Turn",
    "Bolt Twist", "Gear Spin", "Chain Link", "Link Loop", "Magnet Pull",
    "Flask Mix", "DNA Helix", "Petri Grow", "Fire Fight", "Tool Box",
    "Brick Stack", "Field Force", "Case Pack", "Lotion Rub", "Thread Weave",
    "Yarn Knit", "Pin Poke", "Bear Hug", "Broom Sweep", "Basket Catch",
    "Paper Roll", "Soap Wash", "Sponge Squeeze", "Receipt Print", "Eye Ward",
    "Spiral Spin", "Fog Walk", "Rain Dance", "Night Fall", "Dawn Rise",
    "Sun Set", "City Lights", "Bridge Cross", "Rainbow Arc", "River Flow",
    "Wave Crash", "Volcano Erupt", "Galaxy Swirl", "Earth Spin", "Globe Turn",
    "World Map", "Net Surf", "Moon Phase", "Crescent Glow", "Half Moon", "Full Moon"
];

const PRIMES: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

fn hecke(shard: u8, prime: u32) -> u32 {
    let base = prime * shard as u32 + prime * prime;
    let dist = (196883 - shard as u32 * 2770) / 1000;
    let angle = (180 - (shard as u32 * 5) % 360) / 100;
    base + dist + angle
}

fn total_hecke(shard: u8) -> u32 {
    PRIMES.iter().map(|&p| hecke(shard, p)).sum()
}

fn complexity(shard: u8) -> u32 {
    let func = if shard < 70 { (shard / 10) + 1 } else { 7 };
    let perf = if shard < 24 { 1 } else if shard < 48 { 2 } else { 3 };
    let mem = [1, 5, 3, 4, 2][shard as usize % 5];
    shard as u32 + func as u32 * 10 + perf * 5 + mem * 3
}

fn components(shard: u8) -> String {
    let perf = if shard < 24 { "🚀" } else if shard < 48 { "⚡" } else { "🐌" };
    let mem = ["💾", "🔀", "📊", "🔄", "💿"][shard as usize % 5];
    let reg = ["🅰️", "🅱️", "©️", "🇩", "🇪", "🇫", "🇬", "🇭"][shard as usize % 8];
    let func = ["➕","✖️","➗","🔀","🔁","🔂","🔃"][(shard / 10).min(6) as usize];
    format!("{}{}{}{}{}", EMOJIS[shard as usize], perf, mem, reg, func)
}

struct Cell {
    shards: Vec<u8>,
    display: String,
    name: String,
}

fn merge_games() -> Vec<Cell> {
    let mut ordered: Vec<u8> = (0..71).collect();
    ordered.sort_by_key(|&s| (total_hecke(s), s % 10, complexity(s)));
    
    let mut cells = Vec::new();
    let mut used = vec![false; 71];
    
    for &s1 in &ordered {
        if used[s1 as usize] { continue; }
        
        let c1 = components(s1);
        let partner = ordered.iter().find(|&&s2| {
            !used[s2 as usize] && s2 != s1 && {
                let c2 = components(s2);
                c1.chars().skip(2).zip(c2.chars().skip(2)).filter(|(a,b)| a==b).count() >= 3
            }
        });
        
        if let Some(&s2) = partner {
            let c2 = components(s2);
            cells.push(Cell {
                shards: vec![s1, s2],
                display: format!("{}⊕{}", &c1[..4], &c2[..4]),
                name: format!("{}⊕{}", &NAMES[s1 as usize][..6], &NAMES[s2 as usize][..6]),
            });
            used[s1 as usize] = true;
            used[s2 as usize] = true;
        } else {
            cells.push(Cell {
                shards: vec![s1],
                display: c1,
                name: NAMES[s1 as usize].to_string(),
            });
            used[s1 as usize] = true;
        }
    }
    cells
}

fn draw_board(cells: &[Cell], cursor_pos: usize) -> std::io::Result<()> {
    let mut stdout = stdout();
    execute!(stdout, Clear(ClearType::All), cursor::MoveTo(0, 0))?;
    
    // Title
    let title = "🐯 MONSTER GROUP ARCADE 🐯";
    let subtitle = format!("{} games | Arrow keys to select | Enter to play | Q to quit", cells.len());
    queue!(stdout, cursor::MoveTo(((WIDTH - title.len()) / 2) as u16, 0), Print(title))?;
    queue!(stdout, cursor::MoveTo(((WIDTH - subtitle.len()) / 2) as u16, 1), Print(subtitle))?;
    queue!(stdout, cursor::MoveTo(0, 2), Print("=".repeat(WIDTH)))?;
    
    // Emoji grid
    for row in 0..3 {
        queue!(stdout, cursor::MoveTo(0, 4 + row as u16))?;
        for col in 0..12 {
            let idx = row * 12 + col;
            if idx < cells.len() {
                let cell = &cells[idx];
                let display = format!("{:<12}", &cell.display[..cell.display.len().min(11)]);
                
                if idx == cursor_pos {
                    queue!(stdout, SetForegroundColor(Color::Yellow), Print(&display), ResetColor)?;
                } else if cell.shards.contains(&17) {
                    queue!(stdout, SetForegroundColor(Color::Cyan), Print(&display), ResetColor)?;
                } else {
                    queue!(stdout, Print(&display))?;
                }
            }
        }
    }
    
    // Name grid
    for row in 0..3 {
        queue!(stdout, cursor::MoveTo(0, 8 + row as u16))?;
        for col in 0..12 {
            let idx = row * 12 + col;
            if idx < cells.len() {
                let cell = &cells[idx];
                let name = format!("{:<12}", &cell.name[..cell.name.len().min(11)]);
                
                if idx == cursor_pos {
                    queue!(stdout, SetForegroundColor(Color::Yellow), Print(&name), ResetColor)?;
                } else if cell.shards.contains(&17) {
                    queue!(stdout, SetForegroundColor(Color::Cyan), Print(&name), ResetColor)?;
                } else {
                    queue!(stdout, Print(&name))?;
                }
            }
        }
    }
    
    // Info
    queue!(stdout, cursor::MoveTo(0, 12), Print("=".repeat(WIDTH)))?;
    let info = "⊕=Merged | 🚀⚡🐌=Speed | Cyan=Cusp(S17) | Yellow=Selected";
    queue!(stdout, cursor::MoveTo(((WIDTH - info.len()) / 2) as u16, 13), Print(info))?;
    
    if cursor_pos < cells.len() {
        let cell = &cells[cursor_pos];
        let details = format!("Selected: {} | Shards: {:?} | Hecke: {}", 
            cell.name, cell.shards, total_hecke(cell.shards[0]));
        queue!(stdout, cursor::MoveTo(((WIDTH - details.len()) / 2) as u16, 14), Print(details))?;
    }
    
    stdout.flush()
}

fn main() -> std::io::Result<()> {
    let cells = merge_games();
    let mut cursor = 0;
    
    terminal::enable_raw_mode()?;
    let mut stdout = stdout();
    execute!(stdout, terminal::EnterAlternateScreen)?;
    
    draw_board(&cells, cursor)?;
    
    loop {
        if let Event::Key(key) = event::read()? {
            match key.code {
                KeyCode::Char('q') | KeyCode::Char('Q') | KeyCode::Esc => break,
                KeyCode::Left if cursor % 12 > 0 => cursor -= 1,
                KeyCode::Right if cursor % 12 < 11 && cursor < cells.len() - 1 => cursor += 1,
                KeyCode::Up if cursor >= 12 => cursor -= 12,
                KeyCode::Down if cursor + 12 < cells.len() => cursor += 12,
                KeyCode::Enter => {
                    execute!(stdout, Clear(ClearType::All), cursor::MoveTo(0, 0))?;
                    println!("🎮 Launching: {} 🎮", cells[cursor].name);
                    println!("\nShards: {:?}", cells[cursor].shards);
                    println!("Hecke: {}", total_hecke(cells[cursor].shards[0]));
                    println!("Complexity: {}", complexity(cells[cursor].shards[0]));
                    println!("\n[Press any key to return]");
                    stdout.flush()?;
                    event::read()?;
                }
                _ => {}
            }
            draw_board(&cells, cursor)?;
        }
    }
    
    execute!(stdout, terminal::LeaveAlternateScreen)?;
    terminal::disable_raw_mode()?;
    Ok(())
}
