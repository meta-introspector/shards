//! WASM BBS Door Game: Time Dial MAME Room
//! Visit any time period and play era-appropriate games

use wasm_bindgen::prelude::*;
use web_sys::{console, HtmlCanvasElement};

#[wasm_bindgen]
pub struct TimeDial {
    current_year: u32,
    selected_game: String,
}

#[wasm_bindgen]
impl TimeDial {
    #[wasm_bindgen(constructor)]
    pub fn new() -> TimeDial {
        console::log_1(&"🕰️ Time Dial MAME Room initialized".into());
        TimeDial {
            current_year: 2026,
            selected_game: String::from("mothwis"),
        }
    }

    #[wasm_bindgen]
    pub fn set_year(&mut self, year: u32) {
        self.current_year = year;
        console::log_1(&format!("⏰ Time dial set to: {}", year).into());
    }

    #[wasm_bindgen]
    pub fn get_available_games(&self) -> String {
        let games = match self.current_year {
            1980..=1989 => vec![
                "Pac-Man (1980)",
                "Donkey Kong (1981)",
                "Galaga (1981)",
                "Ms. Pac-Man (1982)",
                "Dig Dug (1982)",
                "Pole Position (1982)",
                "Dragon's Lair (1983)",
                "Marble Madness (1984)",
                "Gauntlet (1985)",
                "Out Run (1986)",
            ],
            1990..=1999 => vec![
                "Street Fighter II (1991)",
                "Mortal Kombat (1992)",
                "NBA Jam (1993)",
                "Daytona USA (1994)",
                "Time Crisis (1995)",
                "House of the Dead (1996)",
                "Dance Dance Revolution (1998)",
                "Crazy Taxi (1999)",
            ],
            2000..=2009 => vec![
                "Initial D (2001)",
                "Virtua Fighter 4 (2001)",
                "Guitar Hero Arcade (2009)",
            ],
            2026.. => vec![
                "Mother's Wisdom (2026) 🏆",
                "Monster Market (2026)",
                "Hecke Resonance (2026)",
                "Triple Walk (2026)",
            ],
            _ => vec!["No games available for this era"],
        };
        
        serde_json::to_string(&games).unwrap()
    }

    #[wasm_bindgen]
    pub fn load_game(&mut self, game_name: &str) -> bool {
        self.selected_game = game_name.to_string();
        console::log_1(&format!("🎮 Loading: {}", game_name).into());
        
        // Special handling for Mother's Wisdom
        if game_name.contains("Mother's Wisdom") {
            console::log_1(&"👩 Mother's Wisdom loaded!".into());
            console::log_1(&"🐯 Catch a tiger by its toe...".into());
            return true;
        }
        
        true
    }

    #[wasm_bindgen]
    pub fn render(&self, canvas: HtmlCanvasElement) -> Result<(), JsValue> {
        let context = canvas
            .get_context("2d")?
            .unwrap()
            .dyn_into::<web_sys::CanvasRenderingContext2d>()?;

        // Clear canvas
        context.set_fill_style(&"#000".into());
        context.fill_rect(0.0, 0.0, 640.0, 480.0);

        // Draw time dial
        context.set_fill_style(&"#0f0".into());
        context.set_font("20px monospace");
        context.fill_text(&format!("⏰ TIME DIAL: {}", self.current_year), 10.0, 30.0)?;

        // Draw game title
        context.set_font("16px monospace");
        context.fill_text(&format!("🎮 {}", self.selected_game), 10.0, 60.0)?;

        // Draw instructions
        context.set_font("14px monospace");
        context.fill_text("Use arrow keys to change year", 10.0, 100.0)?;
        context.fill_text("Press ENTER to select game", 10.0, 120.0)?;
        context.fill_text("Press ESC to return to BBS", 10.0, 140.0)?;

        Ok(())
    }
}

#[wasm_bindgen(start)]
pub fn main() {
    console::log_1(&"🚪 BBS Door Game: Time Dial MAME Room".into());
    console::log_1(&"🕰️ Turn the dial to visit any era!".into());
}
