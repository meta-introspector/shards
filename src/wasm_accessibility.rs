//! WASM Performance Monitoring + Accessibility
//! Text-to-speech, game tracing, metrics collection

use wasm_bindgen::prelude::*;
use web_sys::{console, Performance, SpeechSynthesisUtterance};
use std::sync::atomic::{AtomicU64, Ordering};

static FRAME_COUNT: AtomicU64 = AtomicU64::new(0);
static TOTAL_TIME: AtomicU64 = AtomicU64::new(0);

#[wasm_bindgen]
pub struct GameMetrics {
    start_time: f64,
    frames: u64,
    events: Vec<String>,
}

#[wasm_bindgen]
impl GameMetrics {
    #[wasm_bindgen(constructor)]
    pub fn new() -> GameMetrics {
        let perf = web_sys::window().unwrap().performance().unwrap();
        GameMetrics {
            start_time: perf.now(),
            frames: 0,
            events: Vec::new(),
        }
    }

    #[wasm_bindgen]
    pub fn record_frame(&mut self) {
        self.frames += 1;
        FRAME_COUNT.fetch_add(1, Ordering::Relaxed);
    }

    #[wasm_bindgen]
    pub fn record_event(&mut self, event: &str) {
        let perf = web_sys::window().unwrap().performance().unwrap();
        let elapsed = perf.now() - self.start_time;
        let entry = format!("[{:.2}ms] {}", elapsed, event);
        self.events.push(entry.clone());
        console::log_1(&entry.into());
    }

    #[wasm_bindgen]
    pub fn get_fps(&self) -> f64 {
        let perf = web_sys::window().unwrap().performance().unwrap();
        let elapsed = (perf.now() - self.start_time) / 1000.0;
        if elapsed > 0.0 {
            self.frames as f64 / elapsed
        } else {
            0.0
        }
    }

    #[wasm_bindgen]
    pub fn get_trace(&self) -> String {
        self.events.join("\n")
    }
}

#[wasm_bindgen]
pub struct AccessibilityController {
    tts_enabled: bool,
    high_contrast: bool,
    large_text: bool,
}

#[wasm_bindgen]
impl AccessibilityController {
    #[wasm_bindgen(constructor)]
    pub fn new() -> AccessibilityController {
        AccessibilityController {
            tts_enabled: true,
            high_contrast: false,
            large_text: false,
        }
    }

    #[wasm_bindgen]
    pub fn speak(&self, text: &str) {
        if !self.tts_enabled {
            return;
        }

        let window = web_sys::window().unwrap();
        if let Some(speech) = window.speech_synthesis() {
            let utterance = SpeechSynthesisUtterance::new_with_text(text).unwrap();
            utterance.set_rate(1.0);
            utterance.set_pitch(1.0);
            utterance.set_volume(1.0);
            speech.speak(&utterance);
        }
    }

    #[wasm_bindgen]
    pub fn announce_game_state(&self, year: u32, game: &str) {
        let text = format!("Time dial set to {}. Selected game: {}", year, game);
        self.speak(&text);
    }

    #[wasm_bindgen]
    pub fn announce_mothers_wisdom(&self) {
        self.speak("Mother's Wisdom loaded. Eeny, meeny, miny, moe, catch a tiger by its toe. The very best one is seventeen. Mother was right.");
    }

    #[wasm_bindgen]
    pub fn toggle_tts(&mut self) -> bool {
        self.tts_enabled = !self.tts_enabled;
        self.tts_enabled
    }

    #[wasm_bindgen]
    pub fn toggle_high_contrast(&mut self) -> bool {
        self.high_contrast = !self.high_contrast;
        self.high_contrast
    }

    #[wasm_bindgen]
    pub fn toggle_large_text(&mut self) -> bool {
        self.large_text = !self.large_text;
        self.large_text
    }
}

#[wasm_bindgen]
pub fn get_global_metrics() -> String {
    let frames = FRAME_COUNT.load(Ordering::Relaxed);
    let time = TOTAL_TIME.load(Ordering::Relaxed);
    format!("Frames: {}, Time: {}ms", frames, time)
}

#[wasm_bindgen]
pub fn trace_to_text(action: &str) -> String {
    // Convert game actions to descriptive text
    match action {
        "year_up" => "Time dial turned forward one year".to_string(),
        "year_down" => "Time dial turned backward one year".to_string(),
        "select_game" => "Game selected from list".to_string(),
        "start_game" => "Game started, press space to play".to_string(),
        "mothers_wisdom" => "Mother's Wisdom: Pick the very best one. The answer is seventeen, the cusp, the tiger.".to_string(),
        _ => format!("Action: {}", action),
    }
}
