//! WASM Agent Bridge: 26-bit Monster Vector Protocol
//! Browser WASM ↔ AI Agent communication via hypercompressed vectors

use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

/// 26-bit Monster Vector (hypercompressed game state)
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct MonsterVector {
    compressed: u32,  // Only 26 bits used
}

#[wasm_bindgen]
impl MonsterVector {
    #[wasm_bindgen(constructor)]
    pub fn new(year: u8, prime: u8, shard: u8, action: u8) -> MonsterVector {
        let compressed = 
            (year as u32) * 1_000_000 +
            (prime as u32) * 10_000 +
            (shard as u32) * 100 +
            (action as u32);
        
        MonsterVector { compressed }
    }

    #[wasm_bindgen]
    pub fn from_compressed(value: u32) -> MonsterVector {
        MonsterVector { compressed: value & 0x03FFFFFF }  // Mask to 26 bits
    }

    #[wasm_bindgen]
    pub fn get_year(&self) -> u8 {
        ((self.compressed / 1_000_000) % 100) as u8
    }

    #[wasm_bindgen]
    pub fn get_prime(&self) -> u8 {
        ((self.compressed / 10_000) % 100) as u8
    }

    #[wasm_bindgen]
    pub fn get_shard(&self) -> u8 {
        ((self.compressed / 100) % 100) as u8
    }

    #[wasm_bindgen]
    pub fn get_action(&self) -> u8 {
        (self.compressed % 100) as u8
    }

    #[wasm_bindgen]
    pub fn to_compressed(&self) -> u32 {
        self.compressed
    }

    #[wasm_bindgen]
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }
}

/// Accessibility mode for agent
#[wasm_bindgen]
#[derive(Clone, Copy, Debug)]
pub enum AccessibilityMode {
    Visual = 0,
    Auditory = 1,
    Motor = 2,
    Cognitive = 3,
}

/// Agent Bridge: WASM ↔ Agent communication
#[wasm_bindgen]
pub struct AgentBridge {
    agent_id: u8,
    mode: AccessibilityMode,
    current_state: MonsterVector,
}

#[wasm_bindgen]
impl AgentBridge {
    #[wasm_bindgen(constructor)]
    pub fn new(agent_id: u8, mode: AccessibilityMode) -> AgentBridge {
        // Initial state: 2026, prime 17, shard 17, idle
        let initial = MonsterVector::new(46, 6, 17, 0);
        
        AgentBridge {
            agent_id,
            mode,
            current_state: initial,
        }
    }

    #[wasm_bindgen]
    pub fn send_state(&mut self, vector: MonsterVector) -> String {
        self.current_state = vector;
        
        // Adapt output based on accessibility mode
        match self.mode {
            AccessibilityMode::Visual => self.to_audio_description(),
            AccessibilityMode::Auditory => self.to_visual_description(),
            AccessibilityMode::Motor => self.to_voice_commands(),
            AccessibilityMode::Cognitive => self.to_simple_steps(),
        }
    }

    #[wasm_bindgen]
    pub fn receive_action(&mut self, action: u8) -> MonsterVector {
        // Update state with new action
        MonsterVector::new(
            self.current_state.get_year(),
            self.current_state.get_prime(),
            self.current_state.get_shard(),
            action,
        )
    }

    fn to_audio_description(&self) -> String {
        format!(
            "Year {}, Prime index {}, Shard {}, Action {}",
            1980 + self.current_state.get_year(),
            self.current_state.get_prime(),
            self.current_state.get_shard(),
            self.current_state.get_action()
        )
    }

    fn to_visual_description(&self) -> String {
        format!(
            "[Year: {}] [Prime: {}] [Shard: {}] [Action: {}]",
            1980 + self.current_state.get_year(),
            self.current_state.get_prime(),
            self.current_state.get_shard(),
            self.current_state.get_action()
        )
    }

    fn to_voice_commands(&self) -> String {
        format!(
            "Say 'year {}', 'prime {}', 'shard {}', 'action {}'",
            1980 + self.current_state.get_year(),
            self.current_state.get_prime(),
            self.current_state.get_shard(),
            self.current_state.get_action()
        )
    }

    fn to_simple_steps(&self) -> String {
        format!(
            "Step 1: Year is {}. Step 2: Prime is {}. Step 3: Shard is {}.",
            1980 + self.current_state.get_year(),
            self.current_state.get_prime(),
            self.current_state.get_shard()
        )
    }
}

/// MAME Platform Adapter
#[wasm_bindgen]
pub struct MamePlatform {
    platform: String,
    vector: MonsterVector,
}

#[wasm_bindgen]
impl MamePlatform {
    #[wasm_bindgen(constructor)]
    pub fn new(platform: String) -> MamePlatform {
        MamePlatform {
            platform,
            vector: MonsterVector::new(46, 6, 17, 0),
        }
    }

    #[wasm_bindgen]
    pub fn compile_for_platform(&self) -> String {
        format!(
            "Compiling Mother's Wisdom for {} using 26-bit Monster vectors",
            self.platform
        )
    }

    #[wasm_bindgen]
    pub fn get_platform_binary(&self) -> Vec<u8> {
        // Return compressed state as binary
        let compressed = self.vector.to_compressed();
        vec![
            (compressed >> 24) as u8,
            (compressed >> 16) as u8,
            (compressed >> 8) as u8,
            compressed as u8,
        ]
    }
}

#[wasm_bindgen(start)]
pub fn main() {
    console_error_panic_hook::set_once();
    web_sys::console::log_1(&"🌉 WASM Agent Bridge initialized".into());
    web_sys::console::log_1(&"📦 26-bit Monster Vector protocol ready".into());
}
