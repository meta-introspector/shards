// WASM BBS Paxos Market - State in URL
// Extends existing shard0/bbs with Paxos consensus

use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};
use web_sys::window;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaxosMarketState {
    node_id: u8,
    proposal: u64,
    quotes: Vec<MarketQuote>,
    signature: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct MarketQuote {
    framework: String,
    score: u64,
    bid: f64,
    ask: f64,
}

#[wasm_bindgen]
pub struct PaxosMarket {
    state: PaxosMarketState,
}

#[wasm_bindgen]
impl PaxosMarket {
    #[wasm_bindgen(constructor)]
    pub fn new(node_id: u8) -> Self {
        Self {
            state: PaxosMarketState {
                node_id,
                proposal: 0,
                quotes: vec![],
                signature: String::new(),
            }
        }
    }
    
    pub fn encode_to_url(&self) -> String {
        let json = serde_json::to_string(&self.state).unwrap();
        base64::encode(json)
    }
    
    pub fn decode_from_url(encoded: &str) -> Result<Self, JsValue> {
        let json = base64::decode(encoded)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        let state = serde_json::from_slice(&json)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        Ok(Self { state })
    }
    
    pub fn propose(&mut self, quotes_json: &str) -> String {
        let quotes: Vec<MarketQuote> = serde_json::from_str(quotes_json).unwrap();
        self.state.proposal += 1;
        self.state.quotes = quotes;
        self.update_url();
        self.encode_to_url()
    }
    
    fn update_url(&self) {
        if let Some(window) = window() {
            if let Ok(location) = window.location() {
                let encoded = self.encode_to_url();
                location.set_hash(&format!("#{}", encoded)).ok();
            }
        }
    }
}

#[wasm_bindgen(start)]
pub fn main() {
    console_error_panic_hook::set_once();
}
