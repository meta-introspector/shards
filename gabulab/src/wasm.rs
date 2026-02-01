//! WASM bindings for Gabulab

use wasm_bindgen::prelude::*;
use serde_wasm_bindgen::{from_value, to_value};
use crate::{MonsterHarmonic, Topology};

#[wasm_bindgen]
pub fn extract_harmonics_wasm(book_md: &str) -> Result<JsValue, JsValue> {
    let harmonics = MonsterHarmonic::extract(book_md)
        .map_err(|e| JsValue::from_str(&e))?;
    
    to_value(&harmonics)
        .map_err(|e| JsValue::from_str(&e.to_string()))
}

#[wasm_bindgen]
pub fn parse_topology_wasm(book_md: &str) -> Result<JsValue, JsValue> {
    let topology = Topology::from_promptbook(book_md)
        .map_err(|e| JsValue::from_str(&e))?;
    
    to_value(&topology)
        .map_err(|e| JsValue::from_str(&e.to_string()))
}

#[wasm_bindgen]
pub fn visualize_topology_wasm(harmonics_js: JsValue) -> Result<String, JsValue> {
    let harmonics: Vec<MonsterHarmonic> = from_value(harmonics_js)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;
    
    let mut viz = String::from("digraph Gabulab {\n");
    viz.push_str("  rankdir=LR;\n");
    viz.push_str("  node [shape=circle];\n\n");
    
    for h in &harmonics {
        viz.push_str(&format!(
            "  s{} [label=\"Shard {}\\nT_{}\\nj={}\"];\n",
            h.shard, h.shard, h.prime, h.j_invariant
        ));
    }
    
    viz.push_str("\n");
    
    for i in 0..harmonics.len().saturating_sub(1) {
        viz.push_str(&format!(
            "  s{} -> s{};\n",
            harmonics[i].shard,
            harmonics[i + 1].shard
        ));
    }
    
    viz.push_str("}\n");
    
    Ok(viz)
}

#[wasm_bindgen]
pub fn compute_j_invariant_wasm(shard: u8) -> i64 {
    MonsterHarmonic::compute_j_invariant(shard)
}

#[wasm_bindgen]
pub fn get_monster_primes_wasm() -> Vec<u64> {
    crate::MONSTER_PRIMES.to_vec()
}

#[wasm_bindgen(start)]
pub fn main_wasm() {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
}
