// BBS Server Plugin - Pure Rust (replaces worker.js)
// zos-server/plugins/bbs-server/src/lib.rs

use std::ffi::{CStr, CString, c_char};
use std::ptr;
use serde::{Deserialize, Serialize};

#[repr(C)]
pub struct PluginInfo {
    name: *const c_char,
    version: *const c_char,
}

#[no_mangle]
pub extern "C" fn plugin_init() -> *const PluginInfo {
    Box::into_raw(Box::new(PluginInfo {
        name: CString::new("bbs-server").unwrap().into_raw(),
        version: CString::new("0.1.0").unwrap().into_raw(),
    }))
}

#[no_mangle]
pub extern "C" fn plugin_handle(path: *const c_char) -> *const c_char {
    let path = unsafe { CStr::from_ptr(path).to_str().unwrap_or("") };
    
    let response = if path.starts_with("/dial/") {
        handle_dial(&path[6..])
    } else if path == "/bbs" {
        handle_bbs()
    } else if path == "/shards" {
        handle_shards()
    } else {
        ansi_welcome()
    };
    
    CString::new(response).unwrap().into_raw()
}

fn handle_dial(number: &str) -> String {
    let coeffs: Vec<u64> = number.split('-')
        .filter_map(|s| s.parse().ok())
        .collect();
    
    if coeffs.len() >= 2 && coeffs[0] == 744 && coeffs[1] == 196884 {
        let shard_id = coeffs.get(2).unwrap_or(&0) % 71;
        let state = decode_godel_url(&coeffs);
        wasm_loader(state, shard_id)
    } else {
        "Invalid j-invariant sequence".to_string()
    }
}

fn decode_godel_url(coeffs: &[u64]) -> Vec<u8> {
    coeffs.iter().take(71).map(|&n| (n % 256) as u8).collect()
}

fn wasm_loader(state: Vec<u8>, shard_id: u64) -> String {
    format!(r#"<!DOCTYPE html>
<html>
<head>
  <title>CICADA-71 BBS - Shard {}</title>
  <style>
    body {{ background: #000; color: #0f0; font-family: monospace; margin: 0; padding: 20px; }}
    #terminal {{ white-space: pre; font-size: 14px; }}
  </style>
</head>
<body>
  <div id="terminal">Loading BBS from j-invariant...</div>
  <script>
    const state = new Uint8Array([{}]);
    const shardId = {};
    
    setTimeout(() => {{
      document.getElementById('terminal').textContent = `
╔═══════════════════════════════════════════════════════════════╗
║                    CICADA-71 BBS v0.1                         ║
║                  Loaded via j-invariant URL                   ║
║                    Shard {} Active                              ║
╠═══════════════════════════════════════════════════════════════╣
║  Dialed: 744-196884-...                                      ║
║  State: {} bytes decoded                                      ║
║  [M] Message Boards (71 Forums)                              ║
║  [S] Shard Status                                            ║
║  [Q] Quit                                                    ║
╚═══════════════════════════════════════════════════════════════╝
Command: `;
    }}, 1000);
  </script>
</body>
</html>"#, shard_id, state.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(","), shard_id, shard_id, state.len())
}

fn handle_bbs() -> String {
    ansi_welcome()
}

fn handle_shards() -> String {
    let mut shards = Vec::new();
    for i in 0..71 {
        shards.push(format!(r#"{{"id":{},"online":true,"size":1024}}"#, i));
    }
    format!(r#"{{"total":71,"online":71,"quorum":12,"shards":[{}]}}"#, shards.join(","))
}

fn ansi_welcome() -> String {
    r#"╔═══════════════════════════════════════════════════════════════╗
║                    CICADA-71 BBS v0.1                         ║
║                  Running on Linux 0.01 (1991)                 ║
║                    Compiled to WASM (2025)                    ║
╠═══════════════════════════════════════════════════════════════╣
║  [M] Message Boards (71 Forums)                              ║
║  [F] File Areas                                              ║
║  [C] Chat Rooms                                              ║
║  [S] Shard Status                                            ║
║  [Q] Quit                                                    ║
║  Current Shard: 0                                            ║
║  Users Online: 23                                            ║
║  Messages: 196,883                                           ║
╚═══════════════════════════════════════════════════════════════╝
Command: "#.to_string()
}

#[no_mangle]
pub extern "C" fn plugin_cleanup() {
    // Cleanup resources
}
