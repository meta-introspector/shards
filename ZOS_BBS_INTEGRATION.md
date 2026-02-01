# BBS Integration with ZOS-Server Plugin Architecture

## Overview

Merge the BBS implementations (Cloudflare Worker + WASM Paxos) into zos-server as plugins.

## Architecture

```
zos-server (Plugin Host)
    ├─ Plugin: BBS Server (shard0/bbs → zos plugin)
    ├─ Plugin: WASM Paxos Market (wasm-bbs → zos plugin)
    ├─ Plugin: Agent Evaluator (agents/evaluate)
    └─ Plugin: Leaderboard (agents/leaderboard)
```

## Integration Steps

### 1. Convert BBS to ZOS Plugin

```rust
// zos-server/plugins/bbs-server/src/lib.rs

use zos_server::plugin_api::*;

#[no_mangle]
pub extern "C" fn plugin_init() -> *const PluginInfo {
    Box::into_raw(Box::new(PluginInfo {
        name: "bbs-server",
        version: "0.1.0",
        description: "71-Shard BBS with j-invariant dialing",
    }))
}

#[no_mangle]
pub extern "C" fn plugin_handle_request(
    path: *const c_char,
    method: *const c_char,
) -> *const c_char {
    let path = unsafe { CStr::from_ptr(path).to_str().unwrap() };
    
    if path.starts_with("/dial/") {
        handle_dial(path)
    } else if path == "/bbs" {
        handle_bbs()
    } else {
        null()
    }
}

fn handle_dial(path: &str) -> *const c_char {
    let number = &path[6..];
    let coeffs: Vec<u64> = number.split('-')
        .filter_map(|s| s.parse().ok())
        .collect();
    
    if coeffs.len() >= 2 && coeffs[0] == 744 && coeffs[1] == 196884 {
        let shard_id = coeffs.get(2).unwrap_or(&0) % 71;
        let html = format!(r#"
<!DOCTYPE html>
<html>
<head><title>CICADA-71 BBS - Shard {}</title></head>
<body>
  <pre id="terminal">Loading BBS from j-invariant...</pre>
  <script src="/wasm/paxos-market.js"></script>
</body>
</html>
"#, shard_id);
        
        CString::new(html).unwrap().into_raw()
    } else {
        null()
    }
}
```

### 2. WASM Paxos as Plugin

```rust
// zos-server/plugins/paxos-market/src/lib.rs

#[no_mangle]
pub extern "C" fn plugin_init() -> *const PluginInfo {
    Box::into_raw(Box::new(PluginInfo {
        name: "paxos-market",
        version: "0.1.0",
        description: "Paxos consensus market leaderboard",
    }))
}

#[no_mangle]
pub extern "C" fn plugin_serve_wasm() -> *const u8 {
    // Serve compiled WASM binary
    include_bytes!("../../../wasm-bbs/pkg/wasm_bbs_bg.wasm").as_ptr()
}

#[no_mangle]
pub extern "C" fn plugin_handle_paxos(
    operation: *const c_char,
    data: *const c_char,
) -> *const c_char {
    let op = unsafe { CStr::from_ptr(operation).to_str().unwrap() };
    
    match op {
        "prepare" => handle_prepare(data),
        "accept" => handle_accept(data),
        "status" => handle_status(),
        _ => null(),
    }
}
```

### 3. Agent Evaluator Plugin

```rust
// zos-server/plugins/agent-eval/src/lib.rs

#[no_mangle]
pub extern "C" fn plugin_init() -> *const PluginInfo {
    Box::into_raw(Box::new(PluginInfo {
        name: "agent-eval",
        version: "0.1.0",
        description: "AI agent challenge evaluator",
    }))
}

#[no_mangle]
pub extern "C" fn plugin_evaluate(
    framework: *const c_char,
    shard_id: u16,
) -> *const c_char {
    // Run evaluation
    let result = evaluate_agent(framework, shard_id);
    CString::new(serde_json::to_string(&result).unwrap())
        .unwrap()
        .into_raw()
}
```

## Plugin Manifest

```toml
# zos-server/plugins/manifest.toml

[[plugin]]
name = "bbs-server"
path = "plugins/bbs-server/target/release/libbbs_server.so"
routes = ["/dial/*", "/bbs", "/shards"]
priority = 10

[[plugin]]
name = "paxos-market"
path = "plugins/paxos-market/target/release/libpaxos_market.so"
routes = ["/paxos/*", "/wasm/*"]
priority = 20

[[plugin]]
name = "agent-eval"
path = "plugins/agent-eval/target/release/libagent_eval.so"
routes = ["/eval/*", "/leaderboard"]
priority = 30
```

## ZOS Server Integration

```rust
// zos-server/src/main.rs

use plugin_manager::PluginManager;

#[tokio::main]
async fn main() {
    let mut pm = PluginManager::new();
    
    // Load BBS plugins
    pm.load_plugin(Path::new("plugins/bbs-server/target/release/libbbs_server.so"))?;
    pm.load_plugin(Path::new("plugins/paxos-market/target/release/libpaxos_market.so"))?;
    pm.load_plugin(Path::new("plugins/agent-eval/target/release/libagent_eval.so"))?;
    
    // Start server
    let app = Router::new()
        .route("/dial/:number", get(handle_dial))
        .route("/bbs", get(handle_bbs))
        .route("/paxos/:op", post(handle_paxos))
        .route("/eval/:framework/:shard", post(handle_eval))
        .layer(Extension(pm));
    
    axum::Server::bind(&"0.0.0.0:7100".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}

async fn handle_dial(
    Path(number): Path<String>,
    Extension(pm): Extension<PluginManager>,
) -> Html<String> {
    let plugin = pm.get_plugin("bbs-server").unwrap();
    let html = plugin.call("handle_dial", &number);
    Html(html)
}
```

## Directory Structure

```
zos-server/
├── src/
│   ├── main.rs
│   ├── plugin_manager.rs
│   └── plugin_api.rs
├── plugins/
│   ├── bbs-server/
│   │   ├── Cargo.toml
│   │   └── src/lib.rs
│   ├── paxos-market/
│   │   ├── Cargo.toml
│   │   └── src/lib.rs
│   └── agent-eval/
│       ├── Cargo.toml
│       └── src/lib.rs
├── www/
│   ├── wasm/
│   │   ├── paxos_market_bg.wasm
│   │   └── paxos_market.js
│   └── index.html
└── Cargo.toml
```

## Build Script

```bash
#!/usr/bin/env bash
# build_bbs_plugins.sh

set -e

echo "🔨 Building BBS plugins for ZOS-Server"

# Build BBS server plugin
cd zos-server/plugins/bbs-server
cargo build --release --lib
cd ../../..

# Build Paxos market plugin
cd zos-server/plugins/paxos-market
cargo build --release --lib
cd ../../..

# Build WASM
cd wasm-bbs
wasm-pack build --target web
cp pkg/* ../zos-server/www/wasm/
cd ..

# Build agent evaluator
cd zos-server/plugins/agent-eval
cargo build --release --lib
cd ../../..

# Build main server
cd zos-server
cargo build --release
cd ..

echo "✅ All plugins built!"
echo "🚀 Run: ./zos-server/target/release/zos-server"
```

## Benefits

1. **Unified Server**: Single binary hosts all services
2. **Hot Reload**: Plugins can be reloaded without restart
3. **Isolation**: Each plugin runs in separate context
4. **Composability**: Mix and match plugins
5. **Performance**: Native code, no network overhead

## Usage

```bash
# Build everything
./build_bbs_plugins.sh

# Run ZOS server with BBS plugins
./zos-server/target/release/zos-server

# Access BBS
curl http://localhost:7100/dial/744-196884-0

# Access Paxos market
curl http://localhost:7100/paxos/status

# Run agent evaluation
curl -X POST http://localhost:7100/eval/claude/0
```

## Next Steps

1. Implement plugin API in zos-server
2. Convert BBS worker.js to Rust plugin
3. Integrate WASM Paxos
4. Add agent evaluator
5. Deploy unified system
