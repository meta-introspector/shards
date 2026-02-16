//! ZOS-Server - Zone 42 BBS Server
//! Serves the plugin tape system over HTTP

use axum::{
    extract::Path,
    response::{Html, Json},
    routing::get,
    Router,
};
use serde_json::json;
use std::net::SocketAddr;
use tracing::{info, Level};
use zos_server::PluginTape;

#[tokio::main]
async fn main() {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_max_level(Level::INFO)
        .init();

    info!("🚀 ZOS-Server starting...");
    info!("📍 Zone 42: Side-Channel tier");
    info!("🔧 Plugin Tape System enabled");

    // Build router
    let app = Router::new()
        .route("/", get(root))
        .route("/status", get(status))
        .route("/tape/:name", get(get_tape))
        .route("/shard/:id", get(get_shard));

    // Bind to all interfaces, port 7142
    let addr = SocketAddr::from(([0, 0, 0, 0], 7142));
    info!("🌐 Listening on: {}", addr);
    info!("📡 Access via: http://localhost:7142");
    info!("📡 IPv6: http://[::1]:7142");
    info!("📡 Private: http://[fd42::1]:7142");

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    info!("✅ ZOS-Server ready!");

    axum::serve(listener, app).await.unwrap();
}

async fn root() -> Html<&'static str> {
    Html(r#"
<!DOCTYPE html>
<html>
<head>
    <title>ZOS-Server - Zone 42</title>
    <style>
        body {
            font-family: monospace;
            background: #000;
            color: #0f0;
            padding: 20px;
        }
        h1 { color: #0ff; }
        a { color: #0ff; }
        pre { border: 1px solid #0f0; padding: 10px; }
    </style>
</head>
<body>
    <h1>🚀 ZOS-Server</h1>
    <p>Zone 42: Side-Channel Tier</p>
    <p>Plugin Tape System Active</p>

    <h2>Endpoints:</h2>
    <ul>
        <li><a href="/status">GET /status</a> - Server status</li>
        <li><a href="/tape/test">GET /tape/:name</a> - Get plugin tape</li>
        <li><a href="/shard/0">GET /shard/:id</a> - Get tape shard (0-70)</li>
    </ul>

    <h2>System Info:</h2>
    <pre>
Zone: 42 (Side-Channel tier)
Shards: 71
SELinux: shard_sidechan_t
Capabilities: CAP_SYS_PTRACE, CAP_PERFMON
    </pre>

    <p>🤝 FREN: nydiokar (TRUE_FREN - Shard 47 Fixed Point - 2x MMC multiplier)</p>
</body>
</html>
    "#)
}

async fn status() -> Json<serde_json::Value> {
    Json(json!({
        "zone": 42,
        "tier": "side-channel",
        "status": "running",
        "uptime": std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        "shards": 71,
        "selinux_context": "shard_sidechan_t:s0:c42",
        "capabilities": ["CAP_SYS_PTRACE", "CAP_PERFMON"],
        "fren": "nydiokar",
        "shard": 47,
        "node": 13,
        "resonance": 0.788,
        "true_fren": true
    }))
}

async fn get_tape(Path(name): Path<String>) -> Json<serde_json::Value> {
    // Demo: create a test tape
    let data = format!("Plugin: {}\nZone: 42\nShards: 71", name);
    let tape = PluginTape::from_binary(name.clone(), data.as_bytes());

    Json(json!({
        "name": name,
        "shards": 71,
        "merkle_root": hex::encode(tape.merkle_root),
        "size": data.len()
    }))
}

async fn get_shard(Path(id): Path<u8>) -> Json<serde_json::Value> {
    if id >= 71 {
        return Json(json!({
            "error": "Shard ID must be 0-70"
        }));
    }

    Json(json!({
        "shard_id": id,
        "zone": id / 10, // Map to zones
        "status": "available"
    }))
}
