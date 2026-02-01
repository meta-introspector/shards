#!/usr/bin/env bash
# Convert all JS/Python to Rust

set -e

echo "🦀 Converting JS/Python to Rust..."
echo ""

# 1. BBS Server (worker.js → Rust plugin)
echo "📦 Building BBS server plugin..."
cd zos-server/plugins/bbs-server
cargo build --release --lib
cd ../../..

# 2. Agent Evaluator (Python → Rust)
echo "📦 Building agent evaluator..."
cd agents/evaluate
cargo build --release
cd ../..

# 3. Leaderboard (Python → Rust)
echo "📦 Building leaderboard..."
cd agents/leaderboard
cargo build --release
cd ../..

# 4. Shard Generator (Python → Rust)
echo "📦 Building shard generator..."
cd shard0/recon
cargo build --release --bin generate-shards
cd ../..

echo ""
echo "✅ All JS/Python converted to Rust!"
echo ""
echo "📊 Summary:"
echo "   worker.js → zos-server/plugins/bbs-server/target/release/libbbs_server.so"
echo "   evaluate.py → agents/evaluate/target/release/evaluate"
echo "   generate_leaderboard.py → agents/leaderboard/target/release/leaderboard"
echo "   generate_71_shards.py → shard0/recon/target/release/generate-shards"
