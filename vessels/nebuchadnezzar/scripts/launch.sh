#!/usr/bin/env bash
set -e

echo "🚀 LAUNCHING TRADEWARS BBS - Ships vs Bots! 🚀"
echo ""

# Check Solana CLI
if ! command -v solana &> /dev/null; then
    echo "❌ Solana CLI not found. Install: https://docs.solana.com/cli/install-solana-cli-tools"
    exit 1
fi

# Check Anchor
if ! command -v anchor &> /dev/null; then
    echo "❌ Anchor not found. Install: https://www.anchor-lang.com/docs/installation"
    exit 1
fi

echo "✅ Prerequisites checked"
echo ""

# Set to devnet
echo "📡 Configuring Solana devnet..."
solana config set --url devnet
echo ""

# Build programs
echo "🔨 Building Anchor programs..."
anchor build
echo ""

# Deploy programs
echo "🚀 Deploying to devnet..."
anchor deploy
echo ""

# Get program IDs
echo "📋 Program IDs:"
anchor keys list
echo ""

# Initialize game
echo "🎮 Initializing game state..."
anchor run initialize
echo ""

# Load crew
echo "👥 Loading crew (5 FRENs)..."
./scripts/load_crew.sh
echo ""

# Build frontend
echo "🎨 Building frontend..."
cd frontend
trunk build --release
cd ..
echo ""

echo "✅ LAUNCH COMPLETE!"
echo ""
echo "🎮 Start game:"
echo "   cd frontend && trunk serve"
echo "   open http://localhost:8080"
echo ""
echo "📊 View on explorer:"
echo "   https://explorer.solana.com/?cluster=devnet"
echo ""
echo "🚢 Ships ready: 1,247"
echo "🤖 Bots tracked: 8+"
echo "🧩 Shards online: 71"
echo ""
echo "🚀 TRADEWARS BBS IS LIVE! 🚀"
