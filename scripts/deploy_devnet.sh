#!/usr/bin/env bash
# scripts/deploy.sh - Deploy TradeWars BBS to Solana Devnet with Nix

set -e

echo "🚀 TradeWars BBS - Solana Devnet Deployment"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Enter Nix shell
nix develop --command bash << 'NIXEOF'

# 1. Setup Solana
echo "📡 Configuring Solana for devnet..."
solana config set --url https://api.devnet.solana.com

# 2. Check/create wallet
if [ ! -f ~/.config/solana/id.json ]; then
    echo "🔑 Creating new wallet..."
    solana-keygen new --no-bip39-passphrase
fi

WALLET=$(solana-keygen pubkey)
echo "Wallet: $WALLET"

# 3. Airdrop SOL
echo "💰 Requesting airdrop..."
solana airdrop 2 || echo "Airdrop may have failed, continuing..."
solana balance

# 4. Build Anchor program
echo "🔨 Building Anchor program..."
cd programs/tradewars-bbs

# Install Anchor if needed
if ! command -v anchor &> /dev/null; then
    echo "Installing Anchor CLI..."
    cargo install --git https://github.com/coral-xyz/anchor anchor-cli --locked
fi

anchor build

# 5. Deploy program
echo "🚀 Deploying program..."
anchor deploy

# 6. Get program ID
PROGRAM_ID=$(solana-keygen pubkey target/deploy/tradewars_bbs-keypair.json)
echo "✅ Program deployed!"
echo "Program ID: $PROGRAM_ID"

# 7. Update Anchor.toml
sed -i "s/tradewars_bbs = \".*\"/tradewars_bbs = \"$PROGRAM_ID\"/" Anchor.toml

# 8. Build frontend
echo "🎨 Building frontend..."
cd ../../frontend

# Build with Dioxus
dx build --release

# 9. Deploy to Vercel
echo "🌐 Deploying to Vercel..."
vercel deploy --prod --yes

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ DEPLOYMENT COMPLETE!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "📋 Deployment Info:"
echo "  Network: Solana Devnet"
echo "  Program ID: $PROGRAM_ID"
echo "  Wallet: $WALLET"
echo "  Frontend: https://tradewars-bbs.vercel.app"
echo ""
echo "🎮 Next Steps:"
echo "  1. Visit https://tradewars-bbs.vercel.app"
echo "  2. Connect your Solana wallet"
echo "  3. Start trading!"
echo ""

NIXEOF
