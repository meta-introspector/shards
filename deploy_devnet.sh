#!/bin/bash
# Deploy TradeWars BBS to Solana Devnet

set -e

echo "🚀 Deploying TradeWars BBS to Solana Devnet..."

# Setup
solana config set --url https://api.devnet.solana.com
echo "✅ Configured for devnet"

# Check balance
BALANCE=$(solana balance 2>/dev/null || echo "0")
echo "Current balance: $BALANCE"

if [ "$BALANCE" = "0 SOL" ]; then
    echo "💰 Requesting airdrop..."
    solana airdrop 2 || echo "Airdrop failed, continuing..."
fi

echo ""
echo "📋 Next steps:"
echo "1. cd programs/tradewars-bbs"
echo "2. anchor build"
echo "3. anchor deploy"
echo "4. Update PROGRAM_ID in frontend"
echo "5. vercel deploy"
echo ""
echo "Program will be deployed to devnet!"
