#!/usr/bin/env bash
set -e

echo "🚀 Launching Vessel: Nebuchadnezzar"

nix develop --command bash << 'NIXEOF'

# Build
cd programs/tradewars-bbs
anchor build

# Deploy
anchor deploy

# Get program ID
PROGRAM_ID=$(solana-keygen pubkey target/deploy/tradewars_bbs-keypair.json)
echo "✅ Vessel deployed: $PROGRAM_ID"

NIXEOF
