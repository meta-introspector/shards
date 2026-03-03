#!/usr/bin/env bash
# Nix-Wars: Play the game!

set -e

echo "🎮 Nix-Wars: TradeWars as Pure Nix Derivations"
echo "=============================================="
echo ""

cd "$(dirname "$0")/states"

# Genesis
echo "📍 State 0: Genesis"
cd state-0
nix build --no-link
COMMIT_0=$(nix eval --raw .#lib.commitment)
echo "   Commitment: ${COMMIT_0:0:16}..."
echo "   Ships: alpha(0), beta(1), gamma(2)"
cd ..
echo ""

# Move 1
echo "🚀 State 1: Alpha warps to sector 42"
cd state-1
nix build --no-link
COMMIT_1=$(nix eval --raw .#lib.commitment)
echo "   Commitment: ${COMMIT_1:0:16}..."
echo "   Move: alpha → sector 42"
cd ..
echo ""

# Fork
echo "🔀 Fork: Two competing moves"
echo ""

echo "   State 2a: Beta warps to sector 59"
cd state-2a
nix build --no-link
COMMIT_2A=$(nix eval --raw .#lib.commitment)
echo "   Commitment: ${COMMIT_2A:0:16}..."
cd ..
echo ""

echo "   State 2b: Gamma warps to sector 71"
cd state-2b
nix build --no-link
COMMIT_2B=$(nix eval --raw .#lib.commitment)
echo "   Commitment: ${COMMIT_2B:0:16}..."
cd ..
echo ""

# Consensus
echo "🤝 State 3: Consensus Resolution"
cd state-3
nix build
COMMIT_3=$(nix eval --raw .#lib.commitment)
echo "   Commitment: ${COMMIT_3:0:16}..."
echo "   Winner: state-2a (2/3 votes)"
echo "   Chosen: ${COMMIT_2A:0:16}..."
echo "   Rejected: ${COMMIT_2B:0:16}..."
cd ..
echo ""

echo "✅ Game complete! View results:"
echo "   cat states/state-3/result/state.json"
echo "   cat states/state-3/result/consensus.json"
echo ""

echo "📊 Game Lattice:"
echo "   State 0 (genesis)"
echo "       ↓"
echo "   State 1 (alpha→42)"
echo "      / \\"
echo "    2a   2b"
echo "      \\ /"
echo "   State 3 (consensus: 2a)"
