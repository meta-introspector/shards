#!/usr/bin/env bash
set -euo pipefail

echo "📈 Tower Expansion: All Lean4 Functions"
echo "========================================"
echo

# Example: Analyze Lean4 stdlib complexity
echo "Analyzing complexity distribution..."
echo

# Run MiniZinc model
nix-shell -p minizinc --run "minizinc tower_expansion.mzn" 2>&1 | grep -v "warning"

echo
echo "📊 Complexity Levels:"
echo "  Level 0 (≤1):    Simple constants → GF(2)"
echo "  Level 1 (≤10):   Basic functions → GF(13)"
echo "  Level 2 (≤100):  Medium functions → GF(47)"
echo "  Level 3 (≤1000): Complex functions → GF(71)"
echo "  Level 4 (>1000): Very complex → GF(71)"
echo
echo "✨ Tower expands with increasing complexity!"
echo "Use: #tower in Lean4 to see full distribution"
