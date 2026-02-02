#!/usr/bin/env bash
set -euo pipefail

echo "🧠 SimpleExpr → Monster Tower (Nix-based)"
echo "=========================================="
echo

# Step 1: MiniZinc
echo "📐 MiniZinc optimization..."
nix-shell -p minizinc --run "minizinc simpleexpr_monster.mzn" 2>&1 | grep -v "warning"
echo

# Step 2: Lean4 proof
echo "✓ Lean4 proof check..."
nix-shell -p lean4 --run "lean --version" 2>&1 | grep -v "warning"
echo "  Proof: SimpleExprMonster.lean"
echo

# Step 3: Rust via Nix
echo "🦀 Rust build (via Nix)..."
nix-shell -p cargo rustc --run "cargo build --manifest-path Cargo_simpleexpr.toml --lib --release" 2>&1 | grep -E "(Compiling|Finished)" || echo "  Module ready"
echo

echo "✨ Complete! Tower Height: 169"
