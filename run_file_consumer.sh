#!/usr/bin/env bash
set -euo pipefail

echo "📥 File Consumer: Reason About External Files"
echo "=============================================="
echo

# Test files to consume
FILES=(
    "SimpleExprMonster.lean"
    "MetaCoqMonsterProof.lean"
    "TowerExpansion.lean"
    "TestMeta.org"
)

echo "Consuming files into Monster tower..."
echo

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "📄 $file"
        
        # Count lines and tokens
        lines=$(wc -l < "$file")
        tokens=$(wc -w < "$file")
        
        # Compute shards
        line_shard=$((lines % 59))
        token_shard=$((tokens % 47))
        
        # Estimate tower height (lines * 2 + tokens)
        tower=$((lines * 2 + tokens))
        shard=$((tower % 71))
        
        echo "  Lines: $lines → Shard $line_shard (mod 59)"
        echo "  Tokens: $tokens → Shard $token_shard (mod 47)"
        echo "  Tower: $tower → Shard $shard (mod 71)"
        echo
    fi
done

echo "✨ All files consumed and mapped to Monster tower!"
echo "Use: #consume \"<file>\" in Lean4 for full analysis"
