#!/usr/bin/env bash
set -euo pipefail

echo "➡️ Lean4 Code → Arrows Between Shards"
echo "======================================"
echo

# Find all Lean4 files
LEAN_FILES=$(find . -name "*.lean" -type f 2>/dev/null)

# Build shard map and import graph
declare -A shard_map
declare -A arrows

echo "Building import graph..."

while IFS= read -r file; do
    hash=$(sha256sum "$file" 2>/dev/null | cut -d' ' -f1 | head -c 16)
    shard=$((0x$hash % 71))
    shard_map["$file"]=$shard
    
    # Extract imports
    imports=$(grep "^import" "$file" 2>/dev/null | awk '{print $2}' || true)
    
    # For each import, create arrow
    while IFS= read -r import; do
        if [ -n "$import" ]; then
            # Find file that defines this import
            for target in $LEAN_FILES; do
                if grep -q "namespace $import" "$target" 2>/dev/null; then
                    target_hash=$(sha256sum "$target" 2>/dev/null | cut -d' ' -f1 | head -c 16)
                    target_shard=$((0x$target_hash % 71))
                    
                    # Create arrow: source_shard → target_shard
                    arrow_key="${shard}_${target_shard}"
                    arrows["$arrow_key"]=$((${arrows[$arrow_key]:-0} + 1))
                    break
                fi
            done
        fi
    done <<< "$imports"
done <<< "$LEAN_FILES"

# Display arrow statistics
echo "Arrow Statistics:"
echo "  Total arrows: ${#arrows[@]}"
echo

# Top 20 arrows
echo "Top 20 arrows (shard → shard):"
for arrow in $(for a in "${!arrows[@]}"; do echo "$a ${arrows[$a]}"; done | sort -k2 -rn | head -20); do
    from=$(echo "$arrow" | cut -d'_' -f1)
    to=$(echo "$arrow" | cut -d' ' -f1 | cut -d'_' -f2)
    count=$(echo "$arrow" | awk '{print $2}')
    printf "  Shard %2d → Shard %2d: %3d imports\n" "$from" "$to" "$count"
done

echo
echo "✨ Arrow graph complete!"
echo "Arrows show import dependencies between shards"
