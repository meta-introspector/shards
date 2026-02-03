#!/usr/bin/env bash
set -euo pipefail

echo "📊 Load All Lean4 Code → Find Most Similar"
echo "==========================================="
echo

# Find all Lean4 files
echo "Scanning for Lean4 files..."
LEAN_FILES=$(find . -name "*.lean" -type f 2>/dev/null)
TOTAL=$(echo "$LEAN_FILES" | wc -l)

echo "Found: $TOTAL Lean4 files"
echo

# Build shard map
declare -A shard_map
declare -A shard_counts

echo "Building shard map..."
while IFS= read -r file; do
    hash=$(sha256sum "$file" 2>/dev/null | cut -d' ' -f1 | head -c 16)
    shard=$((0x$hash % 71))
    
    shard_map["$file"]=$shard
    shard_counts[$shard]=$((${shard_counts[$shard]:-0} + 1))
done <<< "$LEAN_FILES"

# Find top 10 most populated shards
echo "Top 10 most populated shards:"
for shard in $(for s in "${!shard_counts[@]}"; do echo "$s ${shard_counts[$s]}"; done | sort -k2 -rn | head -10 | awk '{print $1}'); do
    count=${shard_counts[$shard]}
    echo "  Shard $shard: $count files"
    
    # Show sample files
    echo "$LEAN_FILES" | while IFS= read -r file; do
        if [ "${shard_map[$file]}" = "$shard" ]; then
            lines=$(wc -l < "$file" 2>/dev/null || echo 0)
            basename=$(basename "$file")
            echo "    - $basename ($lines lines)"
        fi
    done | head -5
    echo
done

# Find most similar pairs
echo "Finding most similar pairs (same shard)..."
echo

for shard in "${!shard_counts[@]}"; do
    if [ ${shard_counts[$shard]} -ge 2 ]; then
        files_in_shard=()
        while IFS= read -r file; do
            if [ "${shard_map[$file]}" = "$shard" ]; then
                files_in_shard+=("$file")
            fi
        done <<< "$LEAN_FILES"
        
        if [ ${#files_in_shard[@]} -ge 2 ]; then
            echo "Shard $shard (${#files_in_shard[@]} files):"
            for i in "${!files_in_shard[@]}"; do
                echo "  ${files_in_shard[$i]}"
            done | head -3
            echo
        fi
    fi
done | head -30

echo "✨ Analysis complete!"
echo "Total shards used: ${#shard_counts[@]}/71"
