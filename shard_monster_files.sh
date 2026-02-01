#!/usr/bin/env bash
set -e

echo "🔮 SHARDING MONSTER FILES ACROSS 71 SHARDS"
echo "=========================================="

# Get all files from monster submodule
cd monster
files=($(find . -type f -name "*.md" -o -name "*.py" -o -name "*.sh" -o -name "*.parquet" | head -71))
cd ..

echo "Found ${#files[@]} files to shard"

# Distribute files across 71 shards
for i in {0..70}; do
    shard_dir="shard${i}"
    mkdir -p "$shard_dir/monster"
    
    # Calculate which file goes to this shard
    file_idx=$((i % ${#files[@]}))
    file="${files[$file_idx]}"
    
    if [ -n "$file" ]; then
        # Create symlink to monster file
        ln -sf "../../monster/$file" "$shard_dir/monster/$(basename $file)" 2>/dev/null || true
        echo "Shard $i: $(basename $file)"
    fi
done

echo ""
echo "✅ Monster files sharded across 71 shards!"
