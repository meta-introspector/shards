#!/bin/bash
# Move data files into 71 shard directories

echo "🔄 Creating 71 Monster shard directories..."

# Create shard directories
for i in {0..70}; do
    mkdir -p "data/shards/shard_$(printf "%02d" $i)"
done

echo "📊 Distributing data files by hash..."

# Function to hash string to shard (0-70)
hash_to_shard() {
    local str="$1"
    local sum=0
    for ((i=0; i<${#str}; i++)); do
        char="${str:$i:1}"
        sum=$((sum + $(printf '%d' "'$char")))
    done
    echo $((sum % 71))
}

# Distribute JSON files
cd data/
for file in *.json; do
    if [ -f "$file" ]; then
        shard=$(hash_to_shard "$file")
        shard_dir="shards/shard_$(printf "%02d" $shard)"
        ln -sf "../../$file" "$shard_dir/$file"
        echo "  $file → shard $shard"
    fi
done

# Distribute TXT files
for file in *.txt; do
    if [ -f "$file" ]; then
        shard=$(hash_to_shard "$file")
        shard_dir="shards/shard_$(printf "%02d" $shard)"
        ln -sf "../../$file" "$shard_dir/$file"
        echo "  $file → shard $shard"
    fi
done

cd ..

echo ""
echo "✅ Data distributed into 71 shards"
echo ""
echo "Structure:"
echo "  data/shards/shard_00/ - Shard 0 (Complex A)"
echo "  data/shards/shard_06/ - Shard 6 (Terpsichore)"
echo "  data/shards/shard_17/ - Shard 17 (Cusp)"
echo "  ..."
echo "  data/shards/shard_70/ - Shard 70"
