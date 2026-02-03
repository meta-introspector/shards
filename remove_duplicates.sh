#!/bin/bash
# Remove next batch of duplicates (rank 4-13)

echo "🗑️  Removing duplicates (rank 4-13)..."

# Rank 6: extract_71_objects.py
rm -f monster/shards/shard_57/extract_71_objects.py
rm -f shard32/monster/extract_71_objects.py

# Rank 7: prove_zk_rdfa.py
rm -f monster/shards/shard_66/prove_zk_rdfa.py
rm -f shard37/monster/prove_zk_rdfa.py

# Rank 8: convert_paper_to_visual.py
rm -f shard8/monster/convert_paper_to_visual.py
rm -f monster/shards/shard_11/convert_paper_to_visual.py

# Rank 9: translate-hilbert-lean4.py
rm -f shard7/monster/translate-hilbert-lean4.py
rm -f monster/shards/shard_02/translate-hilbert-lean4.py

# Rank 11: tool_wrapper.py
rm -f shard42/monster/tool_wrapper.py
rm -f monster/shards/shard_62/tool_wrapper.py

# Rank 12: iterative_improve.py
rm -f monster/shards/shard_35/iterative_improve.py
rm -f shard5/monster/iterative_improve.py

# Rank 13: prove_rust_simple.py
rm -f monster/shards/shard_68/prove_rust_simple.py
rm -f shard57/monster/prove_rust_simple.py

echo "✅ Removed 14 duplicate files"
echo "💾 Saved ~100 KB"
