#!/usr/bin/env bash
# Generate zkML witnesses for all 71 shards

set -e

echo "🔷 Generating zkML witnesses for 71 shards"
echo "═══════════════════════════════════════════"
echo ""

for SHARD_ID in $(seq 0 70); do
    SHARD_DIR="$HOME/.openclaw/shard-$SHARD_ID"
    mkdir -p "$SHARD_DIR"
    
    # Create synthetic zkML witness
    cat > "$SHARD_DIR/zkwitness-$SHARD_ID.json" << EOF
{
  "shard_id": $SHARD_ID,
  "agent": "CICADA-Harbot-$SHARD_ID",
  "timestamp": $(date +%s),
  "task": "Register on Moltbook",
  "perf_hash": "$(echo -n "shard-$SHARD_ID-perf" | sha256sum | cut -d' ' -f1)",
  "ollama_hash": "$(echo -n "shard-$SHARD_ID-ollama" | sha256sum | cut -d' ' -f1)"
}
EOF
    
    # Create synthetic perf data
    echo "shard-$SHARD_ID-perf-data" > "$SHARD_DIR/zkperf-$SHARD_ID.data"
    
    # Create synthetic ollama log
    echo "shard-$SHARD_ID-ollama-response" > "$SHARD_DIR/ollama-$SHARD_ID.log"
    
    echo "✅ Shard $SHARD_ID witness created"
done

echo ""
echo "✅ All 71 shard witnesses generated"
echo "   Location: ~/.openclaw/shard-*/"
