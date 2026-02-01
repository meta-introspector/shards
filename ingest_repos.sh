#!/bin/bash
# ingest_repos.sh - Ingest Git repositories into 71 shards

set -e

echo "🔮 CICADA-71 Repository Ingestion"
echo "=================================="
echo ""

# Priority repos for self-hosting
REPOS=(
  # Core dependencies
  "https://github.com/leanprover-community/mathlib4:mathlib4"
  "https://github.com/NixOS/nixpkgs:nixpkgs"
  
  # AI Frameworks (Top 10)
  "https://github.com/langchain-ai/langchain:langchain"
  "https://github.com/Significant-Gravitas/AutoGPT:autogpt"
  "https://github.com/run-llama/llama_index:llamaindex"
  "https://github.com/microsoft/autogen:autogen"
  "https://github.com/joaomdmoura/crewAI:crewai"
  "https://github.com/microsoft/semantic-kernel:semantic-kernel"
  "https://github.com/deepset-ai/haystack:haystack"
  "https://github.com/langchain-ai/langgraph:langgraph"
  "https://github.com/elizaOS/eliza:elizaos"
  "https://github.com/steipete/moltbot:moltbot"
  
  # Tools
  "https://github.com/pipelight/pipelight:pipelight"
)

mkdir -p repos shards

for ENTRY in "${REPOS[@]}"; do
  IFS=':' read -r URL NAME <<< "$ENTRY"
  
  echo "📥 Ingesting $NAME..."
  
  # Calculate shard assignment
  HASH=$(echo -n "$NAME" | md5sum | cut -d' ' -f1)
  SHARD=$(python3 -c "print(int('$HASH', 16) % 71)")
  
  echo "   URL: $URL"
  echo "   Shard: $SHARD"
  
  # Clone if not exists
  if [ ! -d "repos/$NAME" ]; then
    git clone --depth=1 "$URL" "repos/$NAME" 2>&1 | grep -v "Cloning" || true
    echo "   ✅ Cloned"
  else
    echo "   ✅ Already exists"
  fi
  
  # Assign to shard
  SHARD_DIR="shards/shard_$(printf '%02d' $SHARD)"
  mkdir -p "$SHARD_DIR"
  
  if [ ! -L "$SHARD_DIR/$NAME" ]; then
    ln -s "../../repos/$NAME" "$SHARD_DIR/$NAME"
    echo "   ✅ Linked to shard $SHARD"
  fi
  
  # Update manifest
  echo "$NAME,$SHARD,$URL" >> repo_manifest.csv
  
  echo ""
done

echo "📊 Ingestion Summary:"
echo "===================="
echo "Total repos: ${#REPOS[@]}"
echo "Shards used: $(ls -d shards/shard_* 2>/dev/null | wc -l)"
echo ""

echo "📈 Shard Distribution:"
for i in {0..70}; do
  SHARD_DIR="shards/shard_$(printf '%02d' $i)"
  if [ -d "$SHARD_DIR" ]; then
    COUNT=$(ls -1 "$SHARD_DIR" 2>/dev/null | wc -l)
    if [ $COUNT -gt 0 ]; then
      echo "  Shard $i: $COUNT repos"
    fi
  fi
done

echo ""
echo "✅ Repository ingestion complete!"
echo ""
echo "Next steps:"
echo "  1. Review: cat repo_manifest.csv"
echo "  2. Build: cd shards/shard_00 && nix build"
echo "  3. Deploy: docker-compose up -d"
