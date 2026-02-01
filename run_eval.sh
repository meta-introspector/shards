#!/usr/bin/env bash
# Run agent evaluation for all frameworks

set -e

SHARD_ID=${1:-0}

echo "🎯 Evaluating all agents on shard $SHARD_ID"
echo "============================================"
echo ""

FRAMEWORKS=("claude" "openai" "ollama" "autogen" "langchain" "crewai")

for fw in "${FRAMEWORKS[@]}"; do
    echo "🤖 Testing $fw..."
    python3 agents/evaluate.py --framework "$fw" --shard "$SHARD_ID" || echo "   ⚠️  $fw failed"
    echo ""
done

echo "📊 Generating leaderboard..."
python3 agents/generate_leaderboard.py

echo ""
echo "✅ Evaluation complete!"
echo "📄 Results in: results/"
echo "📊 Leaderboard: LEADERBOARD.md"
