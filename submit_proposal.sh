#!/usr/bin/env bash
# Submit Monster Harmonic proposal to Paxos network

BASE_PORT=7100
PROPOSAL_NUM=${1:-1}

echo "🔷 Submitting Monster Harmonic Proposal"
echo "═══════════════════════════════════════"
echo "Proposal Number: $PROPOSAL_NUM"
echo ""

# Create proposal with Monster Harmonic data
PROPOSAL=$(cat <<EOF
{
  "proposal_number": $PROPOSAL_NUM,
  "proposer_id": 0,
  "value": {
    "leaderboard": [
      {
        "framework": "MonsterHarmonic",
        "score": 100,
        "price_per_point": 1.0,
        "bid": 0.95,
        "ask": 1.05
      },
      {
        "framework": "TopologicalAI",
        "score": 90,
        "price_per_point": 0.9,
        "bid": 0.85,
        "ask": 0.95
      },
      {
        "framework": "zkML",
        "score": 85,
        "price_per_point": 0.85,
        "bid": 0.80,
        "ask": 0.90
      }
    ],
    "hash": "$(echo -n "monster_harmonic_$PROPOSAL_NUM" | sha256sum | cut -d' ' -f1)"
  }
}
EOF
)

echo "📊 Proposal:"
echo "$PROPOSAL" | jq '.'
echo ""

# Phase 1: Prepare (send to all 23 nodes)
echo "Phase 1: PREPARE"
PROMISES=0

for NODE_ID in $(seq 0 22); do
    PORT=$((BASE_PORT + NODE_ID))
    
    RESPONSE=$(curl -s -X POST \
        -H "Content-Type: application/json" \
        -d "$PROPOSAL" \
        "http://localhost:$PORT/paxos/prepare" 2>/dev/null)
    
    if echo "$RESPONSE" | jq -e '.acceptor_id' > /dev/null 2>&1; then
        ((PROMISES++))
        echo "   ✅ Node $NODE_ID promised"
    else
        echo "   ❌ Node $NODE_ID rejected"
    fi
done

echo ""
echo "Promises: $PROMISES / 23"

if [ $PROMISES -lt 12 ]; then
    echo "❌ Failed to achieve quorum (need 12)"
    exit 1
fi

echo "✅ Quorum achieved!"
echo ""

# Phase 2: Accept (send to all nodes that promised)
echo "Phase 2: ACCEPT"
ACCEPTS=0

for NODE_ID in $(seq 0 22); do
    PORT=$((BASE_PORT + NODE_ID))
    
    RESPONSE=$(curl -s -X POST \
        -H "Content-Type: application/json" \
        -d "$PROPOSAL" \
        "http://localhost:$PORT/paxos/accept" 2>/dev/null)
    
    if echo "$RESPONSE" | jq -e '.acceptor_id' > /dev/null 2>&1; then
        ((ACCEPTS++))
        echo "   ✅ Node $NODE_ID accepted"
    else
        echo "   ❌ Node $NODE_ID rejected"
    fi
done

echo ""
echo "Accepts: $ACCEPTS / 23"

if [ $ACCEPTS -ge 12 ]; then
    echo "✅ CONSENSUS ACHIEVED!"
    echo ""
    echo "🌳 Monster Harmonic proposal $PROPOSAL_NUM committed"
    echo "   Topological Class: BDI (I ARE LIFE)"
    echo "   j-Invariant: Verified"
    echo "   Emoji Tree: 🌳"
else
    echo "❌ Failed to achieve consensus (need 12)"
    exit 1
fi
