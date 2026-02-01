#!/usr/bin/env bash
# Check consensus network status

BASE_PORT=7100
NUM_NODES=23

echo "🔷 Paxos Consensus Network Status"
echo "═══════════════════════════════════"
echo ""

ALIVE=0
PROMISED=0
ACCEPTED=0

for NODE_ID in $(seq 0 22); do
    PORT=$((BASE_PORT + NODE_ID))
    
    STATUS=$(curl -s "http://localhost:$PORT/paxos/status" 2>/dev/null)
    
    if [ $? -eq 0 ]; then
        ((ALIVE++))
        
        PROMISED_NUM=$(echo "$STATUS" | jq -r '.promised_proposal' 2>/dev/null || echo "0")
        ACCEPTED_NUM=$(echo "$STATUS" | jq -r '.accepted_proposal' 2>/dev/null || echo "0")
        HAS_VALUE=$(echo "$STATUS" | jq -r '.has_value' 2>/dev/null || echo "false")
        
        if [ "$PROMISED_NUM" != "0" ]; then
            ((PROMISED++))
        fi
        
        if [ "$ACCEPTED_NUM" != "0" ]; then
            ((ACCEPTED++))
        fi
        
        echo "Node $NODE_ID: ✅ ALIVE | Promised: $PROMISED_NUM | Accepted: $ACCEPTED_NUM | Value: $HAS_VALUE"
    else
        echo "Node $NODE_ID: ❌ DOWN"
    fi
done

echo ""
echo "═══════════════════════════════════"
echo "Alive: $ALIVE / $NUM_NODES"
echo "Promised: $PROMISED"
echo "Accepted: $ACCEPTED"
echo ""

if [ $ALIVE -ge 12 ]; then
    echo "✅ Quorum achieved ($ALIVE >= 12)"
else
    echo "❌ No quorum ($ALIVE < 12)"
fi

if [ $ACCEPTED -ge 12 ]; then
    echo "✅ Consensus achieved ($ACCEPTED >= 12)"
else
    echo "⏳ No consensus yet ($ACCEPTED < 12)"
fi
