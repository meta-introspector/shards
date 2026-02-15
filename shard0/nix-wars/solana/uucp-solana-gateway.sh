#!/usr/bin/env bash
# UUCP <-> Solana Gateway: Bidirectional transaction bridge

set -e

GATEWAY_DIR="/var/spool/uucp/tradewars/gateway"
POLL_INTERVAL="${POLL_INTERVAL:-60}"

mkdir -p "${GATEWAY_DIR}"/{incoming,outgoing,processed,failed}

echo "🌉 UUCP <-> Solana Gateway Starting"
echo "   Poll interval: ${POLL_INTERVAL}s"
echo ""

# Process incoming UUCP -> Solana
process_incoming() {
    for TXN in "${GATEWAY_DIR}"/incoming/*.txn; do
        [ -f "$TXN" ] || continue
        
        echo "📥 UUCP -> Solana: $(basename $TXN)"
        
        COMMITMENT=$(jq -r .commitment "$TXN")
        CYCLES=$(jq -r .zkperf_cycles "$TXN")
        FROM=$(jq -r .from_sector "$TXN")
        TO=$(jq -r .to_sector "$TXN")
        PLAYER=$(jq -r .player "$TXN")
        
        # Submit to Solana
        if anchor run submit-move \
            --commitment "$COMMITMENT" \
            --cycles "$CYCLES" \
            --from "$FROM" \
            --to "$TO" 2>&1 | tee /tmp/solana-submit.log; then
            
            SIG=$(grep -oP 'Signature: \K[A-Za-z0-9]+' /tmp/solana-submit.log || echo "unknown")
            
            # Add signature to transaction
            jq --arg sig "$SIG" '.signature = $sig | .status = "confirmed"' "$TXN" > "${GATEWAY_DIR}/processed/$(basename $TXN)"
            rm "$TXN"
            
            echo "   ✅ Confirmed: ${SIG:0:16}..."
        else
            mv "$TXN" "${GATEWAY_DIR}/failed/"
            echo "   ❌ Failed"
        fi
        echo ""
    done
}

# Process outgoing Solana -> UUCP
process_outgoing() {
    # Query recent Solana transactions
    RECENT_TXS=$(solana transaction-history NixWars11111111111111111111111111111111111 --limit 10 2>/dev/null || echo "[]")
    
    echo "$RECENT_TXS" | jq -c '.[]' | while read -r TX; do
        SIG=$(echo "$TX" | jq -r .signature)
        
        # Check if already processed
        [ -f "${GATEWAY_DIR}/outgoing/${SIG}.txn" ] && continue
        
        echo "📤 Solana -> UUCP: ${SIG:0:16}..."
        
        # Create UUCP transaction file
        echo "$TX" > "${GATEWAY_DIR}/outgoing/${SIG}.txn"
        
        echo "   ✅ Exported"
    done
}

# Main loop
while true; do
    echo "🔄 Gateway cycle: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    
    process_incoming
    process_outgoing
    
    echo "💤 Sleeping ${POLL_INTERVAL}s..."
    echo ""
    sleep "$POLL_INTERVAL"
done
