#!/usr/bin/env bash
# Submit sneakernet transactions from UUCP spool

set -e

PLAYER="${1:-alpha}"
SPOOL_IN="/var/spool/uucp/tradewars/${PLAYER}/in"

if [ ! -d "$SPOOL_IN" ]; then
    echo "❌ No spool directory: ${SPOOL_IN}"
    exit 1
fi

echo "📬 Checking for incoming transactions..."
echo ""

for TXN_FILE in "${SPOOL_IN}"/*.txn; do
    if [ ! -f "$TXN_FILE" ]; then
        echo "No transactions found"
        exit 0
    fi
    
    echo "📦 Processing: $(basename $TXN_FILE)"
    
    COMMITMENT=$(jq -r .commitment "$TXN_FILE")
    CYCLES=$(jq -r .zkperf_cycles "$TXN_FILE")
    FROM=$(jq -r .from_sector "$TXN_FILE")
    TO=$(jq -r .to_sector "$TXN_FILE")
    
    echo "   Commitment: ${COMMITMENT:0:16}..."
    echo "   Move: ${FROM} → ${TO}"
    echo "   Cycles: ${CYCLES}"
    
    # Submit to Solana
    echo "   Submitting to Solana..."
    anchor run submit-move \
        --commitment "$COMMITMENT" \
        --cycles "$CYCLES" \
        --from "$FROM" \
        --to "$TO" 2>&1 | grep -E "Signature|Error" || true
    
    # Archive processed transaction
    ARCHIVE_DIR="/var/spool/uucp/tradewars/${PLAYER}/archive"
    mkdir -p "$ARCHIVE_DIR"
    mv "$TXN_FILE" "$ARCHIVE_DIR/"
    
    echo "   ✅ Processed and archived"
    echo ""
done

echo "✅ All transactions processed"
