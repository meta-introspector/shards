#!/usr/bin/env bash
# Solana Sneakernet: Create offline transaction for UUCP transport

set -e

COMMITMENT="$1"
CYCLES="$2"
FROM="$3"
TO="$4"
PLAYER="${5:-alpha}"

if [ -z "$COMMITMENT" ] || [ -z "$CYCLES" ] || [ -z "$FROM" ] || [ -z "$TO" ]; then
    echo "Usage: $0 <commitment> <cycles> <from_sector> <to_sector> [player]"
    exit 1
fi

SPOOL_DIR="/var/spool/uucp/tradewars/${PLAYER}/out"
mkdir -p "$SPOOL_DIR"

TIMESTAMP=$(date -u +%Y%m%d%H%M%S)
TXN_FILE="${SPOOL_DIR}/move-${TIMESTAMP}.txn"

# Create offline transaction
cat > "$TXN_FILE" << EOF
{
  "version": "0.1.0",
  "type": "nix-wars-move",
  "player": "${PLAYER}",
  "commitment": "${COMMITMENT}",
  "zkperf_cycles": ${CYCLES},
  "from_sector": ${FROM},
  "to_sector": ${TO},
  "timestamp": "${TIMESTAMP}",
  "signature": null,
  "status": "pending"
}
EOF

echo "📦 Created offline transaction: ${TXN_FILE}"
echo "🔒 Commitment: ${COMMITMENT:0:16}..."
echo "⚡ Cycles: ${CYCLES}"
echo "🚀 Move: ${FROM} → ${TO}"
echo ""
echo "Next steps:"
echo "1. Sign: solana sign-transaction ${TXN_FILE}"
echo "2. Transport via UUCP sneakernet"
echo "3. Submit: solana send-transaction ${TXN_FILE}"
