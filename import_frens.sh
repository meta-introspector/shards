#!/usr/bin/env bash
# import_frens.sh - Import and witness all FREN token data
# Scans solfunmeme archives and creates witnesses for each token

set -euo pipefail

SOLFUN_DIR="${1:-/mnt/data1/nix/time/2025/04/25/solfunmeme}"
WITNESS_DIR="witnesses/frens"

if [ ! -d "$SOLFUN_DIR" ]; then
    echo "❌ Directory not found: $SOLFUN_DIR"
    exit 1
fi

mkdir -p "$WITNESS_DIR"

echo "🔍 Importing FRENs from solfunmeme archive..."
echo "=================================================="
echo "Source: $SOLFUN_DIR"
echo "Witness dir: $WITNESS_DIR"
echo ""

# Find all .meta files (token metadata)
TOKENS=$(find "$SOLFUN_DIR" -name "*.meta" -type f | wc -l)
echo "📊 Found $TOKENS tokens"
echo ""

COUNT=0
for META_FILE in "$SOLFUN_DIR"/*.meta; do
    [ -e "$META_FILE" ] || continue
    
    COUNT=$((COUNT + 1))
    TOKEN=$(basename "$META_FILE" .meta)
    ACCOUNT_FILE="${META_FILE%.meta}.account"
    
    echo "[$COUNT/$TOKENS] Processing: $TOKEN"
    
    # Calculate shard (mod 71)
    SHARD=$((0x$(echo -n "$TOKEN" | sha256sum | cut -c1-2) % 71))
    
    # Create witness
    TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    WITNESS_FILE="$WITNESS_DIR/${TOKEN}_witness.json"
    
    cat > "$WITNESS_FILE" <<EOF
{
  "timestamp": "$TIMESTAMP",
  "operation": "import_fren",
  "token": "$TOKEN",
  "shard": $SHARD,
  "source": {
    "archive": "solfunmeme",
    "date": "2025-04-25",
    "meta_file": "$META_FILE",
    "account_file": "$ACCOUNT_FILE"
  },
  "files": {
    "meta_exists": $([ -f "$META_FILE" ] && echo "true" || echo "false"),
    "account_exists": $([ -f "$ACCOUNT_FILE" ] && echo "true" || echo "false"),
    "meta_size": $(stat -c%s "$META_FILE" 2>/dev/null || echo "0"),
    "account_size": $(stat -c%s "$ACCOUNT_FILE" 2>/dev/null || echo "0")
  },
  "status": "imported"
}
EOF
    
    echo "   Shard: $SHARD"
    echo "   Witness: $WITNESS_FILE"
    
    # Extract first few bytes of metadata for preview
    if [ -f "$META_FILE" ]; then
        echo "   Meta preview: $(head -c 100 "$META_FILE" | tr -d '\0' | head -1)"
    fi
    echo ""
done

echo "=================================================="
echo "✨ Import complete!"
echo "   Total tokens: $COUNT"
echo "   Witnesses created: $(ls -1 "$WITNESS_DIR"/*.json 2>/dev/null | wc -l)"
echo ""
echo "Next steps:"
echo "  1. Run 9 Muses consensus on each token"
echo "  2. Generate zkTLS proofs"
echo "  3. Build FREN graph"
echo "  4. Commit witnesses to git"
